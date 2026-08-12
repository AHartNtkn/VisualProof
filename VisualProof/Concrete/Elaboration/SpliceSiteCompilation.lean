import VisualProof.Concrete.Elaboration.SpliceCompilation

/-! Construct the exact compiler result at the splice endpoint. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Diagram
open Theory
open Elaboration

namespace Splice.Input.PlugLayout

private noncomputable def contextPosition
    (context : WireContext d) (wire : Fin d.wireCount)
    (member : wire ∈ context) : Fin context.length :=
  (context.lookup? wire).get
    (Option.isSome_iff_exists.mpr (WireContext.lookup?_complete member))

private theorem contextPosition_get
    (context : WireContext d) (wire : Fin d.wireCount)
    (member : wire ∈ context) :
    context.get (contextPosition context wire member) = wire := by
  apply WireContext.lookup?_sound
  exact (Option.some_get (Option.isSome_iff_exists.mpr
    (WireContext.lookup?_complete member))).symm

private theorem frameWireMap_mem_siteFull
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (sourceOuter : WireContext input.frame.val)
    (wire : Fin input.frame.val.wireCount)
    (member : wire ∈ sourceOuter.extend input.site) :
    layout.frameWireMap wire ∈
      (layout.mapFrameContext sourceOuter).extend
        (layout.frameRegion input.site) := by
  rw [WireContext.extend] at member ⊢
  rcases List.mem_append.mp member with outer | localMember
  · apply List.mem_append_left
    exact List.mem_map.mpr ⟨wire, outer, rfl⟩
  · apply List.mem_append_right
    rw [layout.exactScopeWires_frameRegion consistent terminal input.site,
      if_pos rfl]
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨wire, localMember, rfl⟩

private noncomputable def frameSiteFullMap
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (sourceOuter : WireContext input.frame.val) :
    Fin (sourceOuter.extend input.site).length →
      Fin ((layout.mapFrameContext sourceOuter).extend
        (layout.frameRegion input.site)).length :=
  fun index => contextPosition _
    (layout.frameWireMap ((sourceOuter.extend input.site).get index))
    (frameWireMap_mem_siteFull layout consistent terminal sourceOuter _
      (List.get_mem _ _))

private theorem frameSiteFullMap_get
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (sourceOuter : WireContext input.frame.val)
    (index : Fin (sourceOuter.extend input.site).length) :
    ((layout.mapFrameContext sourceOuter).extend
      (layout.frameRegion input.site)).get
        (frameSiteFullMap layout consistent terminal sourceOuter index) =
      layout.frameWireMap ((sourceOuter.extend input.site).get index) :=
  contextPosition_get _ _ _

private theorem bodyRegion_enclosing_terminal
    (layout : PlugLayout input)
    (ancestor : Fin input.pattern.val.diagram.regionCount)
    (encloses : input.pattern.val.diagram.Encloses ancestor
      input.binderSpine.bodyContainer) :
    layout.bodyRegion ancestor = layout.frameRegion input.site := by
  rcases input.binderSpine.enclosing_bodyContainer_eq_root_or_proxy
      input.pattern.property.diagram_well_formed encloses with root | proxy
  · subst ancestor
    apply (layout.bodyRegion_eq_frameRegion_iff _ _).2
    refine ⟨?_, rfl⟩
    rw [layout.materialRegions.index?_eq_none_iff,
      layout.materialRegions_exact]
    exact decide_eq_false_iff_not.mpr (fun material => material.1 rfl)
  · obtain ⟨index, rfl⟩ := proxy
    apply (layout.bodyRegion_eq_frameRegion_iff _ _).2
    refine ⟨?_, rfl⟩
    rw [layout.materialRegions.index?_eq_none_iff,
      layout.materialRegions_exact]
    exact decide_eq_false_iff_not.mpr
      (fun material => material.2 index rfl)

private theorem patternWireMap_mem_siteFull
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (admissible : input.Admissible)
    (sourceOuter : WireContext input.frame.val)
    (sourceExact : (sourceOuter.extend input.site).Exact input.site)
    (patternExact : (CompiledSite.endpointCall (State.ofOpen input.pattern)
      input.binderSpine.bodyContainer).fullContext.Exact
        input.binderSpine.bodyContainer)
    (wire : Fin input.pattern.val.diagram.wireCount)
    (member : wire ∈ (CompiledSite.endpointCall
      (State.ofOpen input.pattern)
      input.binderSpine.bodyContainer).fullContext) :
    layout.patternWireMap wire ∈
      (layout.mapFrameContext sourceOuter).extend
        (layout.frameRegion input.site) := by
  by_cases exposed : wire ∈ input.pattern.val.exposedWires
  · rw [layout.patternWireMap_of_exposed wire exposed]
    let external := layout.exposedWireIndex wire exposed
    let attachment := input.attachment (layout.exposedPosition external)
    exact frameWireMap_mem_siteFull layout consistent
      admissible.terminal_body sourceOuter attachment
      ((sourceExact.mem_iff attachment).mpr
        (admissible.attachments_visible (layout.exposedPosition external)))
  · let internal := layout.internalWires.index wire (by
      rw [layout.internalWires_exact]
      exact decide_eq_true_iff.mpr exposed)
    have origin : layout.internalWires.origin internal = wire :=
      layout.internalWires.origin_index wire _
    rw [← origin, layout.patternWireMap_internal]
    apply List.mem_append_right
    apply (mem_exactScopeWires layout.plugRaw
      (layout.frameRegion input.site) (layout.internalWire internal)).mpr
    rw [layout.plugRaw_wires_internal]
    simp only [PlugLayout.mapPatternWire]
    rw [layout.bodyRegion_enclosing_terminal
      (input.pattern.val.diagram.wires
        (layout.internalWires.origin internal)).scope]
    have sourceEncloses := (patternExact.mem_iff wire).mp member
    change input.pattern.val.diagram.Encloses
      (input.pattern.val.diagram.wires wire).scope
        input.binderSpine.bodyContainer at sourceEncloses
    simpa only [origin] using sourceEncloses

private noncomputable def patternSiteFullMap
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (admissible : input.Admissible)
    (sourceOuter : WireContext input.frame.val)
    (sourceExact : (sourceOuter.extend input.site).Exact input.site)
    (patternExact : (CompiledSite.endpointCall (State.ofOpen input.pattern)
      input.binderSpine.bodyContainer).fullContext.Exact
        input.binderSpine.bodyContainer) :
    Fin (CompiledSite.endpointCall (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).fullContext.length →
      Fin ((layout.mapFrameContext sourceOuter).extend
        (layout.frameRegion input.site)).length :=
  fun index => contextPosition _
    (layout.patternWireMap
      ((CompiledSite.endpointCall (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).fullContext.get index))
    (patternWireMap_mem_siteFull layout consistent admissible sourceOuter
      sourceExact patternExact _ (List.get_mem _ _))

private theorem patternSiteFullMap_get
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (admissible : input.Admissible)
    (sourceOuter : WireContext input.frame.val)
    (sourceExact : (sourceOuter.extend input.site).Exact input.site)
    (patternExact : (CompiledSite.endpointCall (State.ofOpen input.pattern)
      input.binderSpine.bodyContainer).fullContext.Exact
        input.binderSpine.bodyContainer)
    (index : Fin (CompiledSite.endpointCall (State.ofOpen input.pattern)
      input.binderSpine.bodyContainer).fullContext.length) :
    ((layout.mapFrameContext sourceOuter).extend
      (layout.frameRegion input.site)).get
        (patternSiteFullMap layout consistent admissible sourceOuter
          sourceExact patternExact index) =
      layout.patternWireMap
        ((CompiledSite.endpointCall (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).fullContext.get index) :=
  contextPosition_get _ _ _

private theorem siteTargetFull_eq
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (sourceOuter : WireContext input.frame.val) :
    (layout.mapFrameContext sourceOuter).extend
        (layout.frameRegion input.site) =
      ((sourceOuter.extend input.site).map layout.frameWireMap :
        WireContext layout.plugRaw) ++ layout.bodyLocalWires := by
  have targetLocal := layout.exactScopeWires_frameRegion consistent terminal
    input.site
  rw [if_pos rfl] at targetLocal
  change layout.mapFrameContext sourceOuter ++
      exactScopeWires layout.plugRaw (layout.frameRegion input.site) = _
  rw [targetLocal]
  simp [WireContext.extend, PlugLayout.mapFrameContext,
    PlugLayout.frameLocalWires, List.append_assoc]

private theorem siteTargetFull_nodup
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (sourceOuter : WireContext input.frame.val)
    (sourceExact : (sourceOuter.extend input.site).Exact input.site) :
    ((layout.mapFrameContext sourceOuter).extend
      (layout.frameRegion input.site)).Nodup := by
  rw [layout.siteTargetFull_eq consistent terminal sourceOuter,
    List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · exact sourceExact.nodup.map layout.frameWireMap
      (fun _ _ distinct equality =>
        distinct (layout.frameWireMap_injective consistent equality))
  · unfold PlugLayout.bodyLocalWires
    exact (VisualProof.Data.Finite.filterFin_nodup _).map
      layout.internalWire (fun _ _ distinct equality =>
        distinct (layout.internalWire_injective equality))
  · intro frameWire frameMember internalWire internalMember equality
    obtain ⟨sourceWire, _, rfl⟩ := List.mem_map.mp frameMember
    obtain ⟨internal, _, rfl⟩ := List.mem_map.mp internalMember
    exact layout.internalWire_ne_frameWireMap internal sourceWire equality.symm

private theorem frameWireMap_origin (layout : PlugLayout input)
    (quotient : input.wireQuotient.Carrier) :
    layout.frameWireMap (input.wireQuotient.origin quotient) =
      layout.frameWire quotient := by
  unfold PlugLayout.frameWireMap
  rw [input.quotientWire_wireQuotient_origin]

private theorem materialRegion_not_encloses_frame
    (layout : PlugLayout input)
    (material : layout.materialRegions.Carrier)
    (frame : Fin input.frame.val.regionCount) :
    ¬ layout.plugRaw.Encloses (layout.materialRegion material)
      (layout.frameRegion frame) := by
  rintro ⟨steps, climbed⟩
  rw [layout.climb_frameRegion] at climbed
  cases sourceClimb : input.frame.val.climb steps.val frame with
  | none => simp [sourceClimb] at climbed
  | some sourceRegion =>
      simp [sourceClimb] at climbed
      exact layout.frameRegion_ne_materialRegion sourceRegion material
        (Option.some.inj climbed)

private theorem frameWireMap_scope
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (wire : Fin input.frame.val.wireCount) :
    (layout.plugRaw.wires (layout.frameWireMap wire)).scope =
      layout.frameRegion (input.frame.val.wires wire).scope := by
  have scope := coalescedScope_quotientWire input consistent wire
  unfold PlugLayout.frameWireMap
  rw [layout.plugRaw_wires_frame, scope]

private theorem frameWireMap_mem_full
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (sourceFull : WireContext input.frame.val)
    (targetFull : WireContext layout.plugRaw)
    (sourceExact : sourceFull.Exact input.site)
    (targetExact : targetFull.Exact (layout.frameRegion input.site))
    (wire : Fin input.frame.val.wireCount) (member : wire ∈ sourceFull) :
    layout.frameWireMap wire ∈ targetFull := by
  apply (targetExact.mem_iff _).mpr
  rw [layout.frameWireMap_scope consistent]
  exact (layout.encloses_frameRegion_iff _ _).2
    ((sourceExact.mem_iff wire).mp member)

private noncomputable def frameFullMap
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (sourceFull : WireContext input.frame.val)
    (targetFull : WireContext layout.plugRaw)
    (sourceExact : sourceFull.Exact input.site)
    (targetExact : targetFull.Exact (layout.frameRegion input.site)) :
    Fin sourceFull.length → Fin targetFull.length :=
  fun index => contextPosition targetFull
    (layout.frameWireMap (sourceFull.get index))
    (layout.frameWireMap_mem_full consistent sourceFull targetFull sourceExact
      targetExact _ (List.get_mem _ _))

private theorem frameFullMap_get
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (sourceFull : WireContext input.frame.val)
    (targetFull : WireContext layout.plugRaw)
    (sourceExact : sourceFull.Exact input.site)
    (targetExact : targetFull.Exact (layout.frameRegion input.site))
    (index : Fin sourceFull.length) :
    targetFull.get (layout.frameFullMap consistent sourceFull targetFull
      sourceExact targetExact index) =
        layout.frameWireMap (sourceFull.get index) :=
  contextPosition_get _ _ _

private theorem patternWireMap_mem_full
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (admissible : input.Admissible)
    (sourceFull : WireContext input.frame.val)
    (targetFull : WireContext layout.plugRaw)
    (sourceExact : sourceFull.Exact input.site)
    (targetExact : targetFull.Exact (layout.frameRegion input.site))
    (patternExact : (CompiledSite.endpointCall (State.ofOpen input.pattern)
      input.binderSpine.bodyContainer).fullContext.Exact
        input.binderSpine.bodyContainer)
    (wire : Fin input.pattern.val.diagram.wireCount)
    (member : wire ∈ (CompiledSite.endpointCall
      (State.ofOpen input.pattern)
      input.binderSpine.bodyContainer).fullContext) :
    layout.patternWireMap wire ∈ targetFull := by
  by_cases exposed : wire ∈ input.pattern.val.exposedWires
  · rw [layout.patternWireMap_of_exposed wire exposed]
    let external := layout.exposedWireIndex wire exposed
    let attachment := input.attachment (layout.exposedPosition external)
    exact layout.frameWireMap_mem_full consistent sourceFull targetFull
      sourceExact targetExact attachment
      ((sourceExact.mem_iff attachment).mpr
        (admissible.attachments_visible (layout.exposedPosition external)))
  · let internal := layout.internalWires.index wire (by
      rw [layout.internalWires_exact]
      exact decide_eq_true_iff.mpr exposed)
    have origin : layout.internalWires.origin internal = wire :=
      layout.internalWires.origin_index wire _
    rw [← origin, layout.patternWireMap_internal]
    apply (targetExact.mem_iff _).mpr
    rw [layout.plugRaw_wires_internal]
    simp only [PlugLayout.mapPatternWire]
    have sourceEncloses := (patternExact.mem_iff wire).mp member
    change input.pattern.val.diagram.Encloses
      (input.pattern.val.diagram.wires wire).scope
        input.binderSpine.bodyContainer at sourceEncloses
    have originEncloses : input.pattern.val.diagram.Encloses
        (input.pattern.val.diagram.wires
          (layout.internalWires.origin internal)).scope
        input.binderSpine.bodyContainer := by
      simpa only [origin] using sourceEncloses
    rw [layout.bodyRegion_enclosing_terminal _ originEncloses]
    exact Diagram.Encloses.refl _ _

private noncomputable def patternFullMap
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (admissible : input.Admissible)
    (sourceFull : WireContext input.frame.val)
    (targetFull : WireContext layout.plugRaw)
    (sourceExact : sourceFull.Exact input.site)
    (targetExact : targetFull.Exact (layout.frameRegion input.site))
    (patternExact : (CompiledSite.endpointCall (State.ofOpen input.pattern)
      input.binderSpine.bodyContainer).fullContext.Exact
        input.binderSpine.bodyContainer) :
    Fin (CompiledSite.endpointCall (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).fullContext.length →
      Fin targetFull.length :=
  fun index => contextPosition targetFull
    (layout.patternWireMap ((CompiledSite.endpointCall
      (State.ofOpen input.pattern)
      input.binderSpine.bodyContainer).fullContext.get index))
    (layout.patternWireMap_mem_full consistent admissible sourceFull targetFull
      sourceExact targetExact patternExact _ (List.get_mem _ _))

private theorem patternFullMap_get
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (admissible : input.Admissible)
    (sourceFull : WireContext input.frame.val)
    (targetFull : WireContext layout.plugRaw)
    (sourceExact : sourceFull.Exact input.site)
    (targetExact : targetFull.Exact (layout.frameRegion input.site))
    (patternExact : (CompiledSite.endpointCall (State.ofOpen input.pattern)
      input.binderSpine.bodyContainer).fullContext.Exact
        input.binderSpine.bodyContainer)
    (index : Fin (CompiledSite.endpointCall (State.ofOpen input.pattern)
      input.binderSpine.bodyContainer).fullContext.length) :
    targetFull.get (layout.patternFullMap consistent admissible sourceFull
      targetFull sourceExact targetExact patternExact index) =
      layout.patternWireMap ((CompiledSite.endpointCall
        (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).fullContext.get index) :=
  contextPosition_get _ _ _

private theorem siteTargetFull_exact
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (sourceOuter : WireContext input.frame.val)
    (sourceExact : (sourceOuter.extend input.site).Exact input.site) :
    ((layout.mapFrameContext sourceOuter).extend
      (layout.frameRegion input.site)).Exact
        (layout.frameRegion input.site) := by
  refine ⟨layout.siteTargetFull_nodup consistent terminal sourceOuter
      sourceExact, ?_⟩
  intro targetWire
  rw [layout.siteTargetFull_eq consistent terminal sourceOuter]
  refine Fin.addCases (motive := fun targetWire =>
    targetWire ∈
        ((sourceOuter.extend input.site).map layout.frameWireMap :
          WireContext layout.plugRaw) ++ layout.bodyLocalWires ↔
      layout.plugRaw.Encloses (layout.plugRaw.wires targetWire).scope
        (layout.frameRegion input.site)) (fun quotient => ?_)
      (fun internal => ?_) targetWire
  · change layout.frameWire quotient ∈
        ((sourceOuter.extend input.site).map layout.frameWireMap :
          WireContext layout.plugRaw) ++ layout.bodyLocalWires ↔
      layout.plugRaw.Encloses
        (layout.plugRaw.wires (layout.frameWire quotient)).scope
          (layout.frameRegion input.site)
    have mapped := layout.frameWireMap_origin quotient
    rw [← mapped]
    have scope := coalescedScope_quotientWire input consistent
      (input.wireQuotient.origin quotient)
    rw [input.quotientWire_wireQuotient_origin] at scope
    constructor
    · intro member
      rcases List.mem_append.mp member with frameMember | bodyMember
      · obtain ⟨sourceWire, sourceMember, wireEq⟩ :=
          List.mem_map.mp frameMember
        have sourceEq : sourceWire = input.wireQuotient.origin quotient :=
          layout.frameWireMap_injective consistent
            (wireEq.trans rfl)
        subst sourceWire
        rw [mapped, layout.plugRaw_wires_frame, scope]
        exact (layout.encloses_frameRegion_iff _ _).2
          ((sourceExact.mem_iff _).mp sourceMember)
      · obtain ⟨internal, _, equality⟩ := List.mem_map.mp bodyMember
        exact False.elim (layout.internalWire_ne_frameWireMap internal
          (input.wireQuotient.origin quotient) equality)
    · intro targetEncloses
      apply List.mem_append.mpr
      left
      apply List.mem_map.mpr
      refine ⟨input.wireQuotient.origin quotient, ?_, rfl⟩
      apply (sourceExact.mem_iff _).mpr
      rw [mapped, layout.plugRaw_wires_frame, scope] at targetEncloses
      exact (layout.encloses_frameRegion_iff _ _).1 targetEncloses
  · change layout.internalWire internal ∈
        ((sourceOuter.extend input.site).map layout.frameWireMap :
          WireContext layout.plugRaw) ++ layout.bodyLocalWires ↔
      layout.plugRaw.Encloses
        (layout.plugRaw.wires (layout.internalWire internal)).scope
          (layout.frameRegion input.site)
    constructor
    · intro member
      rcases List.mem_append.mp member with frameMember | bodyMember
      · obtain ⟨sourceWire, _, equality⟩ := List.mem_map.mp frameMember
        exact False.elim (layout.internalWire_ne_frameWireMap internal
          sourceWire equality.symm)
      · obtain ⟨candidate, candidateMember, equality⟩ :=
          List.mem_map.mp bodyMember
        have internalEq : candidate = internal :=
          layout.internalWire_injective equality
        subst candidate
        rw [layout.plugRaw_wires_internal]
        simp only [PlugLayout.mapPatternWire]
        have accepted := (VisualProof.Data.Finite.mem_filterFin internal).mp
          candidateMember
        have scopeEq := of_decide_eq_true accepted
        rw [scopeEq, layout.bodyRegion_bodyContainer]
        exact Diagram.Encloses.refl _ _
    · intro targetEncloses
      apply List.mem_append.mpr
      right
      apply List.mem_map.mpr
      refine ⟨internal, ?_, rfl⟩
      exact (VisualProof.Data.Finite.mem_filterFin internal).mpr (by
        apply decide_eq_true
        rw [layout.plugRaw_wires_internal] at targetEncloses
        simp only [PlugLayout.mapPatternWire] at targetEncloses
        cases materialEq : layout.materialRegions.index?
            (input.pattern.val.diagram.wires
              (layout.internalWires.origin internal)).scope with
        | none =>
            exact (layout.internalWire_not_material_iff_bodyContainer terminal
              internal).1 (by
                have hdeleted :=
                  (layout.materialRegions.index?_eq_none_iff _).1 materialEq
                rw [layout.materialRegions_exact] at hdeleted
                exact decide_eq_false_iff_not.mp hdeleted)
        | some material =>
            have bodyEq : layout.bodyRegion
                (input.pattern.val.diagram.wires
                  (layout.internalWires.origin internal)).scope =
                  layout.materialRegion material := by
              unfold PlugLayout.bodyRegion
              rw [materialEq]
            rw [bodyEq] at targetEncloses
            exact (layout.materialRegion_not_encloses_frame material input.site
              targetEncloses).elim)

private theorem terminalBinderMapped
    (layout : PlugLayout input)
    (sourceBinders : BinderContext input.frame.val targetRels)
    (targetBinders : BinderContext layout.plugRaw targetRels)
    (frameBindersMapped : ∀ binder,
      targetBinders (layout.frameRegion binder) = sourceBinders binder)
    (relationMap : RelationRenaming
      (CompiledSite.endpointCall (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).rels targetRels)
    (hostLookup : ∀ {arity}
      (relation : RelVar
        (CompiledSite.endpointCall (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).rels arity),
      sourceBinders (input.binderTarget
          (terminalRelationProxyEquiv input relation.index)) =
        some ⟨arity, relationMap relation⟩)
    (binder : Fin input.pattern.val.diagram.regionCount)
    {arity} {relation : RelVar
      (CompiledSite.endpointCall (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).rels arity}
    (sourceLookup :
      (CompiledSite.endpointCall (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).binders binder =
          some ⟨arity, relation⟩) :
    targetBinders (layout.binderRegion binder) =
      some ⟨arity, relationMap relation⟩ := by
  have binderEq : binder = input.binderSpine.proxy
      (terminalRelationProxyEquiv input relation.index) := by
    have owner := (CompiledSite.endpoint_binders_enumeration
      (State.ofOpen input.pattern) input.binderSpine.bodyContainer)
        |>.lookup_owner relation sourceLookup
    exact owner.symm.trans
      (terminalRelationProxyEquiv_binder input relation.index).symm
  subst binder
  rw [layout.binderRegion_proxy, frameBindersMapped]
  exact hostLookup relation

/-- Compile the splice endpoint in its actual target occurrence order. The
result is constructed from the retained frame blocks and the terminal pattern
blocks; no target focus or target compiler search is involved. -/
private theorem compileSpliceSiteItems
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (admissible : input.Admissible) (targetWf : layout.plugRaw.WellFormed)
    (sourceFull : WireContext input.frame.val)
    (sourceBinders : BinderContext input.frame.val sourceRels)
    (targetFull : WireContext layout.plugRaw)
    (targetBinders : BinderContext layout.plugRaw sourceRels)
    (frameMap : Fin sourceFull.length → Fin targetFull.length)
    (patternMap : Fin (CompiledSite.endpointCall
      (State.ofOpen input.pattern) input.binderSpine.bodyContainer
        ).fullContext.length → Fin targetFull.length)
    (relationMap : RelationRenaming
      (CompiledSite.endpointCall (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).rels sourceRels)
    (patternBindersMapped : ∀ binder {arity relation},
      (CompiledSite.endpointCall (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).binders binder =
        some ⟨arity, relation⟩ →
      targetBinders (layout.binderRegion binder) =
        some ⟨arity, relationMap relation⟩)
    (frameBindersMapped : ∀ binder,
      targetBinders (layout.frameRegion binder) =
        (sourceBinders binder).map fun relation =>
          ⟨relation.1, relation.2⟩)
    (sourceExact : sourceFull.Exact input.site)
    (targetExact : targetFull.Exact (layout.frameRegion input.site))
    (frameGet : ∀ index,
      targetFull.get (frameMap index) =
        layout.frameWireMap (sourceFull.get index))
    (patternGet : ∀ index,
      targetFull.get (patternMap index) = layout.patternWireMap
        ((CompiledSite.endpointCall (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).fullContext.get index))
    {sourceItems : CompiledItems input.frame.val
      sourceFull sourceRels sourceBinders}
    (sourceCompiled : compileItems? input.frame.val input.frame.property
      input.site sourceFull sourceBinders
      (localOccurrences input.frame.val input.site) (fun _ member => member) =
        some sourceItems) :
    ∃ (targetItems : CompiledItems layout.plugRaw
          targetFull sourceRels targetBinders)
        (sourceNodes sourceChildren : CompiledItems input.frame.val
          sourceFull sourceRels sourceBinders)
        (patternNodesSource patternChildrenSource : CompiledItems
          input.pattern.val.diagram
          (CompiledSite.endpointCall (State.ofOpen input.pattern)
            input.binderSpine.bodyContainer).fullContext
          (CompiledSite.endpointCall (State.ofOpen input.pattern)
            input.binderSpine.bodyContainer).rels
          (CompiledSite.endpointCall (State.ofOpen input.pattern)
            input.binderSpine.bodyContainer).binders)
        (frameNodes patternNodes frameChildren patternChildren : CompiledItems
          layout.plugRaw
          targetFull sourceRels targetBinders),
      compileItems? layout.plugRaw targetWf (layout.frameRegion input.site)
          targetFull
          targetBinders
          (localOccurrences layout.plugRaw (layout.frameRegion input.site))
          (fun _ member => member) = some targetItems ∧
      sourceItems = sourceNodes.append sourceChildren ∧
      (CompiledSite.endpoint (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).items =
        patternNodesSource.append patternChildrenSource ∧
      targetItems = (frameNodes.append patternNodes).append
        (frameChildren.append patternChildren) ∧
      frameNodes.erase = (sourceNodes.erase.renameWires
        frameMap).renameRelations (fun relation => relation) ∧
      patternNodes.erase =
        (patternNodesSource.erase.renameWires
          patternMap).renameRelations
            relationMap ∧
      frameChildren.erase = (sourceChildren.erase.renameWires
        frameMap).renameRelations (fun relation => relation) ∧
      patternChildren.erase =
        (patternChildrenSource.erase.renameWires
          patternMap).renameRelations
            relationMap := by
  let patternState := State.ofOpen input.pattern
  let patternCall := CompiledSite.endpointCall patternState
    input.binderSpine.bodyContainer
  have patternExact : patternCall.fullContext.Exact
      input.binderSpine.bodyContainer := by
    exact CompiledSite.endpoint_fullContext_exact patternState
      input.binderSpine.bodyContainer
  obtain ⟨sourceNodes, sourceChildren, sourceNodesCompiled,
      sourceChildrenCompiled, sourceItemsEq⟩ :=
    compileItems?_append_inv input.frame.property input.site sourceFull
      sourceBinders (localNodeOccurrences input.frame.val input.site)
      (localChildOccurrences input.frame.val input.site)
      (fun _ member => member) sourceCompiled
  have patternCompiled : patternCall.compile?
      input.pattern.val.diagram input.pattern.property.diagram_well_formed =
        some (CompiledSite.endpoint patternState
          input.binderSpine.bodyContainer) := by
    exact CompiledSite.endpoint_computation patternState
      input.binderSpine.bodyContainer
  have patternItemsCompiled :
      compileItems? input.pattern.val.diagram
          input.pattern.property.diagram_well_formed patternCall.origin
          patternCall.fullContext patternCall.binders
          (localOccurrences input.pattern.val.diagram patternCall.origin)
          (fun _ member => member) =
        some (CompiledSite.endpoint patternState
          input.binderSpine.bodyContainer).items := by
    cases endpointEq : CompiledSite.endpoint patternState
        input.binderSpine.bodyContainer with
    | mk items =>
        apply CompilerCall.compile?_items_of_success
          input.pattern.property.diagram_well_formed patternCall
        simpa only [endpointEq] using patternCompiled
  obtain ⟨patternNodesSource, patternChildrenSource, patternNodesCompiled,
      patternChildrenCompiled, patternItemsEq⟩ :=
    compileItems?_append_inv input.pattern.property.diagram_well_formed
      patternCall.origin patternCall.fullContext patternCall.binders
      (localNodeOccurrences input.pattern.val.diagram patternCall.origin)
      (localChildOccurrences input.pattern.val.diagram patternCall.origin)
      (fun _ member => member) patternItemsCompiled
  have patternOrigin : patternCall.origin =
      input.binderSpine.bodyContainer := by
    exact CompiledSite.endpoint_origin patternState
      input.binderSpine.bodyContainer
  have patternRegionMapped : layout.bodyRegion patternCall.origin =
      layout.frameRegion input.site := by
    rw [patternOrigin, layout.bodyRegion_bodyContainer]
  have patternExactAtOrigin : patternCall.fullContext.Exact
      patternCall.origin := by
    simpa only [patternOrigin] using patternExact
  obtain ⟨frameNodes, frameNodesCompiled, frameNodesErase⟩ :=
    layout.compileFrameNodeBlock consistent targetWf input.site sourceFull
      targetFull sourceBinders targetBinders frameMap
      (fun relation => relation) sourceExact targetExact.nodup frameGet
      frameBindersMapped sourceNodesCompiled
  obtain ⟨patternNodes, patternNodesCompiled, patternNodesErase⟩ :=
    layout.compilePatternNodeBlock targetWf
      patternCall.origin (layout.frameRegion input.site)
      patternRegionMapped patternCall.fullContext targetFull
      patternCall.binders targetBinders patternMap relationMap
      patternExactAtOrigin targetExact.nodup patternGet
      (fun _ _ binder _ _ _ sourceLookup =>
        patternBindersMapped binder sourceLookup)
      patternNodesCompiled
  have nodeDirect : ∀ occurrence,
      occurrence ∈ layout.frameNodeOccurrences input.site ++
          layout.bodyNodeOccurrences →
        occurrence ∈ localOccurrences layout.plugRaw
          (layout.frameRegion input.site) := by
    intro occurrence member
    rw [layout.localOccurrences_site admissible]
    exact List.mem_append_left _ member
  have frameNodesCanonical :
      compileItems? layout.plugRaw targetWf (layout.frameRegion input.site)
          targetFull targetBinders (layout.frameNodeOccurrences input.site)
          (fun occurrence member => nodeDirect occurrence
            (List.mem_append_left _ member)) = some frameNodes := by
    exact frameNodesCompiled
  have patternNodesCanonical :
      compileItems? layout.plugRaw targetWf (layout.frameRegion input.site)
          targetFull targetBinders layout.bodyNodeOccurrences
          (fun occurrence member => nodeDirect occurrence
            (List.mem_append_right _ member)) = some patternNodes := by
    have occurrences := layout.map_localNodeOccurrences_body
    have mappedOccurrences :
        (localNodeOccurrences input.pattern.val.diagram
          patternCall.origin).map layout.mapPatternOccurrence =
            layout.bodyNodeOccurrences := by
      rw [patternOrigin]
      exact occurrences
    exact (compileItems?_congr_occurrences targetWf
      (layout.frameRegion input.site) targetFull targetBinders
      mappedOccurrences.symm _ _).trans patternNodesCompiled
  have targetNodesCompiled := compileItems?_append targetWf
    (layout.frameRegion input.site) targetFull targetBinders
    (layout.frameNodeOccurrences input.site) layout.bodyNodeOccurrences
    nodeDirect frameNodesCanonical patternNodesCanonical
  have sourceFrameChildrenDirect : ∀ occurrence,
      occurrence ∈ localChildOccurrences input.frame.val input.site →
        occurrence ∈ localOccurrences input.frame.val input.site :=
    fun _ member => List.mem_append_right _ member
  have childDirect : ∀ occurrence,
      occurrence ∈ layout.frameChildOccurrences input.site ++
          layout.bodyChildOccurrences →
        occurrence ∈ localOccurrences layout.plugRaw
          (layout.frameRegion input.site) := by
    intro occurrence member
    rw [layout.localOccurrences_site admissible]
    exact List.mem_append_right _ member
  have targetFrameChildrenDirect : ∀ occurrence,
      occurrence ∈ (localChildOccurrences input.frame.val input.site).map
          layout.mapFrameOccurrence →
        occurrence ∈ localOccurrences layout.plugRaw
          (layout.frameRegion input.site) := by
    intro occurrence member
    apply childDirect occurrence
    apply List.mem_append_left
    simpa only [layout.map_localChildOccurrences_frame] using member
  obtain ⟨frameChildren, frameChildrenCompiled, frameChildrenErase⟩ :=
    compileItems?_map_success input.frame.property targetWf input.site
      (layout.frameRegion input.site) sourceFull targetFull sourceBinders
      targetBinders (localChildOccurrences input.frame.val input.site)
      layout.mapFrameOccurrence sourceFrameChildrenDirect
      targetFrameChildrenDirect frameMap (fun relation => relation) (by
        intro occurrence member sourceItem sourceItemCompiled
        cases occurrence with
        | node node =>
            exact False.elim
              ((not_mem_localChildOccurrences_node _ _ _) member)
        | child child =>
            have sourceParentEq :=
              (mem_localOccurrences_child input.frame.val input.site child).mp
                (sourceFrameChildrenDirect _ member)
            have childAway : ¬ input.frame.val.Encloses child input.site :=
              checked_direct_child_not_encloses_parent input.frame.property
                sourceParentEq
            have targetParentEq :
                (layout.plugRaw.regions
                  (layout.frameRegion child)).parent? =
                    some (layout.frameRegion input.site) := by
              rw [layout.plugRaw_regions_frame]
              exact (layout.mapFrameRegion_parent_eq_some_iff
                child input.site).2 sourceParentEq
            have sourceChildExact := sourceExact.extend_child
              input.frame.property sourceParentEq
            have targetChildExact := targetExact.extend_child targetWf
              targetParentEq
            cases sourceRegion : input.frame.val.regions child with
            | sheet =>
                rw [compileOccurrence?_child_sheet input.frame.property
                  input.site child sourceFull sourceBinders
                  (sourceFrameChildrenDirect _ member) sourceRegion]
                    at sourceItemCompiled
                contradiction
            | cut parent =>
                have parentEq : parent = input.site := by
                  simpa [sourceRegion, CRegion.parent?] using sourceParentEq
                subst parent
                obtain ⟨sourceChild, sourceChildCompiled, sourceItemEq⟩ :=
                  compileOccurrence?_child_cut_success input.frame.property
                    input.site child sourceFull sourceBinders
                    (sourceFrameChildrenDirect _ member) sourceRegion
                    sourceItemCompiled
                subst sourceItem
                obtain ⟨targetChild, targetChildCompiled,
                    targetChildErase⟩ :=
                  layout.compileFrameRegionAway consistent
                    admissible.terminal_body targetWf child childAway
                    sourceFull targetFull sourceBinders targetBinders frameMap
                    (fun relation => relation) sourceChildExact
                    targetChildExact frameGet frameBindersMapped
                    sourceChildCompiled
                refine ⟨CompiledItem.cut targetChild, ?_, ?_⟩
                · have targetRegion : layout.plugRaw.regions
                      (layout.frameRegion child) =
                        .cut (layout.frameRegion input.site) := by
                    rw [layout.plugRaw_regions_frame, sourceRegion]
                    rfl
                  change compileOccurrence? layout.plugRaw targetWf
                    (layout.frameRegion input.site) targetFull targetBinders
                    (.child (layout.frameRegion child)) _ =
                      some (CompiledItem.cut targetChild)
                  rw [compileOccurrence?_child_cut targetWf
                    (layout.frameRegion input.site) (layout.frameRegion child)
                    targetFull targetBinders
                    (targetFrameChildrenDirect _ (List.mem_map.mpr
                      ⟨LocalOccurrence.child child, member, rfl⟩))
                    targetRegion, targetChildCompiled]
                  rfl
                · exact congrArg Item.cut targetChildErase
            | bubble parent arity =>
                have parentEq : parent = input.site := by
                  simpa [sourceRegion, CRegion.parent?] using sourceParentEq
                subst parent
                obtain ⟨sourceChild, sourceChildCompiled, sourceItemEq⟩ :=
                  compileOccurrence?_child_bubble_success input.frame.property
                    input.site child sourceFull sourceBinders arity
                    (sourceFrameChildrenDirect _ member) sourceRegion
                    sourceItemCompiled
                subst sourceItem
                have pushedMapped := layout.frameBindersMapped_push
                  sourceBinders targetBinders (fun relation => relation)
                  frameBindersMapped child arity
                obtain ⟨targetChild, targetChildCompiled,
                    targetChildErase⟩ :=
                  layout.compileFrameRegionAway consistent
                    admissible.terminal_body targetWf child childAway
                    sourceFull targetFull (sourceBinders.push child arity)
                    (targetBinders.push (layout.frameRegion child) arity)
                    frameMap (RelationRenaming.lift
                      (fun relation => relation) arity)
                    sourceChildExact targetChildExact frameGet pushedMapped
                    sourceChildCompiled
                refine ⟨CompiledItem.bubble arity targetChild, ?_, ?_⟩
                · have targetRegion : layout.plugRaw.regions
                      (layout.frameRegion child) =
                        .bubble (layout.frameRegion input.site) arity := by
                    rw [layout.plugRaw_regions_frame, sourceRegion]
                    rfl
                  change compileOccurrence? layout.plugRaw targetWf
                    (layout.frameRegion input.site) targetFull targetBinders
                    (.child (layout.frameRegion child)) _ =
                      some (CompiledItem.bubble arity targetChild)
                  rw [compileOccurrence?_child_bubble targetWf
                    (layout.frameRegion input.site) (layout.frameRegion child)
                    targetFull targetBinders arity
                    (targetFrameChildrenDirect _ (List.mem_map.mpr
                      ⟨LocalOccurrence.child child, member, rfl⟩))
                    targetRegion, targetChildCompiled]
                  rfl
                · exact congrArg (Item.bubble arity) targetChildErase)
      sourceChildrenCompiled
  have sourcePatternChildrenDirect : ∀ occurrence,
      occurrence ∈ localChildOccurrences input.pattern.val.diagram
          patternCall.origin →
        occurrence ∈ localOccurrences input.pattern.val.diagram
          patternCall.origin :=
    fun _ member => List.mem_append_right _ member
  have targetPatternChildrenDirect : ∀ occurrence,
      occurrence ∈ (localChildOccurrences input.pattern.val.diagram
          patternCall.origin).map layout.mapPatternOccurrence →
        occurrence ∈ localOccurrences layout.plugRaw
          (layout.frameRegion input.site) := by
    intro occurrence member
    apply childDirect occurrence
    apply List.mem_append_right
    have mappedOccurrences :
        (localChildOccurrences input.pattern.val.diagram
          patternCall.origin).map layout.mapPatternOccurrence =
            layout.bodyChildOccurrences := by
      rw [patternOrigin]
      exact layout.map_localChildOccurrences_body
    exact mappedOccurrences ▸ member
  obtain ⟨patternChildren, patternChildrenCompiled,
      patternChildrenErase⟩ :=
    compileItems?_map_success input.pattern.property.diagram_well_formed
      targetWf patternCall.origin (layout.frameRegion input.site)
      patternCall.fullContext targetFull patternCall.binders targetBinders
      (localChildOccurrences input.pattern.val.diagram patternCall.origin)
      layout.mapPatternOccurrence sourcePatternChildrenDirect
      targetPatternChildrenDirect patternMap relationMap (by
        intro occurrence member sourceItem sourceItemCompiled
        cases occurrence with
        | node node =>
            exact False.elim
              ((not_mem_localChildOccurrences_node _ _ _) member)
        | child child =>
            have sourceParentEq :=
              (mem_localOccurrences_child input.pattern.val.diagram
                patternCall.origin child).mp
                  (sourcePatternChildrenDirect _ member)
            have bodyParentEq :
                (input.pattern.val.diagram.regions child).parent? =
                  some input.binderSpine.bodyContainer := by
              simpa only [patternOrigin] using sourceParentEq
            have childMaterial := directBodyChild_isMaterial input child
              bodyParentEq
            have targetParentEq :
                (layout.plugRaw.regions (layout.bodyRegion child)).parent? =
                  some (layout.frameRegion input.site) := by
              rw [layout.plugRaw_regions_materialSource child childMaterial]
              cases sourceRegion : input.pattern.val.diagram.regions child with
              | sheet =>
                  simp [sourceRegion, CRegion.parent?] at bodyParentEq
              | cut parent =>
                  simp [sourceRegion, CRegion.parent?] at bodyParentEq
                  subst parent
                  simp only [PlugLayout.mapPatternRegion, CRegion.parent?]
                  rw [layout.bodyRegion_bodyContainer]
                  rfl
              | bubble parent arity =>
                  simp [sourceRegion, CRegion.parent?] at bodyParentEq
                  subst parent
                  simp only [PlugLayout.mapPatternRegion, CRegion.parent?]
                  rw [layout.bodyRegion_bodyContainer]
                  rfl
            have sourceChildExact := patternExactAtOrigin.extend_child
              input.pattern.property.diagram_well_formed sourceParentEq
            have targetChildExact := targetExact.extend_child targetWf
              targetParentEq
            cases sourceRegion : input.pattern.val.diagram.regions child with
            | sheet =>
                rw [compileOccurrence?_child_sheet
                  input.pattern.property.diagram_well_formed
                  patternCall.origin child patternCall.fullContext
                  patternCall.binders (sourcePatternChildrenDirect _ member)
                  sourceRegion] at sourceItemCompiled
                contradiction
            | cut parent =>
                have parentEq : parent = patternCall.origin := by
                  simpa [sourceRegion, CRegion.parent?] using sourceParentEq
                subst parent
                obtain ⟨sourceChild, sourceChildCompiled, sourceItemEq⟩ :=
                  compileOccurrence?_child_cut_success
                    input.pattern.property.diagram_well_formed
                    patternCall.origin child patternCall.fullContext
                    patternCall.binders (sourcePatternChildrenDirect _ member)
                    sourceRegion sourceItemCompiled
                subst sourceItem
                obtain ⟨targetChild, targetChildCompiled,
                    targetChildErase⟩ :=
                  layout.compileMaterialRegion targetWf child childMaterial
                    patternCall.fullContext targetFull patternCall.binders
                    targetBinders patternMap relationMap sourceChildExact
                    targetChildExact patternGet
                    (fun binder _ _ sourceLookup =>
                      patternBindersMapped binder sourceLookup)
                    sourceChildCompiled
                refine ⟨CompiledItem.cut targetChild, ?_, ?_⟩
                · have targetRegion : layout.plugRaw.regions
                      (layout.bodyRegion child) =
                        .cut (layout.frameRegion input.site) := by
                    rw [layout.plugRaw_regions_materialSource child
                      childMaterial, sourceRegion]
                    simp only [PlugLayout.mapPatternRegion]
                    rw [patternOrigin,
                      layout.bodyRegion_bodyContainer]
                    rfl
                  change compileOccurrence? layout.plugRaw targetWf
                    (layout.frameRegion input.site) targetFull targetBinders
                    (.child (layout.bodyRegion child)) _ =
                      some (CompiledItem.cut targetChild)
                  rw [compileOccurrence?_child_cut targetWf
                    (layout.frameRegion input.site) (layout.bodyRegion child)
                    targetFull targetBinders
                    (targetPatternChildrenDirect _ (List.mem_map.mpr
                      ⟨LocalOccurrence.child child, member, rfl⟩))
                    targetRegion, targetChildCompiled]
                  rfl
                · exact congrArg Item.cut targetChildErase
            | bubble parent arity =>
                have parentEq : parent = patternCall.origin := by
                  simpa [sourceRegion, CRegion.parent?] using sourceParentEq
                subst parent
                obtain ⟨sourceChild, sourceChildCompiled, sourceItemEq⟩ :=
                  compileOccurrence?_child_bubble_success
                    input.pattern.property.diagram_well_formed
                    patternCall.origin child patternCall.fullContext
                    patternCall.binders arity
                    (sourcePatternChildrenDirect _ member) sourceRegion
                    sourceItemCompiled
                subst sourceItem
                have pushedMapped := layout.patternBindersMapped_push
                  patternCall.binders targetBinders relationMap
                  (fun binder _ _ sourceLookup =>
                    patternBindersMapped binder sourceLookup)
                  child childMaterial arity
                obtain ⟨targetChild, targetChildCompiled,
                    targetChildErase⟩ :=
                  layout.compileMaterialRegion targetWf child childMaterial
                    patternCall.fullContext targetFull
                    (patternCall.binders.push child arity)
                    (targetBinders.push (layout.bodyRegion child) arity)
                    patternMap (RelationRenaming.lift relationMap arity)
                    sourceChildExact targetChildExact patternGet pushedMapped
                    sourceChildCompiled
                refine ⟨CompiledItem.bubble arity targetChild, ?_, ?_⟩
                · have targetRegion : layout.plugRaw.regions
                      (layout.bodyRegion child) =
                        .bubble (layout.frameRegion input.site) arity := by
                    rw [layout.plugRaw_regions_materialSource child
                      childMaterial, sourceRegion]
                    simp only [PlugLayout.mapPatternRegion]
                    rw [patternOrigin,
                      layout.bodyRegion_bodyContainer]
                    rfl
                  change compileOccurrence? layout.plugRaw targetWf
                    (layout.frameRegion input.site) targetFull targetBinders
                    (.child (layout.bodyRegion child)) _ =
                      some (CompiledItem.bubble arity targetChild)
                  rw [compileOccurrence?_child_bubble targetWf
                    (layout.frameRegion input.site) (layout.bodyRegion child)
                    targetFull targetBinders arity
                    (targetPatternChildrenDirect _ (List.mem_map.mpr
                      ⟨LocalOccurrence.child child, member, rfl⟩))
                    targetRegion, targetChildCompiled]
                  rfl
                · exact congrArg (Item.bubble arity) targetChildErase)
      patternChildrenCompiled
  have frameChildrenCanonical :
      compileItems? layout.plugRaw targetWf (layout.frameRegion input.site)
          targetFull targetBinders (layout.frameChildOccurrences input.site)
          (fun occurrence member => childDirect occurrence
            (List.mem_append_left _ member)) = some frameChildren := by
    have occurrences := layout.map_localChildOccurrences_frame input.site
    exact (compileItems?_congr_occurrences targetWf
      (layout.frameRegion input.site) targetFull targetBinders
      occurrences.symm _ _).trans frameChildrenCompiled
  have patternChildrenCanonical :
      compileItems? layout.plugRaw targetWf (layout.frameRegion input.site)
          targetFull targetBinders layout.bodyChildOccurrences
          (fun occurrence member => childDirect occurrence
            (List.mem_append_right _ member)) = some patternChildren := by
    have mappedOccurrences :
        (localChildOccurrences input.pattern.val.diagram
          patternCall.origin).map layout.mapPatternOccurrence =
            layout.bodyChildOccurrences := by
      rw [patternOrigin]
      exact layout.map_localChildOccurrences_body
    exact (compileItems?_congr_occurrences targetWf
      (layout.frameRegion input.site) targetFull targetBinders
      mappedOccurrences.symm _ _).trans patternChildrenCompiled
  have targetChildrenCompiled := compileItems?_append targetWf
    (layout.frameRegion input.site) targetFull targetBinders
    (layout.frameChildOccurrences input.site) layout.bodyChildOccurrences
    childDirect frameChildrenCanonical patternChildrenCanonical
  have targetNodesCanonical :
      compileItems? layout.plugRaw targetWf (layout.frameRegion input.site)
          targetFull targetBinders
          (localNodeOccurrences layout.plugRaw
            (layout.frameRegion input.site))
          (fun _ member => List.mem_append_left _ member) =
        some (frameNodes.append patternNodes) := by
    have occurrences : localNodeOccurrences layout.plugRaw
        (layout.frameRegion input.site) =
          layout.frameNodeOccurrences input.site ++
            layout.bodyNodeOccurrences := by
      rw [layout.localNodeOccurrences_frameRegion,
        layout.patternNodeOccurrences_site admissible]
    exact (compileItems?_congr_occurrences targetWf
      (layout.frameRegion input.site) targetFull targetBinders
      occurrences _ _).trans targetNodesCompiled
  have targetChildrenCanonical :
      compileItems? layout.plugRaw targetWf (layout.frameRegion input.site)
          targetFull targetBinders
          (localChildOccurrences layout.plugRaw
            (layout.frameRegion input.site))
          (fun _ member => List.mem_append_right _ member) =
        some (frameChildren.append patternChildren) := by
    have occurrences : localChildOccurrences layout.plugRaw
        (layout.frameRegion input.site) =
          layout.frameChildOccurrences input.site ++
            layout.bodyChildOccurrences := by
      rw [layout.localChildOccurrences_frameRegion,
        layout.materialChildOccurrences_site admissible]
    exact (compileItems?_congr_occurrences targetWf
      (layout.frameRegion input.site) targetFull targetBinders
      occurrences _ _).trans targetChildrenCompiled
  have targetItemsCompiled := compileItems?_append targetWf
    (layout.frameRegion input.site) targetFull targetBinders
    (localNodeOccurrences layout.plugRaw (layout.frameRegion input.site))
    (localChildOccurrences layout.plugRaw (layout.frameRegion input.site))
    (fun _ member => member) targetNodesCanonical targetChildrenCanonical
  have targetItemsCanonical :
      compileItems? layout.plugRaw targetWf
          (layout.frameRegion input.site) targetFull targetBinders
          (localOccurrences layout.plugRaw (layout.frameRegion input.site))
          (fun _ member => member) =
        some ((frameNodes.append patternNodes).append
          (frameChildren.append patternChildren)) := by
    exact (compileItems?_congr_occurrences targetWf
      (layout.frameRegion input.site) targetFull targetBinders
      (localOccurrences_eq_blocks layout.plugRaw
        (layout.frameRegion input.site))
      (fun _ member => member)
      (fun _ member => by simpa only [localOccurrences_eq_blocks] using member)).trans
        targetItemsCompiled
  let targetItems := (frameNodes.append patternNodes).append
    (frameChildren.append patternChildren)
  refine ⟨targetItems, sourceNodes, sourceChildren, patternNodesSource,
    patternChildrenSource, frameNodes, patternNodes, frameChildren,
    patternChildren, targetItemsCanonical, sourceItemsEq, patternItemsEq, rfl,
    frameNodesErase, patternNodesErase, frameChildrenErase,
    patternChildrenErase⟩

private noncomputable def mappedFrameCall
    (layout : PlugLayout input)
    (boundary : List (Fin input.frame.val.wireCount)) :
    CompilerCall input.frame.val →
      CompilerCall layout.plugRaw
  | .root _ _ =>
      .root (layout.outputOpenRoot input boundary).exposedWires
        (layout.outputOpenRoot input boundary).hiddenWires
  | .nested origin outer rels binders =>
      .nested (layout.frameRegion origin) (layout.mapFrameContext outer) rels
        (layout.mapFrameBinders binders)

private theorem mappedFrameCall_origin
    (layout : PlugLayout input) (boundary)
    (call : CompilerCall input.frame.val) :
    (layout.mappedFrameCall boundary call).origin =
      layout.frameRegion call.origin := by
  cases call with
  | root ambient locals => rfl
  | nested origin outer rels binders => rfl

private theorem mappedFrameCall_fullContext_exact
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (admissible : input.Admissible)
    (boundary : List (Fin input.frame.val.wireCount))
    (targetWf : (layout.outputOpenRoot input boundary).WellFormed)
    (call : CompilerCall input.frame.val)
    (atSite : call.origin = input.site)
    (sourceExact : call.fullContext.Exact input.site) :
    (layout.mappedFrameCall boundary call).fullContext.Exact
      (layout.frameRegion input.site) := by
  cases call with
  | root ambient locals =>
      have rootEq : input.frame.val.root = input.site := atSite
      have outputRoot : (layout.outputOpenRoot input boundary).diagram.root =
            layout.frameRegion input.frame.val.root := rfl
      rw [← rootEq, ← outputRoot]
      simpa [mappedFrameCall, CompilerCall.fullContext,
        OpenDiagram.rootWires] using
          (openRootWires_exact targetWf)
  | nested origin outer rels binders =>
      change origin = input.site at atSite
      subst origin
      exact layout.siteTargetFull_exact consistent admissible.terminal_body
        outer sourceExact

/-- Compile the actual target call at the splice endpoint, independently of
whether that endpoint is the open root or a nested region. -/
theorem compileSpliceSite
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (boundary : List (Fin input.frame.val.wireCount))
    (admissible : input.Admissible)
    (targetOpenWf : (layout.outputOpenRoot input boundary).WellFormed)
    (sourceCall : CompilerCall input.frame.val)
    (atSite : sourceCall.origin = input.site)
    (sourceExact : sourceCall.fullContext.Exact input.site)
    (relationMap : RelationRenaming
      (CompiledSite.endpointCall (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).rels sourceCall.rels)
    (hostLookup : ∀ {arity}
      (relation : RelVar
        (CompiledSite.endpointCall (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).rels arity),
      sourceCall.binders (input.binderTarget
          (terminalRelationProxyEquiv input relation.index)) =
        some ⟨arity, relationMap relation⟩)
    {sourceBody : CompiledRegion input.frame.val sourceCall}
    (sourceCompiled : sourceCall.compile? input.frame.val
      input.frame.property = some sourceBody) :
    ∃ targetBody : CompiledRegion layout.plugRaw
        (layout.mappedFrameCall boundary sourceCall),
      (layout.mappedFrameCall boundary sourceCall).compile? layout.plugRaw
        targetOpenWf.diagram_well_formed =
        some targetBody := by
  cases sourceCall with
  | root ambient locals =>
      let targetCall : CompilerCall layout.plugRaw :=
        layout.mappedFrameCall boundary (CompilerCall.root ambient locals)
      have targetOrigin : targetCall.origin =
          layout.frameRegion input.site := by
        exact (layout.mappedFrameCall_origin boundary
          (CompilerCall.root ambient locals)).trans
            (congrArg layout.frameRegion atSite)
      have targetExact : targetCall.fullContext.Exact
          (layout.frameRegion input.site) :=
        layout.mappedFrameCall_fullContext_exact consistent admissible boundary
          targetOpenWf (CompilerCall.root ambient locals) atSite sourceExact
      let frameMap := layout.frameFullMap consistent
        (CompilerCall.root ambient locals).fullContext targetCall.fullContext
        sourceExact targetExact
      let patternExact := CompiledSite.endpoint_fullContext_exact
        (State.ofOpen input.pattern) input.binderSpine.bodyContainer
      let patternMap := layout.patternFullMap consistent admissible
        (CompilerCall.root ambient locals).fullContext targetCall.fullContext
        sourceExact targetExact patternExact
      have patternBindersMapped : ∀ binder {arity relation},
          (CompiledSite.endpointCall (State.ofOpen input.pattern)
              input.binderSpine.bodyContainer).binders binder =
            some ⟨arity, relation⟩ →
          targetCall.binders (layout.binderRegion binder) =
            some ⟨arity, relationMap relation⟩ := by
        intro binder arity relation sourceLookup
        have impossible := hostLookup relation
        simp [CompilerCall.binders, BinderContext.empty] at impossible
      cases sourceBody with
      | mk sourceItems =>
          have sourceItemsCompiled :=
            CompilerCall.compile?_items_of_success input.frame.property
              (CompilerCall.root ambient locals) sourceCompiled
          have sourceItemsAtSite :
              compileItems? input.frame.val input.frame.property input.site
                  (CompilerCall.root ambient locals).fullContext
                  (CompilerCall.root ambient locals).binders
                  (localOccurrences input.frame.val input.site)
                  (fun _ member => member) = some sourceItems := by
            simpa only [atSite] using sourceItemsCompiled
          obtain ⟨targetItems, _, _, _, _, _, _, _, _, targetItemsCompiled,
              _, _, _, _, _, _, _⟩ :=
            layout.compileSpliceSiteItems consistent admissible
              targetOpenWf.diagram_well_formed
              (CompilerCall.root ambient locals).fullContext
              (CompilerCall.root ambient locals).binders
              targetCall.fullContext targetCall.binders frameMap patternMap
              relationMap patternBindersMapped (fun _ => rfl) sourceExact
              targetExact
              (layout.frameFullMap_get consistent _ _ sourceExact targetExact)
              (layout.patternFullMap_get consistent admissible _ _ sourceExact
                targetExact patternExact) sourceItemsAtSite
          let targetBody : CompiledRegion layout.plugRaw targetCall :=
            .mk targetItems
          refine ⟨targetBody, ?_⟩
          rw [CompilerCall.compile?_eq_compileItems?]
          have canonical :
              compileItems? layout.plugRaw targetOpenWf.diagram_well_formed
                  targetCall.origin
                  targetCall.fullContext targetCall.binders
                  (localOccurrences layout.plugRaw targetCall.origin)
                  (fun _ member => member) = some targetItems := by
            simpa only [targetOrigin] using targetItemsCompiled
          rw [canonical]
          rfl
  | nested origin outer rels binders =>
      let targetCall : CompilerCall layout.plugRaw :=
        layout.mappedFrameCall boundary
          (CompilerCall.nested origin outer rels binders)
      have targetOrigin : targetCall.origin =
          layout.frameRegion input.site := by
        exact (layout.mappedFrameCall_origin boundary
          (CompilerCall.nested origin outer rels binders)).trans
            (congrArg layout.frameRegion atSite)
      have targetExact : targetCall.fullContext.Exact
          (layout.frameRegion input.site) :=
        layout.mappedFrameCall_fullContext_exact consistent admissible boundary
          targetOpenWf (CompilerCall.nested origin outer rels binders) atSite
          sourceExact
      let frameMap := layout.frameFullMap consistent
        (CompilerCall.nested origin outer rels binders).fullContext
        targetCall.fullContext
        sourceExact targetExact
      let patternExact := CompiledSite.endpoint_fullContext_exact
        (State.ofOpen input.pattern) input.binderSpine.bodyContainer
      let patternMap := layout.patternFullMap consistent admissible
        (CompilerCall.nested origin outer rels binders).fullContext
        targetCall.fullContext
        sourceExact targetExact patternExact
      have patternBindersMapped : ∀ binder {arity relation},
          (CompiledSite.endpointCall (State.ofOpen input.pattern)
              input.binderSpine.bodyContainer).binders binder =
            some ⟨arity, relation⟩ →
          targetCall.binders (layout.binderRegion binder) =
            some ⟨arity, relationMap relation⟩ := by
        intro binder arity relation sourceLookup
        exact layout.terminalBinderMapped binders targetCall.binders
          (fun binder => by
            dsimp only [targetCall, mappedFrameCall, CompilerCall.binders]
            rw [layout.mapFrameBinders_frameRegion]) relationMap hostLookup
          binder sourceLookup
      cases sourceBody with
      | mk sourceItems =>
          have sourceItemsCompiled :=
            CompilerCall.compile?_items_of_success input.frame.property
              (CompilerCall.nested origin outer rels binders) sourceCompiled
          have sourceItemsAtSite :
              compileItems? input.frame.val input.frame.property input.site
                  (CompilerCall.nested origin outer rels binders).fullContext
                  (CompilerCall.nested origin outer rels binders).binders
                  (localOccurrences input.frame.val input.site)
                  (fun _ member => member) = some sourceItems := by
            simpa only [atSite] using sourceItemsCompiled
          obtain ⟨targetItems, _, _, _, _, _, _, _, _, targetItemsCompiled,
              _, _, _, _, _, _, _⟩ :=
            layout.compileSpliceSiteItems consistent admissible
              targetOpenWf.diagram_well_formed
              (CompilerCall.nested origin outer rels binders).fullContext
              (CompilerCall.nested origin outer rels binders).binders
              targetCall.fullContext
              targetCall.binders frameMap patternMap relationMap
              patternBindersMapped
              (fun binder => by
                dsimp only [targetCall, mappedFrameCall,
                  CompilerCall.binders]
                rw [layout.mapFrameBinders_frameRegion]
                cases binders binder <;> rfl)
              sourceExact targetExact
              (layout.frameFullMap_get consistent _ _ sourceExact targetExact)
              (layout.patternFullMap_get consistent admissible _ _ sourceExact
                targetExact patternExact) sourceItemsAtSite
          let targetBody : CompiledRegion layout.plugRaw targetCall :=
            .mk targetItems
          refine ⟨targetBody, ?_⟩
          rw [CompilerCall.compile?_eq_compileItems?]
          have canonical :
              compileItems? layout.plugRaw targetOpenWf.diagram_well_formed
                  targetCall.origin
                  targetCall.fullContext targetCall.binders
                  (localOccurrences layout.plugRaw targetCall.origin)
                  (fun _ member => member) = some targetItems := by
            simpa only [targetOrigin] using targetItemsCompiled
          rw [canonical]
          rfl

/-- Compile a nested splice endpoint at the exact target context inherited
from its already constructed parent. This is the same endpoint construction as
`compileSpliceSite`, without normalizing that context through a separate call
presentation. -/
theorem compileNestedSpliceSite
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (admissible : input.Admissible) (targetWf : layout.plugRaw.WellFormed)
    (sourceParent : Fin input.frame.val.regionCount)
    (sourceOuter : WireContext input.frame.val)
    (sourceBinders : BinderContext input.frame.val sourceRels)
    (targetOuter : WireContext layout.plugRaw)
    (targetBinders : BinderContext layout.plugRaw sourceRels)
    (atSite : sourceParent = input.site)
    (sourceExact : (sourceOuter.extend sourceParent).Exact sourceParent)
    (targetExact : (targetOuter.extend (layout.frameRegion sourceParent)).Exact
      (layout.frameRegion sourceParent))
    (frameBindersMapped : ∀ binder,
      targetBinders (layout.frameRegion binder) = sourceBinders binder)
    (relationMap : RelationRenaming
      (CompiledSite.endpointCall (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).rels sourceRels)
    (hostLookup : ∀ {arity}
      (relation : RelVar
        (CompiledSite.endpointCall (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).rels arity),
      sourceBinders (input.binderTarget
          (terminalRelationProxyEquiv input relation.index)) =
        some ⟨arity, relationMap relation⟩)
    {sourceBody : CompiledRegion input.frame.val
      (.nested sourceParent sourceOuter sourceRels sourceBinders)}
    (sourceCompiled : compileRegion? input.frame.val input.frame.property
      sourceParent sourceOuter sourceBinders = some sourceBody) :
    ∃ targetBody : CompiledRegion layout.plugRaw
        (.nested (layout.frameRegion sourceParent) targetOuter sourceRels
          targetBinders),
      compileRegion? layout.plugRaw targetWf
        (layout.frameRegion sourceParent) targetOuter targetBinders =
          some targetBody := by
  subst sourceParent
  let sourceFull := sourceOuter.extend input.site
  let targetFull := targetOuter.extend (layout.frameRegion input.site)
  have sourceFullExact : sourceFull.Exact input.site := by
    simpa [sourceFull] using sourceExact
  have targetFullExact : targetFull.Exact (layout.frameRegion input.site) := by
    simpa [targetFull] using targetExact
  let frameMap := layout.frameFullMap consistent sourceFull targetFull
    sourceFullExact targetFullExact
  let patternExact := CompiledSite.endpoint_fullContext_exact
    (State.ofOpen input.pattern) input.binderSpine.bodyContainer
  let patternMap := layout.patternFullMap consistent admissible sourceFull
    targetFull sourceFullExact targetFullExact patternExact
  have patternBindersMapped : ∀ binder {arity relation},
      (CompiledSite.endpointCall (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).binders binder =
        some ⟨arity, relation⟩ →
      targetBinders (layout.binderRegion binder) =
        some ⟨arity, relationMap relation⟩ := by
    intro binder arity relation sourceLookup
    exact layout.terminalBinderMapped sourceBinders targetBinders
      frameBindersMapped relationMap hostLookup binder sourceLookup
  have frameBindersMapped' : ∀ binder,
      targetBinders (layout.frameRegion binder) =
        (sourceBinders binder).map fun relation =>
          ⟨relation.1, relation.2⟩ := by
    intro binder
    rw [frameBindersMapped]
    cases sourceBinders binder <;> rfl
  cases sourceBody with
  | mk sourceItems =>
      have sourceItemsCompiled := compileRegion?_items_of_success
        input.frame.property input.site sourceOuter sourceBinders
        sourceCompiled
      have sourceItemsAtSite :
          compileItems? input.frame.val input.frame.property input.site
              sourceFull sourceBinders
              (localOccurrences input.frame.val input.site)
              (fun _ member => member) = some sourceItems := by
        simpa only [sourceFull] using sourceItemsCompiled
      obtain ⟨targetItems, _, _, _, _, _, _, _, _, targetItemsCompiled,
          _, _, _, _, _, _, _⟩ :=
        layout.compileSpliceSiteItems consistent admissible targetWf
          sourceFull sourceBinders targetFull targetBinders frameMap patternMap
          relationMap patternBindersMapped frameBindersMapped'
          sourceFullExact targetFullExact
          (layout.frameFullMap_get consistent _ _
            sourceFullExact targetFullExact)
          (layout.patternFullMap_get consistent admissible _ _
            sourceFullExact targetFullExact patternExact)
          sourceItemsAtSite
      let targetBody : CompiledRegion layout.plugRaw
          (.nested (layout.frameRegion input.site) targetOuter sourceRels
            targetBinders) := .mk targetItems
      refine ⟨targetBody, ?_⟩
      rw [compileRegion?_eq_compileItems?]
      have canonical :
          compileItems? layout.plugRaw targetWf
              (layout.frameRegion input.site) targetFull targetBinders
              (localOccurrences layout.plugRaw
                (layout.frameRegion input.site))
              (fun _ member => member) = some targetItems := by
        exact targetItemsCompiled
      rw [canonical]
      rfl

end Splice.Input.PlugLayout

end VisualProof.Concrete
