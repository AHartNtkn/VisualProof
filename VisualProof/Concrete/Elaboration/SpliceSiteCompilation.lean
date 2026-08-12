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
    (layout.mapFrameBinders sourceBinders)
        (layout.binderRegion binder) =
      some ⟨arity, relationMap relation⟩ := by
  have binderEq : binder = input.binderSpine.proxy
      (terminalRelationProxyEquiv input relation.index) := by
    have owner := (CompiledSite.endpoint_binders_enumeration
      (State.ofOpen input.pattern) input.binderSpine.bodyContainer)
        |>.lookup_owner relation sourceLookup
    exact owner.symm.trans
      (terminalRelationProxyEquiv_binder input relation.index).symm
  subst binder
  rw [layout.binderRegion_proxy, layout.mapFrameBinders_frameRegion]
  exact hostLookup relation

/-- Compile the splice endpoint in its actual target occurrence order. The
result is constructed from the retained frame blocks and the terminal pattern
blocks; no target focus or target compiler search is involved. -/
private theorem compileSpliceSiteParts
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (admissible : input.Admissible) (targetWf : layout.plugRaw.WellFormed)
    (sourceOuter : WireContext input.frame.val)
    (sourceBinders : BinderContext input.frame.val sourceRels)
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
    (sourceExact : (sourceOuter.extend input.site).Exact input.site)
    {sourceBody : CompiledRegion input.frame.val
      (.nested input.site sourceOuter sourceRels sourceBinders)}
    (sourceCompiled : compileRegion? input.frame.val input.frame.property
      input.site sourceOuter sourceBinders = some sourceBody) :
    ∃ (targetBody : CompiledRegion layout.plugRaw
          (.nested (layout.frameRegion input.site)
            (layout.mapFrameContext sourceOuter) sourceRels
            (layout.mapFrameBinders sourceBinders)))
        (sourceNodes sourceChildren : CompiledItems input.frame.val
          (sourceOuter.extend input.site) sourceRels sourceBinders)
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
          ((layout.mapFrameContext sourceOuter).extend
            (layout.frameRegion input.site)) sourceRels
          (layout.mapFrameBinders sourceBinders)),
      compileRegion? layout.plugRaw targetWf
          (layout.frameRegion input.site) (layout.mapFrameContext sourceOuter)
          (layout.mapFrameBinders sourceBinders) = some targetBody ∧
      sourceBody.items = sourceNodes.append sourceChildren ∧
      (CompiledSite.endpoint (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).items =
        patternNodesSource.append patternChildrenSource ∧
      targetBody.items = (frameNodes.append patternNodes).append
        (frameChildren.append patternChildren) ∧
      frameNodes.erase = (sourceNodes.erase.renameWires
        (frameSiteFullMap layout consistent admissible.terminal_body
          sourceOuter)).renameRelations (fun relation => relation) ∧
      patternNodes.erase =
        (patternNodesSource.erase.renameWires
          (patternSiteFullMap layout consistent admissible sourceOuter sourceExact
            (CompiledSite.endpoint_fullContext_exact
              (State.ofOpen input.pattern) input.binderSpine.bodyContainer))).renameRelations
            relationMap ∧
      frameChildren.erase = (sourceChildren.erase.renameWires
        (frameSiteFullMap layout consistent admissible.terminal_body
          sourceOuter)).renameRelations (fun relation => relation) ∧
      patternChildren.erase =
        (patternChildrenSource.erase.renameWires
          (patternSiteFullMap layout consistent admissible sourceOuter sourceExact
            (CompiledSite.endpoint_fullContext_exact
              (State.ofOpen input.pattern) input.binderSpine.bodyContainer))).renameRelations
            relationMap := by
  let patternState := State.ofOpen input.pattern
  let patternCall := CompiledSite.endpointCall patternState
    input.binderSpine.bodyContainer
  let sourceFull := sourceOuter.extend input.site
  let targetOuter := layout.mapFrameContext sourceOuter
  let targetBinders := layout.mapFrameBinders sourceBinders
  let targetFull := targetOuter.extend (layout.frameRegion input.site)
  let frameMap := frameSiteFullMap layout consistent
    admissible.terminal_body sourceOuter
  have patternExact : patternCall.fullContext.Exact
      input.binderSpine.bodyContainer := by
    exact CompiledSite.endpoint_fullContext_exact patternState
      input.binderSpine.bodyContainer
  let patternMap := patternSiteFullMap layout consistent admissible sourceOuter
    sourceExact patternExact
  have targetExact : targetFull.Exact (layout.frameRegion input.site) := by
    exact layout.siteTargetFull_exact consistent admissible.terminal_body
      sourceOuter sourceExact
  have frameGet : ∀ index,
      targetFull.get (frameMap index) =
        layout.frameWireMap (sourceFull.get index) := by
    exact layout.frameSiteFullMap_get consistent admissible.terminal_body
      sourceOuter
  have patternGet : ∀ index,
      targetFull.get (patternMap index) =
        layout.patternWireMap (patternCall.fullContext.get index) := by
    exact layout.patternSiteFullMap_get consistent admissible sourceOuter
      sourceExact patternExact
  have frameBindersMapped : ∀ binder,
      targetBinders (layout.frameRegion binder) =
        (sourceBinders binder).map fun relation =>
          ⟨relation.1, relation.2⟩ := by
    intro binder
    dsimp only [targetBinders]
    rw [layout.mapFrameBinders_frameRegion]
    cases sourceBinders binder with
    | none => rfl
    | some relation =>
        cases relation
        rfl
  have sourceItemsCompiled := compileRegion?_items_of_success
    input.frame.property input.site sourceOuter sourceBinders sourceCompiled
  obtain ⟨sourceNodes, sourceChildren, sourceNodesCompiled,
      sourceChildrenCompiled, sourceItemsEq⟩ :=
    compileItems?_append_inv input.frame.property input.site sourceFull
      sourceBinders (localNodeOccurrences input.frame.val input.site)
      (localChildOccurrences input.frame.val input.site)
      (fun _ member => member) sourceItemsCompiled
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
        layout.terminalBinderMapped sourceBinders relationMap hostLookup binder
          sourceLookup)
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
    simpa only [targetFull, targetBinders] using frameNodesCompiled
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
      mappedOccurrences.symm _ _).trans (by
        simpa only [targetFull, targetBinders] using patternNodesCompiled)
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
                have pushedBinders :
                    targetBinders.push (layout.frameRegion child) arity =
                      layout.mapFrameBinders
                        (sourceBinders.push child arity) := by
                  dsimp only [targetBinders]
                  exact layout.mapFrameBinders_push sourceBinders child arity
                have pushedMapped : ∀ binder,
                    (targetBinders.push (layout.frameRegion child) arity)
                        (layout.frameRegion binder) =
                      (sourceBinders.push child arity binder).map
                        fun relation => ⟨relation.1,
                          RelationRenaming.lift
                            (fun relation => relation) arity relation.2⟩ := by
                  intro binder
                  rw [pushedBinders, layout.mapFrameBinders_frameRegion]
                  cases lookup : sourceBinders.push child arity binder with
                  | none => rfl
                  | some relation =>
                      simp only [Option.map_some,
                        RelationRenaming.lift_id]
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
                      layout.terminalBinderMapped sourceBinders relationMap
                        hostLookup binder sourceLookup)
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
                    layout.terminalBinderMapped sourceBinders relationMap
                      hostLookup binder sourceLookup)
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
      occurrences.symm _ _).trans (by
        simpa only [targetFull, targetBinders] using frameChildrenCompiled)
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
      mappedOccurrences.symm _ _).trans (by
        simpa only [targetFull, targetBinders] using patternChildrenCompiled)
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
  let targetBody : CompiledRegion layout.plugRaw
      (.nested (layout.frameRegion input.site) targetOuter sourceRels
        targetBinders) :=
    .mk targetItems
  refine ⟨targetBody, sourceNodes, sourceChildren, patternNodesSource,
    patternChildrenSource, frameNodes, patternNodes, frameChildren,
    patternChildren, ?_, sourceItemsEq, patternItemsEq, rfl,
    frameNodesErase, patternNodesErase, frameChildrenErase,
    patternChildrenErase⟩
  rw [compileRegion?_eq_compileItems?]
  change Option.map
    (fun items => (CompiledRegion.mk items : CompiledRegion layout.plugRaw
      (.nested (layout.frameRegion input.site) targetOuter sourceRels
        targetBinders)))
    (compileItems? layout.plugRaw targetWf
      (layout.frameRegion input.site) targetFull targetBinders
      (localOccurrences layout.plugRaw (layout.frameRegion input.site)) _) =
        some targetBody
  rw [targetItemsCanonical]
  rfl

end Splice.Input.PlugLayout

end VisualProof.Concrete
