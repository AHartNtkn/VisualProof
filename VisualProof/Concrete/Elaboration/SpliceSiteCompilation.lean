import VisualProof.Concrete.Elaboration.SpliceCompilation

/-! Construct the exact compiler result at the splice endpoint. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open Theory
open Elaboration

namespace Splice.Input.PlugLayout

private theorem listGetCast {first second : List α}
    (equality : first = second) (index : Fin first.length) :
    first.get index = second.get
      (Fin.cast (congrArg List.length equality) index) := by
  subst second
  rfl

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

theorem siteMappedFull_exact
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (sourceFull : WireContext input.frame.val)
    (sourceExact : sourceFull.Exact input.site) :
    WireContext.Exact
      (((sourceFull.map layout.frameWireMap : WireContext layout.plugRaw) ++
        layout.bodyLocalWires) : WireContext layout.plugRaw)
      (layout.frameRegion input.site) := by
  have targetNodup :
      ((sourceFull.map layout.frameWireMap : WireContext layout.plugRaw) ++
        layout.bodyLocalWires).Nodup := by
    rw [List.nodup_append]
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
  refine ⟨targetNodup, ?_⟩
  intro targetWire
  refine Fin.addCases (motive := fun targetWire =>
    targetWire ∈
        (sourceFull.map layout.frameWireMap :
          WireContext layout.plugRaw) ++ layout.bodyLocalWires ↔
      layout.plugRaw.Encloses (layout.plugRaw.wires targetWire).scope
        (layout.frameRegion input.site)) (fun quotient => ?_)
    (fun internal => ?_) targetWire
  · change layout.frameWire quotient ∈
        (sourceFull.map layout.frameWireMap :
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
        (sourceFull.map layout.frameWireMap :
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

theorem terminalBinderMapped
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

/-- The sole presentation change at the endpoint: interchange the pattern-node
and retained-frame-child blocks. -/
private noncomputable def braidSpliceSiteBlocks
    (frameNodes patternNodes frameChildren patternChildren :
      ItemSeq wires rels) :
    ItemSeqIso (FiniteEquiv.refl (Fin wires)) rels
      ((frameNodes.append patternNodes).append
        (frameChildren.append patternChildren))
      ((frameNodes.append frameChildren).append
        (patternNodes.append patternChildren)) := by
  let middle := ItemSeqIso.appendCommRename patternNodes frameChildren
    (FiniteEquiv.refl (Fin wires))
  have middle' : ItemSeqIso (FiniteEquiv.refl (Fin wires)) rels
      (patternNodes.append frameChildren)
      (frameChildren.append patternNodes) := by
    simpa [FiniteEquiv.refl, ItemSeq.renameWires_id] using middle
  let braidedPrefix := ItemSeqIso.append (ItemSeqIso.refl frameNodes) middle'
  let all := ItemSeqIso.append braidedPrefix (ItemSeqIso.refl patternChildren)
  simpa only [ItemSeq.renameWires_id, ItemSeq.append_assoc] using all

/-- Compile the insertion site's item block and identify its erased region
with the intrinsic splice kernel. This item-level contract is shared by root
and nested compiler calls; call packaging is performed exactly once by the
caller. -/
theorem compileSpliceSiteItems_semantic
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (admissible : input.Admissible) (targetWf : layout.plugRaw.WellFormed)
    (sourceOuter : WireContext input.frame.val)
    (sourceLocal : WireContext input.frame.val)
    (sourceBinders : BinderContext input.frame.val sourceRels)
    (targetOuter : WireContext layout.plugRaw)
    (targetLocal : WireContext layout.plugRaw)
    (targetBinders : BinderContext layout.plugRaw sourceRels)
    (frameMap : Fin (sourceOuter ++ sourceLocal).length →
      Fin (targetOuter ++ targetLocal).length)
    (patternMap : Fin (CompiledSite.endpointCall
      (State.ofOpen input.pattern) input.binderSpine.bodyContainer
        ).fullContext.length →
      Fin (targetOuter ++ targetLocal).length)
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
    (sourceExact : (sourceOuter ++ sourceLocal).Exact input.site)
    (targetExact : (targetOuter ++ targetLocal).Exact
      (layout.frameRegion input.site))
    (frameGet : ∀ index,
      (targetOuter ++ targetLocal).get
          (frameMap index) =
        layout.frameWireMap ((sourceOuter ++ sourceLocal).get index))
    (patternGet : ∀ index,
      (targetOuter ++ targetLocal).get
          (patternMap index) = layout.patternWireMap
        ((CompiledSite.endpointCall (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).fullContext.get index))
    (outerWire : FiniteEquiv (Fin targetOuter.length)
      (Fin sourceOuter.length))
    (localWire : FiniteEquiv
      (Fin targetLocal.length)
      (Fin (sourceLocal.length +
        (CompiledSite.endpointCall (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).localContext.length)))
    (materialWireMap : Fin (CompiledSite.endpointCall
      (State.ofOpen input.pattern)
      input.binderSpine.bodyContainer).outerContext.length →
        Fin (sourceOuter.length + sourceLocal.length))
    (frameFactor : ∀ index,
      extendWireEquiv outerWire localWire
          (Fin.cast (by exact List.length_append)
            (frameMap index)) =
        Region.adjoinHostWire sourceOuter.length
          sourceLocal.length
          (CompiledSite.endpointCall (State.ofOpen input.pattern)
            input.binderSpine.bodyContainer).localContext.length
          (Fin.cast (by exact List.length_append) index))
    (patternFactor : ∀ index,
      extendWireEquiv outerWire localWire
          (Fin.cast (by exact List.length_append)
            (patternMap index)) =
        Region.adjoinMaterialWire sourceOuter.length
          sourceLocal.length
          (CompiledSite.endpointCall (State.ofOpen input.pattern)
            input.binderSpine.bodyContainer).localContext.length
          (extendWireRenaming materialWireMap
            (CompiledSite.endpointCall (State.ofOpen input.pattern)
              input.binderSpine.bodyContainer).localContext.length
            (Fin.cast (CompilerCall.fullContext_length
              (CompiledSite.endpointCall (State.ofOpen input.pattern)
                input.binderSpine.bodyContainer)) index)))
    {sourceItems : CompiledItems input.frame.val
      (sourceOuter ++ sourceLocal) sourceRels sourceBinders}
    (sourceCompiled : compileItems? input.frame.val input.frame.property
      input.site (sourceOuter ++ sourceLocal) sourceBinders
      (localOccurrences input.frame.val input.site) (fun _ member => member) =
        some sourceItems) :
    Nonempty (Σ targetItems : CompiledItems layout.plugRaw
        (targetOuter ++ targetLocal) sourceRels targetBinders,
      PSigma (fun _ : compileItems? layout.plugRaw targetWf
          (layout.frameRegion input.site) (targetOuter ++ targetLocal)
          targetBinders (localOccurrences layout.plugRaw
            (layout.frameRegion input.site)) (fun _ member => member) =
        some targetItems =>
      RegionIso outerWire sourceRels
        (.mk targetLocal.length
          (targetItems.erase.castWiresEq
            (by exact List.length_append)))
        (Region.spliceAt
          sourceLocal.length
          (sourceItems.erase.castWiresEq
            (by exact List.length_append))
          (CompiledSite.body (State.ofOpen input.pattern)
            input.binderSpine.bodyContainer)
          materialWireMap relationMap))) := by
  let sourceFull := sourceOuter ++ sourceLocal
  let targetFull := targetOuter ++ targetLocal
  obtain ⟨targetItems, sourceNodes, sourceChildren, patternNodesSource,
      patternChildrenSource, frameNodes, patternNodes, frameChildren,
      patternChildren, targetItemsCompiled, sourceItemsEq, patternItemsEq,
      targetItemsEq, frameNodesErase, patternNodesErase, frameChildrenErase,
      patternChildrenErase⟩ :=
    layout.compileSpliceSiteItems consistent admissible targetWf sourceFull
      sourceBinders targetFull targetBinders frameMap patternMap relationMap
      patternBindersMapped frameBindersMapped sourceExact targetExact frameGet
      patternGet sourceCompiled
  let patternCall := CompiledSite.endpointCall (State.ofOpen input.pattern)
    input.binderSpine.bodyContainer
  let sourceHost : ItemSeq (sourceOuter.length + sourceLocal.length) sourceRels :=
    sourceItems.erase.castWiresEq (by exact List.length_append)
  let material := CompiledSite.body (State.ofOpen input.pattern)
    input.binderSpine.bodyContainer
  let canonical := Region.spliceAt sourceLocal.length sourceHost
    material materialWireMap relationMap
  let outputWire := extendWireEquiv outerWire localWire
  have makeBlock {sourceWires : Nat}
      (base : ItemSeq sourceWires sourceRels)
      (target : ItemSeq targetFull.length sourceRels)
      (blockMap : Fin sourceWires → Fin targetFull.length)
      (canonicalMap : Fin sourceWires →
        Fin (sourceOuter.length +
          (sourceLocal.length + patternCall.localContext.length)))
      (targetErase : target = base.renameWires blockMap)
      (factor : ∀ index,
        outputWire (Fin.cast (by exact List.length_append)
          (blockMap index)) =
          canonicalMap index) :
      ItemSeqIso outputWire sourceRels
        (target.castWiresEq (by exact List.length_append))
        (base.renameWires canonicalMap) := by
    have renamed := ItemSeqIso.renameWiresEquiv
      (target.castWiresEq (by exact List.length_append)) outputWire
    have targetEq :
        (target.castWiresEq (by exact List.length_append)).renameWires
            outputWire =
          base.renameWires canonicalMap := by
      rw [ItemSeq.castWiresEq_eq_renameWires, targetErase]
      calc
        ((base.renameWires blockMap).renameWires
            (Fin.cast (by exact List.length_append))).renameWires
              outputWire =
            (base.renameWires
              ((Fin.cast (by exact List.length_append)) ∘
                blockMap)
              ).renameWires outputWire := by
                exact congrArg (fun items => items.renameWires outputWire)
                  (ItemSeq.renameWires_comp base blockMap
                    (Fin.cast (by exact List.length_append)))
        _ =
            base.renameWires
              (outputWire ∘ Fin.cast
                (by exact List.length_append) ∘
                blockMap) := by
              exact ItemSeq.renameWires_comp base
                ((Fin.cast (by exact List.length_append)) ∘
                  blockMap)
                outputWire
        _ = _ := by
          apply congrArg (fun wireMap => base.renameWires wireMap)
          funext index
          exact factor index
    exact targetEq ▸ renamed
  have frameNodesErase' : frameNodes.erase =
      sourceNodes.erase.renameWires frameMap := by
    simpa only [ItemSeq.renameRelations_id] using frameNodesErase
  have frameChildrenErase' : frameChildren.erase =
      sourceChildren.erase.renameWires frameMap := by
    simpa only [ItemSeq.renameRelations_id] using frameChildrenErase
  have patternNodesErase' : patternNodes.erase =
      (patternNodesSource.erase.renameRelations relationMap).renameWires
        patternMap := by
    exact patternNodesErase.trans
      (ItemSeq.renameWires_renameRelations patternNodesSource.erase patternMap
        relationMap)
  have patternChildrenErase' : patternChildren.erase =
      (patternChildrenSource.erase.renameRelations relationMap).renameWires
        patternMap := by
    exact patternChildrenErase.trans
      (ItemSeq.renameWires_renameRelations patternChildrenSource.erase patternMap
        relationMap)
  let hostMap := Region.adjoinHostWire sourceOuter.length
    sourceLocal.length patternCall.localContext.length ∘
      Fin.cast (by exact List.length_append)
  let patternCanonicalMap := Region.adjoinMaterialWire sourceOuter.length
    sourceLocal.length patternCall.localContext.length ∘
      extendWireRenaming materialWireMap patternCall.localContext.length ∘
        Fin.cast patternCall.fullContext_length
  have frameBlock := makeBlock sourceNodes.erase frameNodes.erase frameMap
    hostMap frameNodesErase' frameFactor
  have frameChildrenBlock := makeBlock sourceChildren.erase
    frameChildren.erase frameMap hostMap frameChildrenErase' frameFactor
  have patternBlock := makeBlock
    (patternNodesSource.erase.renameRelations relationMap) patternNodes.erase
    patternMap patternCanonicalMap patternNodesErase' patternFactor
  have patternChildrenBlock := makeBlock
    (patternChildrenSource.erase.renameRelations relationMap)
    patternChildren.erase patternMap patternCanonicalMap patternChildrenErase'
    patternFactor
  have materialEq : material =
      patternCall.finish
        ((patternNodesSource.append patternChildrenSource).erase) := by
    have erase_finish {d : Diagram} {call : CompilerCall d}
        (body : CompiledRegion d call) :
        body.erase = call.finish body.items.erase := by
      cases body
      rfl
    simp only [material, CompiledSite.body, patternCall]
    rw [erase_finish]
    rw [← patternItemsEq]
    rfl
  refine ⟨⟨targetItems, ⟨targetItemsCompiled, ?_⟩⟩⟩
  rw [show CompiledSite.body (State.ofOpen input.pattern)
    input.binderSpine.bodyContainer = _ from materialEq]
  simp only [Region.spliceAt, Region.adjoinAt, CompiledItems.erase_append]
  refine RegionIso.mk localWire ?_
  let castFrameNodes := frameNodes.erase.castWiresEq
    (by exact List.length_append)
  let castPatternNodes := patternNodes.erase.castWiresEq
    (by exact List.length_append)
  let castFrameChildren := frameChildren.erase.castWiresEq
    (by exact List.length_append)
  let castPatternChildren := patternChildren.erase.castWiresEq
    (by exact List.length_append)
  let braid := braidSpliceSiteBlocks castFrameNodes castPatternNodes
    castFrameChildren castPatternChildren
  let frameIso := ItemSeqIso.append frameBlock frameChildrenBlock
  let patternIso := ItemSeqIso.append patternBlock patternChildrenBlock
  let blocks := ItemSeqIso.append frameIso patternIso
  have all := ItemSeqIso.trans braid blocks
  have targetItemsErase : targetItems.erase =
      (frameNodes.erase.append patternNodes.erase).append
        (frameChildren.erase.append patternChildren.erase) := by
    exact (congrArg CompiledItems.erase targetItemsEq).trans
      (by simp only [CompiledItems.erase_append])
  have sourceItemsErase : sourceItems.erase =
      sourceNodes.erase.append sourceChildren.erase := by
    exact (congrArg CompiledItems.erase sourceItemsEq).trans
      (CompiledItems.erase_append sourceNodes sourceChildren)
  have targetPresentation :
      targetItems.erase.castWiresEq
          (by exact List.length_append) =
        ((frameNodes.erase.castWiresEq
          (by exact List.length_append)).append
          (patternNodes.erase.castWiresEq
            (by exact List.length_append))).append
        ((frameChildren.erase.castWiresEq
          (by exact List.length_append)).append
          (patternChildren.erase.castWiresEq
            (by exact List.length_append))) := by
    rw [targetItemsErase]
    calc
      _ = ((frameNodes.erase.append patternNodes.erase).castWiresEq
            (by exact List.length_append)).append
          ((frameChildren.erase.append patternChildren.erase).castWiresEq
            (by exact List.length_append)) :=
        ItemSeq.castWiresEq_append _ _ _
      _ = _ := by
        calc
          _ = ((frameNodes.erase.castWiresEq
                  (by exact List.length_append)).append
                (patternNodes.erase.castWiresEq
                  (by exact List.length_append))).append
              ((frameChildren.erase.append patternChildren.erase
                ).castWiresEq
                  (by exact List.length_append)) :=
            congrArg (fun items => items.append
              ((frameChildren.erase.append patternChildren.erase
                ).castWiresEq
                  (by exact List.length_append)))
              (ItemSeq.castWiresEq_append _ _ _)
          _ = _ := congrArg
            (fun items => ((frameNodes.erase.castWiresEq
                (by exact List.length_append)).append
              (patternNodes.erase.castWiresEq
                (by exact List.length_append))).append items)
            (ItemSeq.castWiresEq_append _ _ _)
  have hostPresentation :
      ((sourceNodes.erase.append sourceChildren.erase).castWiresEq
          (by exact List.length_append)).renameWires
          (Region.adjoinHostWire sourceOuter.length
            sourceLocal.length patternCall.localContext.length) =
        (sourceNodes.erase.renameWires hostMap).append
          (sourceChildren.erase.renameWires hostMap) := by
    rw [ItemSeq.castWiresEq_eq_renameWires]
    exact (ItemSeq.renameWires_comp
      (sourceNodes.erase.append sourceChildren.erase)
      (Fin.cast (by exact List.length_append))
      (Region.adjoinHostWire sourceOuter.length
        sourceLocal.length patternCall.localContext.length)).trans
      (by
        simpa only [hostMap] using ItemSeq.renameWires_append
          sourceNodes.erase sourceChildren.erase
          (Region.adjoinHostWire sourceOuter.length
              sourceLocal.length patternCall.localContext.length ∘
            Fin.cast (by exact List.length_append)))
  have patternPresentation :
      (((patternNodesSource.erase.append patternChildrenSource.erase
          ).castWiresEq patternCall.fullContext_length).renameRelations
          relationMap).renameWires
          (Region.adjoinMaterialWire sourceOuter.length
              sourceLocal.length patternCall.localContext.length ∘
            extendWireRenaming materialWireMap
              patternCall.localContext.length) =
        ((patternNodesSource.erase.renameRelations relationMap).renameWires
          patternCanonicalMap).append
        ((patternChildrenSource.erase.renameRelations relationMap).renameWires
          patternCanonicalMap) := by
    rw [ItemSeq.castWiresEq_eq_renameWires,
      ItemSeq.renameWires_renameRelations]
    calc
      _ = ((patternNodesSource.erase.append patternChildrenSource.erase
            ).renameRelations relationMap).renameWires
          ((Region.adjoinMaterialWire sourceOuter.length
                sourceLocal.length patternCall.localContext.length ∘
              extendWireRenaming materialWireMap
                patternCall.localContext.length) ∘
            Fin.cast patternCall.fullContext_length) :=
        ItemSeq.renameWires_comp
          ((patternNodesSource.erase.append patternChildrenSource.erase
            ).renameRelations relationMap)
          (Fin.cast patternCall.fullContext_length)
          (Region.adjoinMaterialWire sourceOuter.length
              sourceLocal.length patternCall.localContext.length ∘
            extendWireRenaming materialWireMap
              patternCall.localContext.length)
      _ = ((patternNodesSource.erase.renameRelations relationMap).append
            (patternChildrenSource.erase.renameRelations relationMap)
          ).renameWires patternCanonicalMap := by
        exact congrArg (fun items => items.renameWires patternCanonicalMap)
          (ItemSeq.renameRelations_append patternNodesSource.erase
            patternChildrenSource.erase relationMap)
      _ = _ := ItemSeq.renameWires_append _ _ _
  have patternPresentation' :
      (((patternCall.castFullItems
          (patternNodesSource.erase.append patternChildrenSource.erase)
        ).renameWires
          (extendWireRenaming materialWireMap patternCall.localContext.length)
        ).renameRelations relationMap).renameWires
          (Region.adjoinMaterialWire sourceOuter.length sourceLocal.length
            patternCall.localContext.length) =
        ((patternNodesSource.erase.renameRelations relationMap).renameWires
          patternCanonicalMap).append
        ((patternChildrenSource.erase.renameRelations relationMap).renameWires
          patternCanonicalMap) := by
    rw [ItemSeq.renameWires_renameRelations, ItemSeq.renameWires_comp]
    exact patternPresentation
  have wirePresentation :
      (FiniteEquiv.refl (Fin (targetOuter.length + targetLocal.length))).trans
        outputWire = outputWire := by
    apply FiniteEquiv.ext
    intro index
    rfl
  have all' := wirePresentation ▸ all
  change ItemSeqIso outputWire sourceRels
    (targetItems.erase.castWiresEq
      (by exact List.length_append)) _
  rw [targetPresentation]
  rw [sourceItemsErase]
  rw [hostPresentation]
  rw [patternPresentation']
  simpa only [castFrameNodes, castPatternNodes, castFrameChildren,
    castPatternChildren] using all'

private theorem bodySourceLocalWires_eq_endpointLocal
    (layout : PlugLayout input) :
    layout.bodySourceLocalWires =
      (CompiledSite.endpointCall (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).localContext := by
  let patternState := State.ofOpen input.pattern
  let call := CompiledSite.endpointCall patternState
    input.binderSpine.bodyContainer
  by_cases atRoot : input.binderSpine.bodyContainer =
      input.pattern.val.diagram.root
  · have callEq : call = .root input.pattern.val.exposedWires
        input.pattern.val.hiddenWires := by
      have focusEq := CompiledSite.focus_root patternState
      simpa [call, patternState, atRoot] using
        congrArg CompiledFocus.endpointCall focusEq
    change layout.bodySourceLocalWires = call.localContext
    rw [callEq]
    unfold PlugLayout.bodySourceLocalWires SurvivorDomain.enumeration
      OpenDiagram.hiddenWires exactScopeWires filterFin
    simp only [CompilerCall.localContext]
    rw [List.filter_filter, List.filter_filter]
    apply List.filter_congr
    intro wire _
    by_cases exposed : wire ∈ input.pattern.val.exposedWires <;>
      by_cases hscoped : (input.pattern.val.diagram.wires wire).scope =
        input.pattern.val.diagram.root <;> rw [layout.internalWires_exact] <;>
        simp [atRoot, exposed, hscoped]
  · change layout.bodySourceLocalWires = call.localContext
    cases callEq : call with
    | root ambient locals =>
        have originEq := CompiledSite.endpoint_origin patternState
          input.binderSpine.bodyContainer
        simp [call, callEq, CompilerCall.origin] at originEq
        exact (atRoot originEq.symm).elim
    | nested origin outer rels binders =>
        have originEq : origin = input.binderSpine.bodyContainer := by
          simpa [call, callEq, CompilerCall.origin] using
            CompiledSite.endpoint_origin patternState
              input.binderSpine.bodyContainer
        change layout.bodySourceLocalWires =
          exactScopeWires input.pattern.val.diagram origin
        subst origin
        unfold PlugLayout.bodySourceLocalWires
        let predicate := fun wire : Fin input.pattern.val.diagram.wireCount =>
          decide ((input.pattern.val.diagram.wires wire).scope =
            input.binderSpine.bodyContainer)
        have survives : ∀ wire, predicate wire = true →
            layout.internalWires.survives wire = true := by
          intro wire accepted
          rw [layout.internalWires_exact]
          apply decide_eq_true
          intro exposed
          have rootScope := input.pattern.property.exposed_root_scoped exposed
          exact atRoot ((of_decide_eq_true accepted).symm.trans rootScope)
        unfold exactScopeWires filterFin SurvivorDomain.enumeration
        change List.filter predicate
          (List.filter layout.internalWires.survives
            (allFin input.pattern.val.diagram.wireCount)) =
          List.filter predicate (allFin input.pattern.val.diagram.wireCount)
        rw [List.filter_filter]
        apply List.filter_congr
        intro wire _
        by_cases accepted : predicate wire = true
        · have survivor := survives wire accepted
          simp [accepted, survivor]
        · simp [accepted]

theorem bodyLocalWires_eq_endpointLocalMap
    (layout : PlugLayout input) :
    layout.bodyLocalWires =
      (CompiledSite.endpointCall (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).localContext.map
          layout.patternWireMap := by
  unfold PlugLayout.bodyLocalWires
  let positions := filterFin fun wire : layout.internalWires.Carrier =>
    decide ((input.pattern.val.diagram.wires
      (layout.internalWires.origin wire)).scope =
        input.binderSpine.bodyContainer)
  calc
    positions.map layout.internalWire =
        positions.map (layout.patternWireMap ∘
          layout.internalWires.origin) := by
      apply List.map_congr_left
      intro wire _
      exact (layout.patternWireMap_internal wire).symm
    _ = (positions.map layout.internalWires.origin).map
        layout.patternWireMap := List.map_map.symm
    _ = _ := by
      rw [show positions.map layout.internalWires.origin =
          layout.bodySourceLocalWires by exact layout.bodyLocalOrigins,
        layout.bodySourceLocalWires_eq_endpointLocal]

private noncomputable def canonicalFrameMap
    (layout : PlugLayout input) (sourceCall : CompilerCall input.frame.val)
    (targetCall : CompilerCall layout.plugRaw)
    (targetEq : targetCall.fullContext =
      sourceCall.fullContext.map layout.frameWireMap ++
        (CompiledSite.endpointCall (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).localContext.map
            layout.patternWireMap) :
    Fin sourceCall.fullContext.length →
      Fin targetCall.fullContext.length :=
  fun index => ⟨index.val, by
    rw [targetEq]
    have lengthEq :
        (sourceCall.fullContext.map layout.frameWireMap ++
          (CompiledSite.endpointCall (State.ofOpen input.pattern)
            input.binderSpine.bodyContainer).localContext.map
              layout.patternWireMap).length =
        sourceCall.fullContext.length +
          (CompiledSite.endpointCall (State.ofOpen input.pattern)
            input.binderSpine.bodyContainer).localContext.length := by
      simp only [List.length_append, List.length_map]
      rfl
    exact lengthEq.symm ▸ (by omega)⟩

private noncomputable def canonicalPatternMap
    (layout : PlugLayout input) (sourceCall : CompilerCall input.frame.val)
    (targetCall : CompilerCall layout.plugRaw)
    (targetEq : targetCall.fullContext =
      sourceCall.fullContext.map layout.frameWireMap ++
        (CompiledSite.endpointCall (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).localContext.map
            layout.patternWireMap)
    (materialWireMap : Fin (CompiledSite.endpointCall
      (State.ofOpen input.pattern) input.binderSpine.bodyContainer
        ).outerContext.length → Fin sourceCall.fullContext.length) :
    Fin (CompiledSite.endpointCall (State.ofOpen input.pattern)
      input.binderSpine.bodyContainer).fullContext.length →
      Fin targetCall.fullContext.length :=
  fun index =>
    let patternCall := CompiledSite.endpointCall (State.ofOpen input.pattern)
      input.binderSpine.bodyContainer
    let split := Fin.cast patternCall.fullContext_length index
    Fin.addCases
      (fun outer => ⟨(materialWireMap outer).val, by
        rw [targetEq]
        have lengthEq :
            (sourceCall.fullContext.map layout.frameWireMap ++
              (CompiledSite.endpointCall (State.ofOpen input.pattern)
                input.binderSpine.bodyContainer).localContext.map
                  layout.patternWireMap).length =
            sourceCall.fullContext.length +
              (CompiledSite.endpointCall (State.ofOpen input.pattern)
                input.binderSpine.bodyContainer).localContext.length := by
          simp only [List.length_append, List.length_map]
          rfl
        exact lengthEq.symm ▸ (by omega)⟩)
      (fun localIndex => ⟨sourceCall.fullContext.length + localIndex.val, by
        rw [targetEq]
        have lengthEq :
            (sourceCall.fullContext.map layout.frameWireMap ++
              (CompiledSite.endpointCall (State.ofOpen input.pattern)
                input.binderSpine.bodyContainer).localContext.map
                  layout.patternWireMap).length =
            sourceCall.fullContext.length +
              (CompiledSite.endpointCall (State.ofOpen input.pattern)
                input.binderSpine.bodyContainer).localContext.length := by
          simp only [List.length_append, List.length_map]
          rfl
        exact lengthEq.symm ▸ (by
          change _ < sourceCall.fullContext.length + patternCall.localContext.length
          omega)⟩) split

private theorem canonicalPatternMap_outer_val
    (layout : PlugLayout input) (sourceCall : CompilerCall input.frame.val)
    (targetCall : CompilerCall layout.plugRaw)
    (targetEq : targetCall.fullContext =
      sourceCall.fullContext.map layout.frameWireMap ++
        (CompiledSite.endpointCall (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).localContext.map
            layout.patternWireMap)
    (materialWireMap : Fin (CompiledSite.endpointCall
      (State.ofOpen input.pattern) input.binderSpine.bodyContainer
        ).outerContext.length → Fin sourceCall.fullContext.length)
    (outer : Fin (CompiledSite.endpointCall (State.ofOpen input.pattern)
      input.binderSpine.bodyContainer).outerContext.length) :
    (layout.canonicalPatternMap sourceCall targetCall targetEq materialWireMap
      (Fin.cast (CompilerCall.fullContext_length _).symm
        (Fin.castAdd (CompiledSite.endpointCall (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).localContext.length outer))).val =
        (materialWireMap outer).val := by
  simp [canonicalPatternMap]

private theorem canonicalPatternMap_local_val
    (layout : PlugLayout input) (sourceCall : CompilerCall input.frame.val)
    (targetCall : CompilerCall layout.plugRaw)
    (targetEq : targetCall.fullContext =
      sourceCall.fullContext.map layout.frameWireMap ++
        (CompiledSite.endpointCall (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).localContext.map
            layout.patternWireMap)
    (materialWireMap : Fin (CompiledSite.endpointCall
      (State.ofOpen input.pattern) input.binderSpine.bodyContainer
        ).outerContext.length → Fin sourceCall.fullContext.length)
    (localIndex : Fin (CompiledSite.endpointCall (State.ofOpen input.pattern)
      input.binderSpine.bodyContainer).localContext.length) :
    (layout.canonicalPatternMap sourceCall targetCall targetEq materialWireMap
      (Fin.cast (CompilerCall.fullContext_length _).symm
        (Fin.natAdd (CompiledSite.endpointCall (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).outerContext.length localIndex))).val =
        sourceCall.fullContext.length + localIndex.val := by
  simp [canonicalPatternMap]

private theorem canonicalFrameMap_get
    (layout : PlugLayout input) (sourceCall : CompilerCall input.frame.val)
    (targetCall : CompilerCall layout.plugRaw)
    (targetEq : targetCall.fullContext =
      sourceCall.fullContext.map layout.frameWireMap ++
        (CompiledSite.endpointCall (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).localContext.map
            layout.patternWireMap)
    (index : Fin sourceCall.fullContext.length) :
    targetCall.fullContext.get
        (layout.canonicalFrameMap sourceCall targetCall targetEq index) =
      layout.frameWireMap (sourceCall.fullContext.get index) := by
  rw [List.get_of_eq targetEq]
  change (sourceCall.fullContext.map layout.frameWireMap ++
      (CompiledSite.endpointCall (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).localContext.map
          layout.patternWireMap)[index.val] = _
  rw [List.getElem_append_left (by
    rw [List.length_map]
    exact index.isLt)]
  exact List.getElem_map layout.frameWireMap

private theorem canonicalPatternMap_get
    (layout : PlugLayout input) (sourceCall : CompilerCall input.frame.val)
    (targetCall : CompilerCall layout.plugRaw)
    (targetEq : targetCall.fullContext =
      sourceCall.fullContext.map layout.frameWireMap ++
        (CompiledSite.endpointCall (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).localContext.map
            layout.patternWireMap)
    (materialWireMap : Fin (CompiledSite.endpointCall
      (State.ofOpen input.pattern) input.binderSpine.bodyContainer
        ).outerContext.length → Fin sourceCall.fullContext.length)
    (materialGet : ∀ index,
      sourceCall.fullContext.get (materialWireMap index) =
        input.attachment (layout.exposedPosition
          (Fin.cast (congrArg List.length (patternTerminal_outerContext input
            terminal)) index)))
    (index : Fin (CompiledSite.endpointCall (State.ofOpen input.pattern)
      input.binderSpine.bodyContainer).fullContext.length) :
    targetCall.fullContext.get
        (layout.canonicalPatternMap sourceCall targetCall targetEq
          materialWireMap index) =
      layout.patternWireMap ((CompiledSite.endpointCall
        (State.ofOpen input.pattern) input.binderSpine.bodyContainer
          ).fullContext.get index) := by
  let patternCall := CompiledSite.endpointCall (State.ofOpen input.pattern)
    input.binderSpine.bodyContainer
  let split := Fin.cast patternCall.fullContext_length index
  refine Fin.addCases (motive := fun position =>
    targetCall.fullContext.get
        (layout.canonicalPatternMap sourceCall targetCall targetEq materialWireMap
          (Fin.cast patternCall.fullContext_length.symm position)) =
      layout.patternWireMap (patternCall.fullContext.get
        (Fin.cast patternCall.fullContext_length.symm position)))
    (fun outer => by
      have mapVal := layout.canonicalPatternMap_outer_val sourceCall targetCall
        targetEq materialWireMap outer
      let mapped := layout.canonicalPatternMap sourceCall targetCall targetEq
        materialWireMap (Fin.cast patternCall.fullContext_length.symm
          (Fin.castAdd patternCall.localContext.length outer))
      let candidate : Fin targetCall.fullContext.length :=
        ⟨(materialWireMap outer).val, by
          have := mapped.isLt
          rw [mapVal] at this
          exact this⟩
      have mapEq : mapped = candidate := Fin.ext mapVal
      change targetCall.fullContext.get mapped = _
      rw [mapEq]
      rw [List.get_of_eq targetEq]
      change (sourceCall.fullContext.map layout.frameWireMap ++
        patternCall.localContext.map layout.patternWireMap)[
          (materialWireMap outer).val] = _
      rw [List.getElem_append_left (by
        rw [List.length_map]
        exact (materialWireMap outer).isLt), List.getElem_map]
      have outerGet : patternCall.fullContext.get
          (Fin.cast patternCall.fullContext_length.symm
            (Fin.castAdd patternCall.localContext.length outer)) =
          patternCall.outerContext.get outer := by
        unfold CompilerCall.fullContext
        exact List.getElem_append_left outer.isLt
      rw [outerGet]
      have outerEq := patternTerminal_outerContext input terminal
      have wireEq : patternCall.outerContext.get outer =
          input.pattern.val.exposedWires.get
            (Fin.cast (congrArg List.length outerEq) outer) := by
        exact listGetCast outerEq outer
      rw [wireEq, layout.patternWireMap_exposed_get]
      have mappedAttachment := congrArg layout.frameWireMap (materialGet outer)
      simpa [List.get_eq_getElem, PlugLayout.frameWireMap,
        PlugLayout.exposedAttachment] using mappedAttachment)
    (fun localIndex => by
      have mapVal := layout.canonicalPatternMap_local_val sourceCall targetCall
        targetEq materialWireMap localIndex
      let mapped := layout.canonicalPatternMap sourceCall targetCall targetEq
        materialWireMap (Fin.cast patternCall.fullContext_length.symm
          (Fin.natAdd patternCall.outerContext.length localIndex))
      let candidate : Fin targetCall.fullContext.length :=
        ⟨sourceCall.fullContext.length + localIndex.val, by
          have := mapped.isLt
          rw [mapVal] at this
          exact this⟩
      have mapEq : mapped = candidate := Fin.ext mapVal
      change targetCall.fullContext.get mapped = _
      rw [mapEq]
      rw [List.get_of_eq targetEq]
      have inBounds : sourceCall.fullContext.length + localIndex.val <
          (sourceCall.fullContext.map layout.frameWireMap ++
            patternCall.localContext.map layout.patternWireMap).length := by
        rw [List.length_append, List.length_map, List.length_map]
        exact Nat.add_lt_add_left localIndex.isLt _
      change (sourceCall.fullContext.map layout.frameWireMap ++
        patternCall.localContext.map layout.patternWireMap)[
          sourceCall.fullContext.length + localIndex.val]'inBounds = _
      rw [List.getElem_append_right (by rw [List.length_map]; omega)]
      have subEq : sourceCall.fullContext.length + localIndex.val -
          (sourceCall.fullContext.map layout.frameWireMap).length =
          localIndex.val := by
        rw [List.length_map]
        omega
      simp only [subEq, List.getElem_map]
      have localGet : patternCall.fullContext.get
          (Fin.cast patternCall.fullContext_length.symm
            (Fin.natAdd patternCall.outerContext.length localIndex)) =
          patternCall.localContext.get localIndex := by
        unfold CompilerCall.fullContext
        simpa only [List.get_eq_getElem, Nat.add_sub_cancel_left] using
          (List.getElem_append_right
            (as := patternCall.outerContext) (bs := patternCall.localContext)
            (Nat.le_add_right patternCall.outerContext.length localIndex.val))
      rw [localGet]
      rfl) split

noncomputable def canonicalOuterWire
    (layout : PlugLayout input) (sourceCall : CompilerCall input.frame.val)
    (targetOuter : WireContext layout.plugRaw)
    (outerEq : targetOuter =
      sourceCall.outerContext.map layout.frameWireMap) :
    FiniteEquiv (Fin targetOuter.length)
      (Fin sourceCall.outerContext.length) :=
  FiniteEquiv.finCast ((congrArg List.length outerEq).trans
    (List.length_map layout.frameWireMap))

private noncomputable def canonicalLocalWire
    (layout : PlugLayout input) (sourceCall : CompilerCall input.frame.val)
    (targetCall : CompilerCall layout.plugRaw)
    (outerEq : targetCall.outerContext =
      sourceCall.outerContext.map layout.frameWireMap)
    (targetEq : targetCall.fullContext =
      sourceCall.fullContext.map layout.frameWireMap ++
        (CompiledSite.endpointCall (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).localContext.map
            layout.patternWireMap) :
    FiniteEquiv (Fin targetCall.localContext.length)
      (Fin (sourceCall.localContext.length +
        (CompiledSite.endpointCall (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).localContext.length)) := by
  apply FiniteEquiv.finCast
  have lengths := congrArg List.length targetEq
  have outerLength : targetCall.outerContext.length =
      sourceCall.outerContext.length :=
    (congrArg List.length outerEq).trans
      (List.length_map layout.frameWireMap)
  have sourceLength := sourceCall.fullContext_length
  have targetLength := targetCall.fullContext_length
  have mappedLength :
      (sourceCall.fullContext.map layout.frameWireMap ++
        (CompiledSite.endpointCall (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).localContext.map
            layout.patternWireMap).length =
      sourceCall.fullContext.length +
        (CompiledSite.endpointCall (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).localContext.length := by
    simp only [List.length_append, List.length_map]
    rfl
  have totalLength := lengths.trans mappedLength
  omega

private theorem canonicalExtendedWire_val
    (layout : PlugLayout input) (sourceCall : CompilerCall input.frame.val)
    (targetCall : CompilerCall layout.plugRaw)
    (outerEq : targetCall.outerContext =
      sourceCall.outerContext.map layout.frameWireMap)
    (targetEq : targetCall.fullContext =
      sourceCall.fullContext.map layout.frameWireMap ++
        (CompiledSite.endpointCall (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).localContext.map
            layout.patternWireMap)
    (index : Fin (targetCall.outerContext.length +
      targetCall.localContext.length)) :
    (extendWireEquiv (layout.canonicalOuterWire sourceCall
      targetCall.outerContext outerEq)
      (layout.canonicalLocalWire sourceCall targetCall outerEq targetEq)
      index).val = index.val := by
  refine Fin.addCases (motive := fun position =>
    (extendWireEquiv
      (layout.canonicalOuterWire sourceCall targetCall.outerContext outerEq)
      (layout.canonicalLocalWire sourceCall targetCall outerEq targetEq)
      position).val = position.val)
    (fun inherited => by
      simp [extendWireEquiv, canonicalOuterWire, FiniteEquiv.finCast])
    (fun localIndex => by
      have outerLength : sourceCall.outerContext.length =
          targetCall.outerContext.length :=
        ((congrArg List.length outerEq).trans
          (List.length_map layout.frameWireMap)).symm
      simp [extendWireEquiv, canonicalLocalWire, FiniteEquiv.finCast,
        outerLength]) index

private theorem canonicalFrameFactor
    (layout : PlugLayout input) (sourceCall : CompilerCall input.frame.val)
    (targetCall : CompilerCall layout.plugRaw)
    (outerEq : targetCall.outerContext =
      sourceCall.outerContext.map layout.frameWireMap)
    (targetEq : targetCall.fullContext =
      sourceCall.fullContext.map layout.frameWireMap ++
        (CompiledSite.endpointCall (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).localContext.map
            layout.patternWireMap)
    (index : Fin sourceCall.fullContext.length) :
    extendWireEquiv (layout.canonicalOuterWire sourceCall
        targetCall.outerContext outerEq)
        (layout.canonicalLocalWire sourceCall targetCall outerEq targetEq)
        (Fin.cast targetCall.fullContext_length
          (layout.canonicalFrameMap sourceCall targetCall targetEq index)) =
      Region.adjoinHostWire sourceCall.outerContext.length
        sourceCall.localContext.length
        (CompiledSite.endpointCall (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).localContext.length
        (Fin.cast sourceCall.fullContext_length index) := by
  apply Fin.ext
  rw [layout.canonicalExtendedWire_val sourceCall targetCall outerEq targetEq]
  rfl

private theorem canonicalPatternFactor
    (layout : PlugLayout input) (sourceCall : CompilerCall input.frame.val)
    (targetCall : CompilerCall layout.plugRaw)
    (outerEq : targetCall.outerContext =
      sourceCall.outerContext.map layout.frameWireMap)
    (targetEq : targetCall.fullContext =
      sourceCall.fullContext.map layout.frameWireMap ++
        (CompiledSite.endpointCall (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).localContext.map
            layout.patternWireMap)
    (materialWireMap : Fin (CompiledSite.endpointCall
      (State.ofOpen input.pattern) input.binderSpine.bodyContainer
        ).outerContext.length → Fin sourceCall.fullContext.length)
    (index : Fin (CompiledSite.endpointCall (State.ofOpen input.pattern)
      input.binderSpine.bodyContainer).fullContext.length) :
    extendWireEquiv (layout.canonicalOuterWire sourceCall
        targetCall.outerContext outerEq)
        (layout.canonicalLocalWire sourceCall targetCall outerEq targetEq)
        (Fin.cast targetCall.fullContext_length
          (layout.canonicalPatternMap sourceCall targetCall targetEq
            materialWireMap index)) =
      Region.adjoinMaterialWire sourceCall.outerContext.length
        sourceCall.localContext.length
        (CompiledSite.endpointCall (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).localContext.length
        (extendWireRenaming
          (fun wire => Fin.cast sourceCall.fullContext_length
            (materialWireMap wire))
          (CompiledSite.endpointCall (State.ofOpen input.pattern)
            input.binderSpine.bodyContainer).localContext.length
          (Fin.cast (CompilerCall.fullContext_length
            (CompiledSite.endpointCall (State.ofOpen input.pattern)
              input.binderSpine.bodyContainer)) index)) := by
  let patternCall := CompiledSite.endpointCall (State.ofOpen input.pattern)
    input.binderSpine.bodyContainer
  let split := Fin.cast patternCall.fullContext_length index
  apply Fin.ext
  rw [layout.canonicalExtendedWire_val sourceCall targetCall outerEq targetEq]
  refine Fin.addCases (motive := fun position =>
    (layout.canonicalPatternMap sourceCall targetCall targetEq materialWireMap
      (Fin.cast patternCall.fullContext_length.symm position)).val =
      (Region.adjoinMaterialWire sourceCall.outerContext.length
        sourceCall.localContext.length patternCall.localContext.length
        (extendWireRenaming
          (fun wire => Fin.cast sourceCall.fullContext_length
            (materialWireMap wire)) patternCall.localContext.length
          position)).val)
    (fun outer => by
      have mapVal := layout.canonicalPatternMap_outer_val sourceCall targetCall
        targetEq materialWireMap outer
      simpa [Region.adjoinMaterialWire, extendWireRenaming] using mapVal)
    (fun localIndex => by
      have mapVal := layout.canonicalPatternMap_local_val sourceCall targetCall
        targetEq materialWireMap localIndex
      dsimp only [patternCall] at mapVal ⊢
      simpa [Region.adjoinMaterialWire, extendWireRenaming,
        sourceCall.fullContext_length] using mapVal) split

noncomputable def frameTargetCall
    (layout : PlugLayout input) :
    (sourceCall : CompilerCall input.frame.val) →
    (targetOuter targetLocal : WireContext layout.plugRaw) →
    BinderContext layout.plugRaw sourceCall.rels →
    CompilerCall layout.plugRaw
  | .root _ _, targetOuter, targetLocal, _ =>
      .root targetOuter targetLocal
  | .nested origin _ rels _, targetOuter, _, targetBinders =>
      .nested (layout.frameRegion origin) targetOuter rels targetBinders

/-- Package the exact item result for the matching root or nested frame call. -/
noncomputable def frameTargetBody
    (layout : PlugLayout input) (sourceCall : CompilerCall input.frame.val)
    (targetOuter targetLocal : WireContext layout.plugRaw)
    (targetBinders : BinderContext layout.plugRaw sourceCall.rels)
    (targetLocalCall : (layout.frameTargetCall sourceCall targetOuter
      targetLocal targetBinders).localContext = targetLocal)
    (targetItems : CompiledItems layout.plugRaw (targetOuter ++ targetLocal)
      sourceCall.rels targetBinders) :
    CompiledRegion layout.plugRaw
      (layout.frameTargetCall sourceCall targetOuter targetLocal
        targetBinders) := by
  cases sourceCall with
  | root =>
      have targetBindersEq : targetBinders = BinderContext.empty := by
        funext binder
        cases lookup : targetBinders binder with
        | none => rfl
        | some value =>
            obtain ⟨arity, relation⟩ := value
            exact Fin.elim0 relation.index
      subst targetBinders
      exact .mk targetItems
  | nested =>
      change exactScopeWires layout.plugRaw _ = targetLocal at targetLocalCall
      subst targetLocal
      exact .mk targetItems

/-- Expose the erasure of a frame target at the source call's outer and
relation indices. This is elimination of the root/nested call constructor;
the compiled target remains the only represented value. -/
noncomputable def frameTargetErase
    (layout : PlugLayout input) (sourceCall : CompilerCall input.frame.val)
    (targetOuter targetLocal : WireContext layout.plugRaw)
    (targetBinders : BinderContext layout.plugRaw sourceCall.rels)
    (targetBody : CompiledRegion layout.plugRaw
      (layout.frameTargetCall sourceCall targetOuter targetLocal
        targetBinders)) :
    Region targetOuter.length sourceCall.rels := by
  cases sourceCall <;> exact targetBody.erase

@[simp] theorem frameTargetErase_frameTargetBody
    (layout : PlugLayout input) (sourceCall : CompilerCall input.frame.val)
    (targetOuter targetLocal : WireContext layout.plugRaw)
    (targetBinders : BinderContext layout.plugRaw sourceCall.rels)
    (targetLocalCall : (layout.frameTargetCall sourceCall targetOuter
      targetLocal targetBinders).localContext = targetLocal)
    (targetItems : CompiledItems layout.plugRaw (targetOuter ++ targetLocal)
      sourceCall.rels targetBinders) :
    layout.frameTargetErase sourceCall targetOuter targetLocal targetBinders
        (layout.frameTargetBody sourceCall targetOuter targetLocal targetBinders
          targetLocalCall targetItems) =
      Region.mk targetLocal.length
        (targetItems.erase.castWiresEq (by exact List.length_append)) := by
  cases sourceCall with
  | root =>
      have targetBindersEq : targetBinders = BinderContext.empty := by
        funext binder
        cases lookup : targetBinders binder with
        | none => rfl
        | some value =>
            obtain ⟨arity, relation⟩ := value
            exact Fin.elim0 relation.index
      subst targetBinders
      rfl
  | nested =>
      change exactScopeWires layout.plugRaw _ = targetLocal at targetLocalCall
      subst targetLocal
      rfl

theorem frameTargetCall_compile_of_items
    (layout : PlugLayout input) (targetWf : layout.plugRaw.WellFormed)
    (sourceCall : CompilerCall input.frame.val)
    (targetOuter targetLocal : WireContext layout.plugRaw)
    (targetBinders : BinderContext layout.plugRaw sourceCall.rels)
    (targetLocalCall : (layout.frameTargetCall sourceCall targetOuter
      targetLocal targetBinders).localContext = targetLocal)
    (targetItems : CompiledItems layout.plugRaw (targetOuter ++ targetLocal)
      sourceCall.rels targetBinders)
    (itemsCompiled : compileItems? layout.plugRaw targetWf
      (layout.frameRegion sourceCall.origin) (targetOuter ++ targetLocal)
      targetBinders (localOccurrences layout.plugRaw
        (layout.frameRegion sourceCall.origin)) (fun _ member => member) =
        some targetItems) :
    (layout.frameTargetCall sourceCall targetOuter targetLocal
      targetBinders).compile? layout.plugRaw targetWf =
      some (layout.frameTargetBody sourceCall targetOuter targetLocal
        targetBinders targetLocalCall targetItems) := by
  cases sourceCall with
  | root ambient locals =>
      have targetBindersEq : targetBinders = BinderContext.empty := by
        funext binder
        cases lookup : targetBinders binder with
        | none => rfl
        | some value =>
            obtain ⟨arity, relation⟩ := value
            exact Fin.elim0 relation.index
      subst targetBinders
      change (CompilerCall.root targetOuter targetLocal).compile?
          layout.plugRaw targetWf = some (.mk targetItems)
      rw [CompilerCall.compile?_eq_compileItems?]
      change (do
        let items ← compileItems? layout.plugRaw targetWf layout.plugRaw.root
          (targetOuter ++ targetLocal) BinderContext.empty
          (localOccurrences layout.plugRaw layout.plugRaw.root)
          (fun _ member => member)
        pure (CompiledRegion.mk items : CompiledRegion layout.plugRaw
          (.root targetOuter targetLocal))) =
          some (CompiledRegion.mk targetItems : CompiledRegion layout.plugRaw
            (.root targetOuter targetLocal))
      have rootEq : layout.frameRegion input.frame.val.root =
          layout.plugRaw.root := rfl
      have normalized : compileItems? layout.plugRaw targetWf
          (layout.frameRegion input.frame.val.root)
          (targetOuter ++ targetLocal) BinderContext.empty
          (localOccurrences layout.plugRaw
            (layout.frameRegion input.frame.val.root))
          (fun _ member => member) = some targetItems := by
        simpa using itemsCompiled
      rw [← rootEq, normalized]
      rfl
  | nested origin context rels binders =>
      change exactScopeWires layout.plugRaw (layout.frameRegion origin) =
        targetLocal at targetLocalCall
      subst targetLocal
      change (CompilerCall.nested (layout.frameRegion origin) targetOuter rels
          targetBinders).compile? layout.plugRaw targetWf =
        some (.mk targetItems)
      rw [CompilerCall.compile?_eq_compileItems?]
      change (do
        let items ← compileItems? layout.plugRaw targetWf
          (layout.frameRegion origin)
          (targetOuter ++ exactScopeWires layout.plugRaw
            (layout.frameRegion origin)) targetBinders
          (localOccurrences layout.plugRaw (layout.frameRegion origin))
          (fun _ member => member)
        pure (CompiledRegion.mk items : CompiledRegion layout.plugRaw
          (.nested (layout.frameRegion origin) targetOuter rels
            targetBinders))) = some (.mk targetItems)
      have normalized : compileItems? layout.plugRaw targetWf
          (layout.frameRegion origin)
          (targetOuter ++ exactScopeWires layout.plugRaw
            (layout.frameRegion origin)) targetBinders
          (localOccurrences layout.plugRaw (layout.frameRegion origin))
          (fun _ member => member) = some targetItems := by
        simpa using itemsCompiled
      rw [normalized]
      rfl

def SpliceSiteSemantic
    (layout : PlugLayout input) (targetWf : layout.plugRaw.WellFormed)
    (sourceCall : CompilerCall input.frame.val)
    (targetOuter targetLocal : WireContext layout.plugRaw)
    (targetBinders : BinderContext layout.plugRaw sourceCall.rels)
    (outerWire : FiniteEquiv (Fin targetOuter.length)
      (Fin sourceCall.outerContext.length))
    (materialWireMap : Fin (CompiledSite.endpointCall
      (State.ofOpen input.pattern) input.binderSpine.bodyContainer
        ).outerContext.length →
      Fin (sourceCall.outerContext.length + sourceCall.localContext.length))
    (relationMap : RelationRenaming
      (CompiledSite.endpointCall (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).rels sourceCall.rels)
    (sourceBody : CompiledRegion input.frame.val sourceCall) : Prop :=
  match sourceCall, sourceBody with
  | .root ambient locals, .mk sourceItems =>
      Nonempty (Σ targetBody : CompiledRegion layout.plugRaw
          (layout.frameTargetCall (.root ambient locals) targetOuter
            targetLocal targetBinders),
        PSigma (fun _ : (layout.frameTargetCall
            (.root ambient locals) targetOuter targetLocal
              targetBinders).compile? layout.plugRaw targetWf =
              some targetBody =>
          RegionIso outerWire [] targetBody.erase
            (Region.spliceAt locals.length
              (sourceItems.erase.castWiresEq (by exact List.length_append))
              (CompiledSite.body (State.ofOpen input.pattern)
                input.binderSpine.bodyContainer)
              materialWireMap relationMap)))
  | .nested origin sourceOuter sourceRels sourceBinders, .mk sourceItems =>
      Nonempty (Σ targetBody : CompiledRegion layout.plugRaw
          (layout.frameTargetCall
            (.nested origin sourceOuter sourceRels sourceBinders)
              targetOuter targetLocal targetBinders),
        PSigma (fun _ : (layout.frameTargetCall
            (.nested origin sourceOuter sourceRels sourceBinders)
              targetOuter targetLocal targetBinders).compile?
                layout.plugRaw targetWf = some targetBody =>
          RegionIso outerWire sourceRels targetBody.erase
            (Region.spliceAt (exactScopeWires input.frame.val origin).length
              (sourceItems.erase.castWiresEq (by exact List.length_append))
              (CompiledSite.body (State.ofOpen input.pattern)
                input.binderSpine.bodyContainer)
              materialWireMap relationMap)))
/-- Compile and identify the actual splice endpoint for any compiler call.
Root and nested calls share this one contract; their concrete outer and local
wire presentations are supplied only as endpoint factor laws. -/
theorem compileSpliceSite
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (admissible : input.Admissible)
    (targetWf : layout.plugRaw.WellFormed)
    (sourceCall : CompilerCall input.frame.val)
    (targetOuter targetLocal : WireContext layout.plugRaw)
    (targetBinders : BinderContext layout.plugRaw sourceCall.rels)
    (atSite : sourceCall.origin = input.site)
    (outerEq : targetOuter =
      sourceCall.outerContext.map layout.frameWireMap)
    (targetEq : (layout.frameTargetCall sourceCall targetOuter targetLocal
        targetBinders).fullContext =
      sourceCall.fullContext.map layout.frameWireMap ++
        (CompiledSite.endpointCall (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).localContext.map
            layout.patternWireMap)
    (sourceExact : sourceCall.fullContext.Exact input.site)
    (frameBindersMapped : ∀ binder,
      targetBinders (layout.frameRegion binder) = sourceCall.binders binder)
    (relationMap : RelationRenaming
      (CompiledSite.endpointCall (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).rels sourceCall.rels)
    (hostLookup : ∀ {arity} (relation : RelVar
      (CompiledSite.endpointCall (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).rels arity),
      sourceCall.binders (input.binderTarget
        (terminalRelationProxyEquiv input relation.index)) =
          some ⟨arity, relationMap relation⟩)
    (materialWireMap : Fin (CompiledSite.endpointCall
      (State.ofOpen input.pattern) input.binderSpine.bodyContainer
        ).outerContext.length →
      Fin sourceCall.fullContext.length)
    (materialGet : ∀ index,
      sourceCall.fullContext.get (materialWireMap index) =
        input.attachment (layout.exposedPosition
          (Fin.cast (congrArg List.length (patternTerminal_outerContext input
            terminal)) index)))
    {sourceBody : CompiledRegion input.frame.val sourceCall}
    (sourceCompiled : sourceCall.compile? input.frame.val
      input.frame.property = some sourceBody) :
    layout.SpliceSiteSemantic targetWf sourceCall targetOuter targetLocal
      targetBinders
      (layout.canonicalOuterWire sourceCall targetOuter outerEq)
      (fun wire => Fin.cast sourceCall.fullContext_length
        (materialWireMap wire)) relationMap sourceBody := by
  let targetCall := layout.frameTargetCall sourceCall targetOuter targetLocal
    targetBinders
  have targetExact : targetCall.fullContext.Exact
      (layout.frameRegion input.site) := by
    rw [targetEq]
    rw [← layout.bodyLocalWires_eq_endpointLocalMap]
    exact layout.siteMappedFull_exact consistent terminal _ sourceExact
  cases sourceCall with
  | root ambient locals =>
      cases sourceBody with
      | mk sourceItems =>
          dsimp only [SpliceSiteSemantic]
          let sourceCall : CompilerCall input.frame.val := .root ambient locals
          let targetCall : CompilerCall layout.plugRaw :=
            layout.frameTargetCall sourceCall targetOuter targetLocal
              targetBinders
          let outerWire := layout.canonicalOuterWire sourceCall targetOuter
            outerEq
          let localWire := layout.canonicalLocalWire sourceCall targetCall
            outerEq targetEq
          have targetOrigin : targetCall.origin =
              layout.frameRegion input.site := by
            change input.frame.val.root = input.site at atSite
            change layout.frameRegion input.frame.val.root =
              layout.frameRegion input.site
            exact congrArg (fun region => layout.frameRegion region) atSite
          let frameMap := layout.canonicalFrameMap sourceCall targetCall targetEq
          let patternMap := layout.canonicalPatternMap sourceCall targetCall
            targetEq materialWireMap
          have patternBindersMapped : ∀ binder {arity relation},
              (CompiledSite.endpointCall (State.ofOpen input.pattern)
                  input.binderSpine.bodyContainer).binders binder =
                some ⟨arity, relation⟩ →
              targetCall.binders (layout.binderRegion binder) =
                some ⟨arity, relationMap relation⟩ := by
            intro binder arity relation sourceLookup
            have impossible := hostLookup relation
            simp [CompilerCall.binders, BinderContext.empty] at impossible
          have sourceItemsCompiled :=
            CompilerCall.compile?_items_of_success input.frame.property
              sourceCall sourceCompiled
          have sourceItemsAtSite : compileItems? input.frame.val
              input.frame.property input.site sourceCall.fullContext
              sourceCall.binders (localOccurrences input.frame.val input.site)
              (fun _ member => member) = some sourceItems := by
            rw [atSite] at sourceItemsCompiled
            exact sourceItemsCompiled
          obtain ⟨targetItems, targetItemsCompiled, endpointIso⟩ :=
            layout.compileSpliceSiteItems_semantic consistent admissible
              targetWf sourceCall.outerContext
              sourceCall.localContext sourceCall.binders targetCall.outerContext
              targetCall.localContext targetCall.binders frameMap patternMap
              relationMap patternBindersMapped (fun _ => rfl) sourceExact
              targetExact
              (layout.canonicalFrameMap_get sourceCall targetCall targetEq)
              (layout.canonicalPatternMap_get (terminal := terminal)
                sourceCall targetCall targetEq
                materialWireMap materialGet) outerWire localWire
              (fun wire => Fin.cast sourceCall.fullContext_length
                (materialWireMap wire))
              (layout.canonicalFrameFactor sourceCall targetCall outerEq
                targetEq)
              (layout.canonicalPatternFactor sourceCall targetCall outerEq
                targetEq materialWireMap) sourceItemsAtSite
          let targetBody : CompiledRegion layout.plugRaw targetCall :=
            .mk targetItems
          refine ⟨⟨targetBody, ⟨?_, ?_⟩⟩⟩
          · rw [CompilerCall.compile?_eq_compileItems?]
            have canonical : compileItems? layout.plugRaw
                targetWf targetCall.origin
                targetCall.fullContext targetCall.binders
                (localOccurrences layout.plugRaw targetCall.origin)
                (fun _ member => member) = some targetItems := by
              simpa only [targetOrigin] using targetItemsCompiled
            change (do
              let items ← compileItems? layout.plugRaw
                targetWf targetCall.origin targetCall.fullContext
                targetCall.binders
                (localOccurrences layout.plugRaw targetCall.origin)
                (fun _ member => member)
              pure (CompiledRegion.mk items)) =
                some (CompiledRegion.mk targetItems)
            rw [canonical]
            rfl
          · exact endpointIso
  | nested origin sourceOuter sourceRels sourceBinders =>
      cases sourceBody with
      | mk sourceItems =>
          dsimp only [SpliceSiteSemantic]
          let sourceCall : CompilerCall input.frame.val :=
            .nested origin sourceOuter sourceRels sourceBinders
          let targetCall : CompilerCall layout.plugRaw :=
            layout.frameTargetCall sourceCall targetOuter targetLocal
              targetBinders
          let outerWire := layout.canonicalOuterWire sourceCall targetOuter
            outerEq
          let localWire := layout.canonicalLocalWire sourceCall targetCall
            outerEq targetEq
          have targetOrigin : targetCall.origin =
              layout.frameRegion input.site := by
            change origin = input.site at atSite
            change layout.frameRegion origin = layout.frameRegion input.site
            exact congrArg (fun region => layout.frameRegion region) atSite
          let frameMap := layout.canonicalFrameMap sourceCall targetCall targetEq
          let patternMap := layout.canonicalPatternMap sourceCall targetCall
            targetEq materialWireMap
          have patternBindersMapped : ∀ binder {arity relation},
              (CompiledSite.endpointCall (State.ofOpen input.pattern)
                  input.binderSpine.bodyContainer).binders binder =
                some ⟨arity, relation⟩ →
              targetCall.binders (layout.binderRegion binder) =
                some ⟨arity, relationMap relation⟩ := by
            exact layout.terminalBinderMapped sourceBinders targetCall.binders
              frameBindersMapped relationMap hostLookup
          have frameBindersMapped' : ∀ binder,
              targetCall.binders (layout.frameRegion binder) =
                (sourceBinders binder).map fun relation =>
                  ⟨relation.1, relation.2⟩ := by
            intro binder
            have mapped := frameBindersMapped binder
            change targetBinders (layout.frameRegion binder) =
              sourceBinders binder at mapped
            change targetBinders (layout.frameRegion binder) =
              (sourceBinders binder).map fun relation =>
                ⟨relation.1, relation.2⟩
            rw [mapped]
            cases sourceBinders binder <;> rfl
          have sourceItemsCompiled :=
            CompilerCall.compile?_items_of_success input.frame.property
              sourceCall sourceCompiled
          have sourceItemsAtSite : compileItems? input.frame.val
              input.frame.property input.site sourceCall.fullContext
              sourceCall.binders (localOccurrences input.frame.val input.site)
              (fun _ member => member) = some sourceItems := by
            rw [atSite] at sourceItemsCompiled
            exact sourceItemsCompiled
          obtain ⟨targetItems, targetItemsCompiled, endpointIso⟩ :=
            layout.compileSpliceSiteItems_semantic consistent admissible
              targetWf sourceCall.outerContext
              sourceCall.localContext sourceCall.binders targetCall.outerContext
              targetCall.localContext targetCall.binders frameMap patternMap
              relationMap patternBindersMapped frameBindersMapped' sourceExact
              targetExact
              (layout.canonicalFrameMap_get sourceCall targetCall targetEq)
              (layout.canonicalPatternMap_get (terminal := terminal)
                sourceCall targetCall targetEq
                materialWireMap materialGet) outerWire localWire
              (fun wire => Fin.cast sourceCall.fullContext_length
                (materialWireMap wire))
              (layout.canonicalFrameFactor sourceCall targetCall outerEq
                targetEq)
              (layout.canonicalPatternFactor sourceCall targetCall outerEq
                targetEq materialWireMap) sourceItemsAtSite
          let targetBody : CompiledRegion layout.plugRaw targetCall :=
            .mk targetItems
          refine ⟨⟨targetBody, ⟨?_, ?_⟩⟩⟩
          · rw [CompilerCall.compile?_eq_compileItems?]
            have canonical : compileItems? layout.plugRaw
                targetWf targetCall.origin
                targetCall.fullContext targetCall.binders
                (localOccurrences layout.plugRaw targetCall.origin)
                (fun _ member => member) = some targetItems := by
              simpa only [targetOrigin] using targetItemsCompiled
            dsimp only [targetBody]
            change (do
              let items ← compileItems? layout.plugRaw targetWf
                targetCall.origin targetCall.fullContext targetCall.binders
                (localOccurrences layout.plugRaw targetCall.origin)
                (fun _ member => member)
              pure (CompiledRegion.mk items)) =
                some (CompiledRegion.mk targetItems)
            rw [canonical]
            rfl
          · exact endpointIso

end Splice.Input.PlugLayout

end VisualProof.Concrete
