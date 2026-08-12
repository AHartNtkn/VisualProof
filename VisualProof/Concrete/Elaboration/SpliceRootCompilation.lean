import VisualProof.Concrete.Elaboration.SpliceSiteCompilation

/-! Construct the target root by following the canonical source host zipper. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Diagram
open Theory
open Elaboration

namespace Splice.Input.PlugLayout

private theorem sibling_not_encloses
    {d : Diagram} (hwf : d.WellFormed)
    {parent selected sibling site : Fin d.regionCount}
    (selectedParent : (d.regions selected).parent? = some parent)
    (siblingParent : (d.regions sibling).parent? = some parent)
    (different : sibling ≠ selected)
    (selectedEncloses : d.Encloses selected site) :
    ¬ d.Encloses sibling site := by
  intro siblingEncloses
  rcases d.enclosingRegions_comparable selectedEncloses siblingEncloses with
    selectedSibling | siblingSelected
  · rcases Elaboration.encloses_direct_child siblingParent selectedSibling with
      same | selectedParentEncloses
    · exact different same.symm
    · exact Elaboration.checked_direct_child_not_encloses_parent hwf
        selectedParent selectedParentEncloses
  · rcases Elaboration.encloses_direct_child selectedParent siblingSelected with
      same | siblingParentEncloses
    · exact different same
    · exact Elaboration.checked_direct_child_not_encloses_parent hwf
        siblingParent siblingParentEncloses

mutual
  private theorem compileNestedAlongZipper
      (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
      (admissible : input.Admissible) (targetWf : layout.plugRaw.WellFormed)
      {endpointCall : CompilerCall input.frame.val}
      {endpoint : CompiledRegion input.frame.val endpointCall}
      (relationMap : RelationRenaming
        (CompiledSite.endpointCall (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).rels endpointCall.rels)
      (hostLookup : ∀ {arity} (relation : RelVar
          (CompiledSite.endpointCall (State.ofOpen input.pattern)
            input.binderSpine.bodyContainer).rels arity),
        endpointCall.binders (input.binderTarget
            (terminalRelationProxyEquiv input relation.index)) =
          some ⟨arity, relationMap relation⟩)
      {parent : Fin input.frame.val.regionCount}
      {sourceOuter : WireContext input.frame.val}
      {sourceBinders : BinderContext input.frame.val sourceRels}
      {sourceBody : CompiledRegion input.frame.val
        (.nested parent sourceOuter sourceRels sourceBinders)}
      {targetOuter : WireContext layout.plugRaw}
      {targetBinders : BinderContext layout.plugRaw sourceRels}
      (focus : CompiledZipper input.frame.val sourceBody input.site
        endpointCall endpoint)
      (compiled : compileRegion? input.frame.val input.frame.property parent
        sourceOuter sourceBinders = some sourceBody)
      (sourceExact : (sourceOuter.extend parent).Exact parent)
      (targetExact : (targetOuter.extend (layout.frameRegion parent)).Exact
        (layout.frameRegion parent))
      (outerMap : Fin sourceOuter.length → Fin targetOuter.length)
      (outerGet : ∀ index, targetOuter.get (outerMap index) =
        layout.frameWireMap (sourceOuter.get index))
      (bindersMapped : ∀ binder,
        targetBinders (layout.frameRegion binder) = sourceBinders binder)
      (sourceCovers : sourceBinders.Covers parent)
      (sourceEnumeration : BinderContext.Enumeration input.frame.val
        sourceBinders parent) :
      ∃ targetBody : CompiledRegion layout.plugRaw
          (.nested (layout.frameRegion parent) targetOuter sourceRels
            targetBinders),
        compileRegion? layout.plugRaw targetWf (layout.frameRegion parent)
          targetOuter targetBinders = some targetBody := by
    cases focus
    case here =>
      exact layout.compileNestedSpliceSite consistent admissible targetWf
        input.site sourceOuter sourceBinders targetOuter targetBinders rfl
        sourceExact targetExact bindersMapped relationMap hostLookup compiled
    case child items nested =>
      have sourceItemsCompiled := compileRegion?_items_of_success
        input.frame.property parent sourceOuter sourceBinders compiled
      have sourceOrigins := compileItems?_origins input.frame.property parent
        _ _ sourceItemsCompiled
      have itemsDirect : ∀ occurrence, occurrence ∈ items.origins →
          occurrence ∈ localOccurrences input.frame.val parent := by
        intro occurrence member
        rw [← sourceOrigins]
        exact member
      have itemsCompiled : compileItems? input.frame.val input.frame.property
          parent (sourceOuter.extend parent) sourceBinders items.origins
          itemsDirect = some items := by
        exact (compileItems?_congr_occurrences input.frame.property parent
          (context := sourceOuter.extend parent) (binders := sourceBinders)
          (equal := sourceOrigins) itemsDirect (fun _ member => member)).trans
            sourceItemsCompiled
      obtain ⟨selected, selectedMember, selectedParent, selectedEncloses⟩ :=
        nested.selected_child input.frame.property parent sourceExact
          sourceCovers sourceEnumeration itemsDirect itemsCompiled
      have parentAway : parent ≠ input.site := by
        intro same
        subst parent
        exact Elaboration.checked_direct_child_not_encloses_parent
          input.frame.property selectedParent selectedEncloses
      let fullMap := layout.extendFrameContextMap consistent
        admissible.terminal_body parent parentAway sourceOuter targetOuter
          outerMap
      have fullGet : ∀ index,
          (targetOuter.extend (layout.frameRegion parent)).get
              (fullMap index) =
            layout.frameWireMap ((sourceOuter.extend parent).get index) :=
        layout.extendFrameContextMap_get consistent admissible.terminal_body
          parent parentAway sourceOuter targetOuter outerMap outerGet
      have sourceNodup : items.origins.Nodup := by
        exact sourceOrigins.symm ▸ localOccurrences_nodup input.frame.val parent
      obtain ⟨targetItems, targetItemsCompiled⟩ :=
        compileItemsAlongZipper layout consistent admissible targetWf
          relationMap hostLookup nested itemsDirect itemsCompiled
          sourceNodup parentAway sourceExact targetExact fullMap fullGet
          bindersMapped sourceCovers sourceEnumeration
      refine ⟨.mk targetItems, ?_⟩
      have occurrenceEq : localOccurrences layout.plugRaw
          (layout.frameRegion parent) =
            items.origins.map layout.mapFrameOccurrence := by
        rw [layout.localOccurrences_frameRegion_of_ne_site parent parentAway]
        simpa only [CompiledRegion.items] using
          congrArg (List.map layout.mapFrameOccurrence) sourceOrigins.symm
      have targetCanonical : compileItems? layout.plugRaw targetWf
          (layout.frameRegion parent)
          (targetOuter.extend (layout.frameRegion parent)) targetBinders
          (localOccurrences layout.plugRaw (layout.frameRegion parent))
          (fun _ member => member) = some targetItems :=
        (compileItems?_congr_occurrences targetWf
          (layout.frameRegion parent) _ _ occurrenceEq
          (fun _ member => member) _).trans targetItemsCompiled
      rw [compileRegion?_eq_compileItems?, targetCanonical]
      rfl

  private theorem compileItemsAlongZipper
      (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
      (admissible : input.Admissible) (targetWf : layout.plugRaw.WellFormed)
      {endpointCall : CompilerCall input.frame.val}
      {endpoint : CompiledRegion input.frame.val endpointCall}
      (relationMap : RelationRenaming
        (CompiledSite.endpointCall (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).rels endpointCall.rels)
      (hostLookup : ∀ {arity} (relation : RelVar
          (CompiledSite.endpointCall (State.ofOpen input.pattern)
            input.binderSpine.bodyContainer).rels arity),
        endpointCall.binders (input.binderTarget
            (terminalRelationProxyEquiv input relation.index)) =
          some ⟨arity, relationMap relation⟩)
      {parent : Fin input.frame.val.regionCount}
      {sourceContext : WireContext input.frame.val}
      {sourceBinders : BinderContext input.frame.val sourceRels}
      {sourceItems : CompiledItems input.frame.val sourceContext sourceRels
        sourceBinders}
      {targetContext : WireContext layout.plugRaw}
      {targetBinders : BinderContext layout.plugRaw sourceRels}
      (focus : CompiledItemsZipper input.frame.val sourceItems input.site
        endpointCall endpoint)
      (sourceDirect : ∀ occurrence, occurrence ∈ sourceItems.origins →
        occurrence ∈ localOccurrences input.frame.val parent)
      (compiled : compileItems? input.frame.val input.frame.property parent
        sourceContext sourceBinders sourceItems.origins sourceDirect =
          some sourceItems)
      (sourceNodup : sourceItems.origins.Nodup)
      (parentAway : parent ≠ input.site)
      (sourceExact : sourceContext.Exact parent)
      (targetExact : targetContext.Exact (layout.frameRegion parent))
      (wireMap : Fin sourceContext.length → Fin targetContext.length)
      (wireGet : ∀ index, targetContext.get (wireMap index) =
        layout.frameWireMap (sourceContext.get index))
      (bindersMapped : ∀ binder,
        targetBinders (layout.frameRegion binder) = sourceBinders binder)
      (sourceCovers : sourceBinders.Covers parent)
      (sourceEnumeration : BinderContext.Enumeration input.frame.val
        sourceBinders parent) :
      ∃ targetItems : CompiledItems layout.plugRaw targetContext sourceRels
          targetBinders,
        compileItems? layout.plugRaw targetWf (layout.frameRegion parent)
          targetContext targetBinders
          (sourceItems.origins.map layout.mapFrameOccurrence)
          (fun occurrence member => by
            rw [layout.localOccurrences_frameRegion_of_ne_site parent
              parentAway]
            obtain ⟨sourceOccurrence, sourceMember, rfl⟩ :=
              List.mem_map.mp member
            exact List.mem_map.mpr
              ⟨sourceOccurrence, sourceDirect _ sourceMember, rfl⟩) =
            some targetItems := by
    cases focus
    case cut origin body suffix nested =>
      obtain ⟨headCompiled, suffixCompiled⟩ :=
        compileItems?_cons_inv input.frame.property parent sourceContext
          sourceBinders (.cut body) suffix sourceDirect compiled
      let headDirect : LocalOccurrence.child origin ∈
          localOccurrences input.frame.val parent :=
        sourceDirect (.child origin)
          (by simp [CompiledItems.origins, CompiledItem.origin])
      let suffixDirect : ∀ occurrence, occurrence ∈ suffix.origins →
          occurrence ∈ localOccurrences input.frame.val parent := by
        intro occurrence member
        apply sourceDirect occurrence
        simp only [CompiledItems.origins, CompiledItem.origin, List.mem_cons]
        exact Or.inr member
      have sourceParent : (input.frame.val.regions origin).parent? =
          some parent :=
        (mem_localOccurrences_child input.frame.val parent origin).mp headDirect
      have headCompiled' : compileOccurrence? input.frame.val
          input.frame.property parent sourceContext sourceBinders
          (.child origin) headDirect = some (.cut body) := by
        simpa only [CompiledItem.origin] using headCompiled
      have sourceRegion : input.frame.val.regions origin = .cut parent := by
        cases regionEq : input.frame.val.regions origin with
        | sheet =>
            rw [compileOccurrence?_child_sheet input.frame.property parent
              origin sourceContext sourceBinders headDirect regionEq] at headCompiled'
            contradiction
        | cut actualParent =>
            have parentEq : actualParent = parent := by
              simpa [regionEq, CRegion.parent?] using sourceParent
            subst actualParent
            rfl
        | bubble actualParent arity =>
            have parentEq : actualParent = parent := by
              simpa [regionEq, CRegion.parent?] using sourceParent
            subst actualParent
            rw [compileOccurrence?_child_bubble input.frame.property parent
              origin sourceContext sourceBinders arity headDirect regionEq] at headCompiled'
            cases childCompiled : compileRegion? input.frame.val
                input.frame.property origin sourceContext
                (sourceBinders.push origin arity) <;>
              simp [childCompiled] at headCompiled'
      have bodyCompiled := compileOccurrence?_child_cut_body
        input.frame.property parent origin sourceContext sourceBinders
          headDirect sourceRegion headCompiled'
      have sourceChildExact := sourceExact.extend_child input.frame.property
        sourceParent
      have targetParent : (layout.plugRaw.regions
          (layout.frameRegion origin)).parent? =
            some (layout.frameRegion parent) := by
        rw [layout.plugRaw_regions_frame]
        exact (layout.mapFrameRegion_parent_eq_some_iff origin parent).2
          sourceParent
      have targetChildExact := targetExact.extend_child targetWf targetParent
      obtain ⟨targetChild, targetChildCompiled⟩ :=
        compileNestedAlongZipper layout consistent admissible targetWf
          relationMap hostLookup nested bodyCompiled sourceChildExact
          targetChildExact wireMap wireGet bindersMapped
          (BinderContext.covers_cut_child sourceCovers sourceRegion)
          (sourceEnumeration.cutChild input.frame.property sourceRegion)
      have selectedEncloses := nested.endpoint_encloses
        input.frame.property bodyCompiled sourceChildExact
          (BinderContext.covers_cut_child sourceCovers sourceRegion)
          (sourceEnumeration.cutChild input.frame.property sourceRegion)
      have originNotSuffix : LocalOccurrence.child origin ∉ suffix.origins :=
        (List.nodup_cons.mp (by simpa [CompiledItems.origins,
          CompiledItem.origin] using sourceNodup)).1
      obtain ⟨targetSuffix, targetSuffixCompiled, _⟩ :=
        layout.compileFrameItemsAway consistent admissible.terminal_body
          targetWf parent parentAway sourceContext targetContext sourceBinders
          targetBinders wireMap (fun relation => relation) sourceExact
          targetExact wireGet (fun binder => by
            rw [bindersMapped]
            cases sourceBinders binder <;> rfl) suffixDirect
          (fun sibling member => by
            have siblingParent :=
              (mem_localOccurrences_child input.frame.val parent sibling).mp
                (suffixDirect _ member)
            apply sibling_not_encloses input.frame.property sourceParent
              siblingParent
            · intro same
              subst sibling
              exact originNotSuffix member
            · exact selectedEncloses)
          suffixCompiled
      let targetHead : CompiledItem layout.plugRaw targetContext sourceRels
          targetBinders := .cut targetChild
      have targetRegion : layout.plugRaw.regions
          (layout.frameRegion origin) = .cut (layout.frameRegion parent) := by
        rw [layout.plugRaw_regions_frame, sourceRegion]
        rfl
      have targetHeadDirect : LocalOccurrence.child (layout.frameRegion origin) ∈
          localOccurrences layout.plugRaw (layout.frameRegion parent) := by
        rw [layout.localOccurrences_frameRegion_of_ne_site parent parentAway]
        exact List.mem_map.mpr ⟨.child origin, headDirect, rfl⟩
      have targetHeadCompiled : compileOccurrence? layout.plugRaw targetWf
          (layout.frameRegion parent) targetContext targetBinders
          (.child (layout.frameRegion origin)) targetHeadDirect =
            some targetHead := by
        rw [compileOccurrence?_child_cut targetWf
          (layout.frameRegion parent) (layout.frameRegion origin) targetContext
          targetBinders targetHeadDirect targetRegion, targetChildCompiled]
        rfl
      refine ⟨.cons targetHead targetSuffix, ?_⟩
      change compileItems? layout.plugRaw targetWf (layout.frameRegion parent)
        targetContext targetBinders
        (.child (layout.frameRegion origin) ::
          suffix.origins.map layout.mapFrameOccurrence) _ =
          some (.cons targetHead targetSuffix)
      rw [compileItems?_cons, targetHeadCompiled]
      rw [targetSuffixCompiled]
      rfl
    case bubble origin arity body suffix nested =>
      obtain ⟨headCompiled, suffixCompiled⟩ :=
        compileItems?_cons_inv input.frame.property parent sourceContext
          sourceBinders (.bubble arity body) suffix sourceDirect compiled
      let headDirect : LocalOccurrence.child origin ∈
          localOccurrences input.frame.val parent :=
        sourceDirect (.child origin)
          (by simp [CompiledItems.origins, CompiledItem.origin])
      let suffixDirect : ∀ occurrence, occurrence ∈ suffix.origins →
          occurrence ∈ localOccurrences input.frame.val parent := by
        intro occurrence member
        apply sourceDirect occurrence
        simp only [CompiledItems.origins, CompiledItem.origin, List.mem_cons]
        exact Or.inr member
      have sourceParent : (input.frame.val.regions origin).parent? =
          some parent :=
        (mem_localOccurrences_child input.frame.val parent origin).mp headDirect
      have headCompiled' : compileOccurrence? input.frame.val
          input.frame.property parent sourceContext sourceBinders
          (.child origin) headDirect = some (.bubble arity body) := by
        simpa only [CompiledItem.origin] using headCompiled
      have sourceRegion : input.frame.val.regions origin =
          .bubble parent arity := by
        cases regionEq : input.frame.val.regions origin with
        | sheet =>
            rw [compileOccurrence?_child_sheet input.frame.property parent
              origin sourceContext sourceBinders headDirect regionEq] at headCompiled'
            contradiction
        | cut actualParent =>
            have parentEq : actualParent = parent := by
              simpa [regionEq, CRegion.parent?] using sourceParent
            subst actualParent
            rw [compileOccurrence?_child_cut input.frame.property parent origin
              sourceContext sourceBinders headDirect regionEq] at headCompiled'
            cases childCompiled : compileRegion? input.frame.val
                input.frame.property origin sourceContext sourceBinders <;>
              simp [childCompiled] at headCompiled'
        | bubble actualParent actualArity =>
            have parentEq : actualParent = parent := by
              simpa [regionEq, CRegion.parent?] using sourceParent
            have arityEq : actualArity = arity := by
              rw [compileOccurrence?_child_bubble input.frame.property parent
                origin sourceContext sourceBinders actualArity headDirect
                (parentEq ▸ regionEq)] at headCompiled'
              cases childCompiled : compileRegion? input.frame.val
                  input.frame.property origin sourceContext
                  (sourceBinders.push origin actualArity) <;>
                simp [childCompiled] at headCompiled'
              exact headCompiled'.1
            subst actualParent
            subst actualArity
            rfl
      have bodyCompiled := compileOccurrence?_child_bubble_body
        input.frame.property parent origin sourceContext sourceBinders arity
          headDirect sourceRegion headCompiled'
      have sourceChildExact := sourceExact.extend_child input.frame.property
        sourceParent
      have targetParent : (layout.plugRaw.regions
          (layout.frameRegion origin)).parent? =
            some (layout.frameRegion parent) := by
        rw [layout.plugRaw_regions_frame]
        exact (layout.mapFrameRegion_parent_eq_some_iff origin parent).2
          sourceParent
      have targetChildExact := targetExact.extend_child targetWf targetParent
      have childBindersMapped : ∀ binder,
          (targetBinders.push (layout.frameRegion origin) arity)
              (layout.frameRegion binder) =
            (sourceBinders.push origin arity) binder := by
        intro binder
        by_cases same : binder = origin
        · subst binder
          rw [BinderContext.push_self, BinderContext.push_self]
        · have targetDifferent : layout.frameRegion binder ≠
              layout.frameRegion origin := by
            intro equality
            exact same ((layout.frameRegion_eq_frameRegion_iff binder origin).1
              equality)
          rw [BinderContext.push_other _ arity targetDifferent,
            BinderContext.push_other _ arity same, bindersMapped]
      obtain ⟨targetChild, targetChildCompiled⟩ :=
        compileNestedAlongZipper layout consistent admissible targetWf
          relationMap hostLookup nested bodyCompiled sourceChildExact
          targetChildExact wireMap wireGet childBindersMapped
          (BinderContext.push_covers_bubble_child sourceCovers sourceRegion)
          (sourceEnumeration.bubbleChild input.frame.property sourceRegion)
      have selectedEncloses := nested.endpoint_encloses
        input.frame.property bodyCompiled sourceChildExact
          (BinderContext.push_covers_bubble_child sourceCovers sourceRegion)
          (sourceEnumeration.bubbleChild input.frame.property sourceRegion)
      have originNotSuffix : LocalOccurrence.child origin ∉ suffix.origins :=
        (List.nodup_cons.mp (by simpa [CompiledItems.origins,
          CompiledItem.origin] using sourceNodup)).1
      obtain ⟨targetSuffix, targetSuffixCompiled, _⟩ :=
        layout.compileFrameItemsAway consistent admissible.terminal_body
          targetWf parent parentAway sourceContext targetContext sourceBinders
          targetBinders wireMap (fun relation => relation) sourceExact
          targetExact wireGet (fun binder => by
            rw [bindersMapped]
            cases sourceBinders binder <;> rfl) suffixDirect
          (fun sibling member => by
            have siblingParent :=
              (mem_localOccurrences_child input.frame.val parent sibling).mp
                (suffixDirect _ member)
            apply sibling_not_encloses input.frame.property sourceParent
              siblingParent
            · intro same
              subst sibling
              exact originNotSuffix member
            · exact selectedEncloses)
          suffixCompiled
      let targetHead : CompiledItem layout.plugRaw targetContext sourceRels
          targetBinders := .bubble arity targetChild
      have targetRegion : layout.plugRaw.regions
          (layout.frameRegion origin) =
            .bubble (layout.frameRegion parent) arity := by
        rw [layout.plugRaw_regions_frame, sourceRegion]
        rfl
      have targetHeadDirect : LocalOccurrence.child (layout.frameRegion origin) ∈
          localOccurrences layout.plugRaw (layout.frameRegion parent) := by
        rw [layout.localOccurrences_frameRegion_of_ne_site parent parentAway]
        exact List.mem_map.mpr ⟨.child origin, headDirect, rfl⟩
      have targetHeadCompiled : compileOccurrence? layout.plugRaw targetWf
          (layout.frameRegion parent) targetContext targetBinders
          (.child (layout.frameRegion origin)) targetHeadDirect =
            some targetHead := by
        rw [compileOccurrence?_child_bubble targetWf
          (layout.frameRegion parent) (layout.frameRegion origin) targetContext
          targetBinders arity targetHeadDirect targetRegion, targetChildCompiled]
        rfl
      refine ⟨.cons targetHead targetSuffix, ?_⟩
      change compileItems? layout.plugRaw targetWf (layout.frameRegion parent)
        targetContext targetBinders
        (.child (layout.frameRegion origin) ::
          suffix.origins.map layout.mapFrameOccurrence) _ =
          some (.cons targetHead targetSuffix)
      rw [compileItems?_cons, targetHeadCompiled]
      rw [targetSuffixCompiled]
      rfl
    case tail head suffix nested =>
      obtain ⟨headCompiled, suffixCompiled⟩ :=
        compileItems?_cons_inv input.frame.property parent sourceContext
          sourceBinders head suffix sourceDirect compiled
      let headDirect : head.origin ∈ localOccurrences input.frame.val parent :=
        sourceDirect head.origin (by simp [CompiledItems.origins])
      let suffixDirect : ∀ occurrence, occurrence ∈ suffix.origins →
          occurrence ∈ localOccurrences input.frame.val parent := by
        intro occurrence member
        apply sourceDirect occurrence
        simp only [CompiledItems.origins, List.mem_cons]
        exact Or.inr member
      have suffixNodup : suffix.origins.Nodup :=
        (List.nodup_cons.mp (by simpa [CompiledItems.origins] using
          sourceNodup)).2
      obtain ⟨selected, selectedMember, selectedParent, selectedEncloses⟩ :=
        nested.selected_child input.frame.property parent sourceExact
          sourceCovers sourceEnumeration suffixDirect suffixCompiled
      have headNotSuffix : head.origin ∉ suffix.origins :=
        (List.nodup_cons.mp (by simpa [CompiledItems.origins] using
          sourceNodup)).1
      let headItems : CompiledItems input.frame.val sourceContext sourceRels
          sourceBinders := .cons head .nil
      let headItemsDirect : ∀ occurrence, occurrence ∈ headItems.origins →
          occurrence ∈ localOccurrences input.frame.val parent := by
        intro occurrence member
        have occurrenceEq : occurrence = head.origin := by
          simpa [headItems, CompiledItems.origins] using member
        subst occurrence
        exact headDirect
      have headItemsCompiled : compileItems? input.frame.val
          input.frame.property parent sourceContext sourceBinders
          headItems.origins headItemsDirect = some headItems := by
        change compileItems? input.frame.val input.frame.property parent
          sourceContext sourceBinders [head.origin] _ = some (.cons head .nil)
        rw [compileItems?_cons, headCompiled, compileItems?_nil]
        rfl
      obtain ⟨targetHead, targetHeadCompiled, _⟩ :=
        layout.compileFrameItemsAway consistent admissible.terminal_body
          targetWf parent parentAway sourceContext targetContext sourceBinders
          targetBinders wireMap (fun relation => relation) sourceExact
          targetExact wireGet (fun binder => by
            rw [bindersMapped]
            cases sourceBinders binder <;> rfl) headItemsDirect
          (fun child member => by
            have childOccurrenceEq : LocalOccurrence.child child =
                head.origin := by
              simpa [headItems, CompiledItems.origins] using member
            have childParent : (input.frame.val.regions child).parent? =
                some parent := by
              apply (mem_localOccurrences_child input.frame.val parent child).mp
              rw [childOccurrenceEq]
              exact headDirect
            apply sibling_not_encloses input.frame.property selectedParent
              childParent
            · intro same
              subst child
              apply headNotSuffix
              rw [← childOccurrenceEq]
              exact selectedMember
            · exact selectedEncloses)
          headItemsCompiled
      obtain ⟨targetSuffix, targetSuffixCompiled⟩ :=
        compileItemsAlongZipper layout consistent admissible targetWf
          relationMap hostLookup nested suffixDirect suffixCompiled suffixNodup
          parentAway sourceExact targetExact wireMap wireGet bindersMapped
          sourceCovers sourceEnumeration
      refine ⟨targetHead.append targetSuffix, ?_⟩
      have combined := compileItems?_append targetWf
        (layout.frameRegion parent) targetContext targetBinders
        (headItems.origins.map layout.mapFrameOccurrence)
        (suffix.origins.map layout.mapFrameOccurrence)
        (fun occurrence member => by
          rw [layout.localOccurrences_frameRegion_of_ne_site parent parentAway]
          rcases List.mem_append.mp member with headMember | suffixMember
          · obtain ⟨sourceOccurrence, sourceMember, rfl⟩ :=
              List.mem_map.mp headMember
            exact List.mem_map.mpr
              ⟨sourceOccurrence, sourceDirect sourceOccurrence (by
                simp only [CompiledItems.origins, List.mem_cons]
                exact Or.inl (by
                  simpa [headItems, CompiledItems.origins] using sourceMember)),
                rfl⟩
          · obtain ⟨sourceOccurrence, sourceMember, rfl⟩ :=
              List.mem_map.mp suffixMember
            exact List.mem_map.mpr
              ⟨sourceOccurrence, sourceDirect sourceOccurrence (by
                simp only [CompiledItems.origins, List.mem_cons]
                exact Or.inr sourceMember), rfl⟩)
        targetHeadCompiled targetSuffixCompiled
      simpa only [headItems, CompiledItems.origins, CompiledItem.origin,
        List.map_cons, List.map_nil, List.singleton_append] using combined
end

/-- Compile the complete target open root by following the one canonical source
zipper to the splice site. -/
private theorem compileRootAlongZipper
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (boundary : List (Fin input.frame.val.wireCount))
    (admissible : input.Admissible)
    (targetOpenWf : (layout.outputOpenRoot input boundary).WellFormed)
    {endpointCall : CompilerCall input.frame.val}
    {endpoint : CompiledRegion input.frame.val endpointCall}
    (relationMap : RelationRenaming
      (CompiledSite.endpointCall (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).rels endpointCall.rels)
    (hostLookup : ∀ {arity} (relation : RelVar
        (CompiledSite.endpointCall (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).rels arity),
      endpointCall.binders (input.binderTarget
          (terminalRelationProxyEquiv input relation.index)) =
        some ⟨arity, relationMap relation⟩)
    {sourceBody : CompiledRegion input.frame.val
      (.root (frameOpen input boundary).exposedWires
        (frameOpen input boundary).hiddenWires)}
    {site : Fin input.frame.val.regionCount}
    (focus : CompiledZipper input.frame.val sourceBody site
      endpointCall endpoint)
    (siteEq : site = input.site)
    (sourceCompiled : compileRoot? input.frame.val input.frame.property
      (frameOpen input boundary).exposedWires
      (frameOpen input boundary).hiddenWires = some sourceBody)
    (sourceExact : WireContext.Exact (frameOpen input boundary).rootWires
      input.frame.val.root) :
    ∃ targetBody : CompiledRegion layout.plugRaw
        (.root (layout.outputOpenRoot input boundary).exposedWires
          (layout.outputOpenRoot input boundary).hiddenWires),
      compileRoot? layout.plugRaw targetOpenWf.diagram_well_formed
        (layout.outputOpenRoot input boundary).exposedWires
        (layout.outputOpenRoot input boundary).hiddenWires =
          some targetBody := by
  cases focus
  case here =>
    have atSite : input.frame.val.root = input.site := siteEq
    simpa only [compileRoot?] using
      layout.compileSpliceSite consistent boundary admissible targetOpenWf
        (.root (frameOpen input boundary).exposedWires
          (frameOpen input boundary).hiddenWires) atSite
        (atSite ▸ sourceExact)
        relationMap hostLookup sourceCompiled
  case child items nested =>
    subst site
    let sourceCall : CompilerCall input.frame.val :=
      .root (frameOpen input boundary).exposedWires
        (frameOpen input boundary).hiddenWires
    have sourceItemsCompiled := sourceCall.compile?_items_of_success
      input.frame.property (by simpa [sourceCall, compileRoot?] using
        sourceCompiled)
    have sourceOrigins := compileItems?_origins input.frame.property
      input.frame.val.root _ _ sourceItemsCompiled
    change items.origins =
      localOccurrences input.frame.val input.frame.val.root at sourceOrigins
    have itemsDirect : ∀ occurrence, occurrence ∈ items.origins →
        occurrence ∈ localOccurrences input.frame.val input.frame.val.root := by
      intro occurrence member
      rw [← sourceOrigins]
      exact member
    have itemsCompiled : compileItems? input.frame.val input.frame.property
        input.frame.val.root (frameOpen input boundary).rootWires
        BinderContext.empty items.origins itemsDirect = some items := by
      exact (compileItems?_congr_occurrences input.frame.property
        input.frame.val.root (context := (frameOpen input boundary).rootWires)
        (binders := BinderContext.empty) (equal := sourceOrigins) itemsDirect
        (fun _ member => member)).trans sourceItemsCompiled
    have sourceCovers := BinderContext.empty_covers_root input.frame.property
    have sourceEnumeration := BinderContext.Enumeration.empty input.frame.val
    obtain ⟨selected, _, selectedParent, selectedEncloses⟩ :=
      nested.selected_child input.frame.property input.frame.val.root sourceExact
        sourceCovers sourceEnumeration itemsDirect itemsCompiled
    have rootAway : input.frame.val.root ≠ input.site := by
      intro same
      exact Elaboration.checked_direct_child_not_encloses_parent
        input.frame.property selectedParent (by simpa [same] using
          selectedEncloses)
    have targetExact : WireContext.Exact
        (layout.outputOpenRoot input boundary).rootWires layout.plugRaw.root := by
      simpa [OpenDiagram.rootWires] using openRootWires_exact targetOpenWf
    let wireMap := layout.mapFrameExactContext consistent input.frame.val.root
      (frameOpen input boundary).rootWires
      (layout.outputOpenRoot input boundary).rootWires sourceExact targetExact
    have wireGet : ∀ index,
        (layout.outputOpenRoot input boundary).rootWires.get (wireMap index) =
          layout.frameWireMap
            ((frameOpen input boundary).rootWires.get index) :=
      layout.mapFrameExactContext_get consistent input.frame.val.root
        (frameOpen input boundary).rootWires
        (layout.outputOpenRoot input boundary).rootWires sourceExact targetExact
    have sourceNodup : items.origins.Nodup := by
      exact sourceOrigins.symm ▸
        localOccurrences_nodup input.frame.val input.frame.val.root
    obtain ⟨targetItems, targetItemsCompiled⟩ :=
      compileItemsAlongZipper layout consistent admissible
        targetOpenWf.diagram_well_formed relationMap hostLookup nested
        itemsDirect itemsCompiled sourceNodup rootAway sourceExact targetExact
        wireMap wireGet (show ∀ binder,
          (BinderContext.empty : BinderContext layout.plugRaw [])
              (layout.frameRegion binder) =
            (BinderContext.empty : BinderContext input.frame.val []) binder from
          fun _ => rfl) sourceCovers sourceEnumeration
    refine ⟨.mk targetItems, ?_⟩
    have occurrenceEq : localOccurrences layout.plugRaw layout.plugRaw.root =
        items.origins.map layout.mapFrameOccurrence := by
      change localOccurrences layout.plugRaw
          (layout.frameRegion input.frame.val.root) = _
      rw [layout.localOccurrences_frameRegion_of_ne_site
        input.frame.val.root rootAway]
      simpa only [CompiledRegion.items] using
        congrArg (List.map layout.mapFrameOccurrence) sourceOrigins.symm
    have targetCanonical : compileItems? layout.plugRaw
        targetOpenWf.diagram_well_formed layout.plugRaw.root
        (layout.outputOpenRoot input boundary).rootWires BinderContext.empty
        (localOccurrences layout.plugRaw layout.plugRaw.root)
        (fun _ member => member) = some targetItems :=
      (compileItems?_congr_occurrences targetOpenWf.diagram_well_formed
        layout.plugRaw.root _ _ occurrenceEq (fun _ member => member) _).trans
          targetItemsCompiled
    rw [compileRoot?_eq_compileItems?]
    change (do
      let compiledItems ← compileItems? layout.plugRaw
        targetOpenWf.diagram_well_formed layout.plugRaw.root
        (layout.outputOpenRoot input boundary).rootWires BinderContext.empty
        (localOccurrences layout.plugRaw layout.plugRaw.root) _
      pure (CompiledRegion.mk compiledItems : CompiledRegion layout.plugRaw
        (.root (layout.outputOpenRoot input boundary).exposedWires
          (layout.outputOpenRoot input boundary).hiddenWires))) =
        some (CompiledRegion.mk targetItems : CompiledRegion layout.plugRaw
          (.root (layout.outputOpenRoot input boundary).exposedWires
            (layout.outputOpenRoot input boundary).hiddenWires))
    rw [targetCanonical]
    rfl

end Splice.Input.PlugLayout

end VisualProof.Concrete
