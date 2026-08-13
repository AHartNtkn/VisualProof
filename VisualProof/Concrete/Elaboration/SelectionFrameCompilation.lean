import VisualProof.Concrete.Elaboration.SelectionReplacementCompilation

/-! Lift selection compaction through the canonical source compiler zipper. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Diagram
open Theory
open Elaboration

namespace FrameDomains

noncomputable def targetCall
    (domains : FrameDomains d selection)
    (sourceCall : CompilerCall d)
    (originSurvives : domains.regions.survives sourceCall.origin = true)
    (targetOuter targetLocal : WireContext (d.removeRaw selection domains))
    (targetBinders : BinderContext (d.removeRaw selection domains)
      sourceCall.rels) : CompilerCall (d.removeRaw selection domains) :=
  match sourceCall with
  | .root _ _ => .root targetOuter targetLocal
  | .nested origin _ rels _ =>
      .nested (domains.regions.index origin originSurvives) targetOuter rels
        targetBinders

noncomputable def targetBody
    (domains : FrameDomains d selection)
    (sourceCall : CompilerCall d)
    (originSurvives : domains.regions.survives sourceCall.origin = true)
    (targetOuter targetLocal : WireContext (d.removeRaw selection domains))
    (targetBinders : BinderContext (d.removeRaw selection domains)
      sourceCall.rels)
    (localEq : (domains.targetCall sourceCall originSurvives targetOuter
      targetLocal targetBinders).localContext = targetLocal)
    (items : CompiledItems (d.removeRaw selection domains)
      (targetOuter ++ targetLocal) sourceCall.rels targetBinders) :
    CompiledRegion (d.removeRaw selection domains)
      (domains.targetCall sourceCall originSurvives targetOuter targetLocal
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
      exact .mk items
  | nested =>
      change exactScopeWires (d.removeRaw selection domains) _ = targetLocal
        at localEq
      subst targetLocal
      exact .mk items

noncomputable def targetErase
    (domains : FrameDomains d selection)
    (sourceCall : CompilerCall d)
    (originSurvives : domains.regions.survives sourceCall.origin = true)
    (targetOuter targetLocal : WireContext (d.removeRaw selection domains))
    (targetBinders : BinderContext (d.removeRaw selection domains)
      sourceCall.rels)
    (body : CompiledRegion (d.removeRaw selection domains)
      (domains.targetCall sourceCall originSurvives targetOuter targetLocal
        targetBinders)) : Region targetOuter.length sourceCall.rels := by
  cases sourceCall <;> exact body.erase

@[simp] theorem targetErase_targetBody
    (domains : FrameDomains d selection)
    (sourceCall : CompilerCall d)
    (originSurvives : domains.regions.survives sourceCall.origin = true)
    (targetOuter targetLocal : WireContext (d.removeRaw selection domains))
    (targetBinders : BinderContext (d.removeRaw selection domains)
      sourceCall.rels)
    (localEq : (domains.targetCall sourceCall originSurvives targetOuter
      targetLocal targetBinders).localContext = targetLocal)
    (items : CompiledItems (d.removeRaw selection domains)
      (targetOuter ++ targetLocal) sourceCall.rels targetBinders) :
    domains.targetErase sourceCall originSurvives targetOuter targetLocal
        targetBinders (domains.targetBody sourceCall originSurvives targetOuter
          targetLocal targetBinders localEq items) =
      Region.mk targetLocal.length
        (items.erase.castWiresEq (by exact List.length_append)) := by
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
      change exactScopeWires (d.removeRaw selection domains) _ = targetLocal
        at localEq
      subst targetLocal
      rfl

theorem targetCall_compile_of_items
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (sourceCall : CompilerCall host.val)
    (originSurvives : domains.regions.survives sourceCall.origin = true)
    (targetOuter targetLocal : WireContext
      (host.val.removeRaw selection domains))
    (targetBinders : BinderContext
      (host.val.removeRaw selection domains) sourceCall.rels)
    (localEq : (domains.targetCall sourceCall originSurvives targetOuter
      targetLocal targetBinders).localContext = targetLocal)
    (items : CompiledItems (host.val.removeRaw selection domains)
      (targetOuter ++ targetLocal) sourceCall.rels targetBinders)
    (compiled : compileItems? (host.val.removeRaw selection domains)
      (Diagram.removeRaw_wellFormed host selection domains)
      (domains.regions.index sourceCall.origin originSurvives)
      (targetOuter ++ targetLocal) targetBinders
      (localOccurrences (host.val.removeRaw selection domains)
        (domains.regions.index sourceCall.origin originSurvives))
      (fun _ member => member) = some items) :
    (domains.targetCall sourceCall originSurvives targetOuter targetLocal
      targetBinders).compile? (host.val.removeRaw selection domains)
        (Diagram.removeRaw_wellFormed host selection domains) =
      some (domains.targetBody sourceCall originSurvives targetOuter
        targetLocal targetBinders localEq items) := by
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
      have targetRoot : domains.regions.index host.val.root originSurvives =
          (host.val.removeRaw selection domains).root := by
        apply domains.regions.origin_injective
        rw [domains.regions.origin_index]
        exact domains.root_origin.symm
      change (CompilerCall.root targetOuter targetLocal).compile?
          (host.val.removeRaw selection domains)
            (Diagram.removeRaw_wellFormed host selection domains) =
        some (.mk items)
      rw [CompilerCall.compile?_eq_compileItems?]
      change (do
        let result ← compileItems? (host.val.removeRaw selection domains)
          (Diagram.removeRaw_wellFormed host selection domains)
          (host.val.removeRaw selection domains).root
          (targetOuter ++ targetLocal) BinderContext.empty
          (localOccurrences (host.val.removeRaw selection domains)
            (host.val.removeRaw selection domains).root) (fun _ member => member)
        pure (CompiledRegion.mk result : CompiledRegion
          (host.val.removeRaw selection domains)
            (.root targetOuter targetLocal))) = some (.mk items)
      have normalized : compileItems? (host.val.removeRaw selection domains)
          (Diagram.removeRaw_wellFormed host selection domains)
          (domains.regions.index host.val.root originSurvives)
          (targetOuter ++ targetLocal) BinderContext.empty
          (localOccurrences (host.val.removeRaw selection domains)
            (domains.regions.index host.val.root originSurvives))
          (fun _ member => member) = some items := by
        simpa using compiled
      rw [targetRoot] at normalized
      rw [normalized]
      rfl
  | nested origin context rels binders =>
      change exactScopeWires (host.val.removeRaw selection domains)
        (domains.regions.index origin originSurvives) = targetLocal at localEq
      subst targetLocal
      rw [CompilerCall.compile?_eq_compileItems?]
      change (do
        let result ← compileItems? (host.val.removeRaw selection domains)
          (Diagram.removeRaw_wellFormed host selection domains)
          (domains.regions.index origin originSurvives)
          (targetOuter ++ exactScopeWires
            (host.val.removeRaw selection domains)
            (domains.regions.index origin originSurvives)) targetBinders
          (localOccurrences (host.val.removeRaw selection domains)
            (domains.regions.index origin originSurvives)) (fun _ member => member)
        pure (CompiledRegion.mk result : CompiledRegion
          (host.val.removeRaw selection domains)
            (.nested (domains.regions.index origin originSurvives)
              targetOuter rels targetBinders))) = some (.mk items)
      have normalized : compileItems? (host.val.removeRaw selection domains)
          (Diagram.removeRaw_wellFormed host selection domains)
          (domains.regions.index origin originSurvives)
          (targetOuter ++ exactScopeWires
            (host.val.removeRaw selection domains)
            (domains.regions.index origin originSurvives)) targetBinders
          (localOccurrences (host.val.removeRaw selection domains)
            (domains.regions.index origin originSurvives))
          (fun _ member => member) = some items := by
        simpa using compiled
      rw [normalized]
      rfl

structure FrameEvidence
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    (sourceCall : CompilerCall host.val)
    (sourceBody : CompiledRegion host.val sourceCall)
    (targetOuter targetLocal : WireContext
      (host.val.removeRaw selection domains))
    (targetBinders : BinderContext
      (host.val.removeRaw selection domains) sourceCall.rels) where
  originSurvives : domains.regions.survives sourceCall.origin = true
  outerEq : targetOuter = domains.mapWireContext sourceCall.outerContext
  localEq : targetLocal = domains.mapWireContext sourceCall.localContext
  outerSurvives : ∀ wire, wire ∈ sourceCall.outerContext →
    domains.wires.survives wire = true
  targetLocalCall : (domains.targetCall sourceCall originSurvives targetOuter
    targetLocal targetBinders).localContext = targetLocal
  bindersEq : targetBinders = domains.mapBinderContext sourceCall.binders
  sourceExact : sourceCall.fullContext.Exact sourceCall.origin
  sourceCovers : sourceCall.binders.Covers sourceCall.origin
  sourceEnumeration : BinderContext.Enumeration host.val sourceCall.binders
    sourceCall.origin
  sourceCompiled : sourceCall.compile? host.val host.property = some sourceBody

noncomputable def FrameEvidence.outerWire
    (frame : FrameEvidence host selection domains sourceCall sourceBody
      targetOuter targetLocal targetBinders) :
    FiniteEquiv (Fin targetOuter.length)
      (Fin sourceCall.outerContext.length) :=
  (FiniteEquiv.finCast (congrArg List.length frame.outerEq)).trans
    (domains.mapWireContextEquiv sourceCall.outerContext frame.outerSurvives)

structure FrameFocusResult
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    {sourceCall endpointCall : CompilerCall host.val}
    {sourceBody : CompiledRegion host.val sourceCall}
    {endpoint : CompiledRegion host.val endpointCall}
    {site : Fin host.val.regionCount}
    (focus : CompiledZipper host.val sourceBody site endpointCall endpoint)
    (targetOuter targetLocal : WireContext
      (host.val.removeRaw selection domains))
    (targetBinders : BinderContext
      (host.val.removeRaw selection domains) sourceCall.rels)
    (frame : FrameEvidence host selection domains sourceCall sourceBody
      targetOuter targetLocal targetBinders) where
  targetBody : CompiledRegion (host.val.removeRaw selection domains)
    (domains.targetCall sourceCall frame.originSurvives targetOuter targetLocal
      targetBinders)
  targetCompiled : (domains.targetCall sourceCall frame.originSurvives
    targetOuter targetLocal targetBinders).compile?
      (host.val.removeRaw selection domains)
      (Diagram.removeRaw_wellFormed host selection domains) = some targetBody
  holeWires : Nat
  holeWire : FiniteEquiv (Fin holeWires)
    (Fin endpointCall.outerContext.length)
  targetSite : Region holeWires endpointCall.rels
  targetContext : DiagramContext targetOuter.length holeWires
    sourceCall.rels endpointCall.rels
  alignment : DiagramContextIso
    frame.outerWire holeWire sourceCall.rels endpointCall.rels
    targetContext focus.intrinsic.context
  targetRebuild : targetContext.fill targetSite =
    domains.targetErase sourceCall frame.originSurvives targetOuter targetLocal
      targetBinders targetBody

private abbrev FrameRegionFold
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    {sourceCall endpointCall : CompilerCall host.val}
    (sourceBody : CompiledRegion host.val sourceCall)
    (site : Fin host.val.regionCount)
    (endpoint : CompiledRegion host.val endpointCall)
    (focus : CompiledZipper host.val sourceBody site endpointCall endpoint) :=
  (siteEq : site = selection.val.anchor) →
  (targetOuter targetLocal : WireContext
    (host.val.removeRaw selection domains)) →
  (targetBinders : BinderContext
    (host.val.removeRaw selection domains) sourceCall.rels) →
  (frame : FrameEvidence host selection domains sourceCall sourceBody
    targetOuter targetLocal targetBinders) →
  Nonempty (FrameFocusResult host selection domains focus targetOuter
    targetLocal targetBinders frame)

private abbrev FrameItemsFold
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    {sourceCall endpointCall : CompilerCall host.val}
    (items : CompiledItems host.val sourceCall.fullContext
      sourceCall.rels sourceCall.binders)
    (site : Fin host.val.regionCount)
    (endpoint : CompiledRegion host.val endpointCall)
    (focus : CompiledItemsZipper host.val items site endpointCall endpoint) :=
  (siteEq : site = selection.val.anchor) →
  (targetOuter targetLocal : WireContext
    (host.val.removeRaw selection domains)) →
  (targetBinders : BinderContext
    (host.val.removeRaw selection domains) sourceCall.rels) →
  (frame : FrameEvidence host selection domains sourceCall (.mk items)
    targetOuter targetLocal targetBinders) →
  Nonempty (FrameFocusResult host selection domains (.child focus)
    targetOuter targetLocal targetBinders frame)

/-- The single source-focus fold constructs the compact frame compiler result
and aligns its unfilled endpoint context with the source endpoint context. -/
theorem compileAlongFocus
    (host : Checked) (selection : CheckedSelection host.val)
    (domains : FrameDomains host.val selection)
    {sourceCall endpointCall : CompilerCall host.val}
    {sourceBody : CompiledRegion host.val sourceCall}
    {site : Fin host.val.regionCount}
    {endpoint : CompiledRegion host.val endpointCall}
    (focus : CompiledZipper host.val sourceBody site endpointCall endpoint) :
    FrameRegionFold host selection domains sourceBody site endpoint focus := by
  apply CompiledZipper.rec
    (motive_1 := fun sourceBody site _ endpoint focus =>
      FrameRegionFold host selection domains sourceBody site endpoint focus)
    (motive_2 := fun items site _ endpoint focus =>
      FrameItemsFold host selection domains items site endpoint focus)
  · intro sourceCall source siteEq targetOuter targetLocal targetBinders frame
    have originEq : sourceCall.origin = selection.val.anchor := siteEq
    cases sourceCall with
    | root sourceAmbient sourceLocal =>
        let result := Classical.choice (domains.compileRootSurvivors host
          selection sourceAmbient sourceLocal targetOuter targetLocal
          frame.outerEq frame.localEq frame.sourceExact source
          frame.sourceCompiled)
        refine ⟨{
          targetBody := result.body
          targetCompiled := result.compiled
          holeWires := targetOuter.length
          holeWire := frame.outerWire
          targetSite := result.body.erase
          targetContext := .hole
          alignment := .hole frame.outerWire
          targetRebuild := ?_
        }⟩
        rfl
    | nested origin sourceOuter rels sourceBinders =>
        let result := Classical.choice (domains.compileRegionSurvivors host
          selection origin frame.originSurvives sourceOuter sourceBinders
          targetOuter frame.outerEq targetBinders frame.bindersEq
          frame.sourceExact source frame.sourceCompiled)
        refine ⟨{
          targetBody := result.body
          targetCompiled := result.compiled
          holeWires := targetOuter.length
          holeWire := frame.outerWire
          targetSite := result.body.erase
          targetContext := .hole
          alignment := .hole frame.outerWire
          targetRebuild := ?_
        }⟩
        rfl
  · intro sourceCall endpointCall items site endpoint nested induction
      siteEq targetOuter targetLocal targetBinders frame
    exact induction siteEq targetOuter targetLocal targetBinders frame
  · intro sourceCall origin body before suffix items site endpointCall
      endpoint nested rebuild induction siteEq targetOuter targetLocal
      targetBinders frame
    subst items
    have sourceItemsCompiled := sourceCall.compile?_items_of_success
      host.property frame.sourceCompiled
    have sourceOrigins := compileItems?_origins host.property
      sourceCall.origin sourceCall.fullContext sourceCall.binders
      sourceItemsCompiled
    let sourceDirect : ∀ occurrence,
        occurrence ∈ (before.append (.cons (.cut body) suffix)).origins →
          occurrence ∈ localOccurrences host.val sourceCall.origin := by
      intro occurrence member
      simpa only [sourceOrigins] using member
    have canonicalCompiled : compileItems? host.val host.property
        sourceCall.origin sourceCall.fullContext sourceCall.binders
        (before.append (.cons (.cut body) suffix)).origins sourceDirect =
          some (before.append (.cons (.cut body) suffix)) := by
      simpa only [sourceOrigins] using sourceItemsCompiled
    obtain ⟨beforeCompiled, selectedCompiled, suffixCompiled⟩ :=
      compileItems?_selected_inv host.property sourceCall.origin
        sourceCall.fullContext sourceCall.binders before (.cut body) suffix
        sourceDirect canonicalCompiled
    let selectedDirect : LocalOccurrence.child origin ∈
        localOccurrences host.val sourceCall.origin :=
      sourceDirect (.child origin) (by
        simp [CompiledItems.origins_append, CompiledItems.origins,
          CompiledItem.origin])
    have selectedCompiled' : compileOccurrence? host.val host.property
        sourceCall.origin sourceCall.fullContext sourceCall.binders
        (.child origin) selectedDirect = some (.cut body) := by
      simpa only [CompiledItem.origin] using selectedCompiled
    have sourceParent := (mem_localOccurrences_child host.val
      sourceCall.origin origin).mp selectedDirect
    have sourceRegion : host.val.regions origin = .cut sourceCall.origin := by
      cases regionEq : host.val.regions origin with
      | sheet =>
          rw [compileOccurrence?_child_sheet host.property sourceCall.origin
            origin sourceCall.fullContext sourceCall.binders selectedDirect
            regionEq] at selectedCompiled'
          contradiction
      | cut parent =>
          have parentEq : parent = sourceCall.origin := by
            simpa [regionEq, CRegion.parent?] using sourceParent
          subst parent
          rfl
      | bubble parent arity =>
          have parentEq : parent = sourceCall.origin := by
            simpa [regionEq, CRegion.parent?] using sourceParent
          subst parent
          rw [compileOccurrence?_child_bubble host.property sourceCall.origin
            origin sourceCall.fullContext sourceCall.binders arity
            selectedDirect regionEq] at selectedCompiled'
          cases childResult : compileRegion? host.val host.property origin
              sourceCall.fullContext (sourceCall.binders.push origin arity) <;>
            simp [childResult] at selectedCompiled'
    have childCompiled := compileOccurrence?_child_cut_body host.property
      sourceCall.origin origin sourceCall.fullContext sourceCall.binders
      selectedDirect sourceRegion selectedCompiled'
    have childExact := frame.sourceExact.extend_child host.property sourceParent
    have childCovers := BinderContext.covers_cut_child frame.sourceCovers
      sourceRegion
    have childEnumeration := frame.sourceEnumeration.cutChild host.property
      sourceRegion
    have childEncloses := nested.endpoint_encloses host.property childCompiled
      childExact childCovers childEnumeration
    have parentEnclosesChild : host.val.Encloses sourceCall.origin origin := by
      refine ⟨⟨1, by omega⟩, ?_⟩
      simp [Diagram.climb, sourceParent]
    have above : host.val.Encloses sourceCall.origin selection.val.anchor :=
      checked_encloses_trans host.property parentEnclosesChild
        (by simpa only [siteEq] using childEncloses)
    have parentAway : sourceCall.origin ≠ selection.val.anchor := by
      intro same
      rw [same] at sourceParent
      exact checked_direct_child_not_encloses_parent host.property sourceParent
        (by simpa only [siteEq] using childEncloses)
    have localSurvives : ∀ wire, wire ∈ sourceCall.localContext →
        domains.wires.survives wire = true := by
      intro wire member
      exact domains.visibleWire_survives_above host selection sourceCall.origin
        above parentAway sourceCall.fullContext frame.sourceExact wire
        (List.mem_append_right _ member)
    let localWire : FiniteEquiv (Fin targetLocal.length)
        (Fin sourceCall.localContext.length) :=
      (FiniteEquiv.finCast (congrArg List.length frame.localEq)).trans
        (domains.mapWireContextEquiv sourceCall.localContext localSurvives)
    let childTargetOuter := targetOuter ++ targetLocal
    let childTargetLocal := domains.mapWireContext
      (exactScopeWires host.val origin)
    have childOuterEq : childTargetOuter =
        domains.mapWireContext sourceCall.fullContext := by
      dsimp only [childTargetOuter]
      rw [CompilerCall.fullContext, domains.mapWireContext_append,
        ← frame.outerEq, ← frame.localEq]
    have childSurvives : domains.regions.survives origin = true :=
      domains.localOccurrence_survives_above host selection sourceCall.origin
        above parentAway (.child origin) selectedDirect
    have childLocalCall : exactScopeWires
        (host.val.removeRaw selection domains)
          (domains.regions.index origin childSurvives) = childTargetLocal := by
      dsimp only [childTargetLocal]
      rw [← domains.mapWireContext_exactScope host selection
        (domains.regions.index origin childSurvives),
        domains.regions.origin_index]
    have childOuterSurvives : ∀ wire, wire ∈ sourceCall.fullContext →
        domains.wires.survives wire = true := by
      intro wire member
      exact domains.visibleWire_survives_above host selection sourceCall.origin
        above parentAway sourceCall.fullContext frame.sourceExact wire member
    let childFrame : FrameEvidence host selection domains
        (.nested origin sourceCall.fullContext sourceCall.rels
          sourceCall.binders) body childTargetOuter childTargetLocal
          targetBinders := {
      originSurvives := childSurvives
      outerEq := childOuterEq
      localEq := rfl
      outerSurvives := childOuterSurvives
      targetLocalCall := childLocalCall
      bindersEq := frame.bindersEq
      sourceExact := childExact
      sourceCovers := childCovers
      sourceEnumeration := childEnumeration
      sourceCompiled := childCompiled
    }
    obtain ⟨childResult⟩ := induction siteEq childTargetOuter
      childTargetLocal targetBinders childFrame
    have sourceNodup :
        (before.append (.cons (.cut body) suffix)).origins.Nodup := by
      rw [sourceOrigins]
      exact localOccurrences_nodup host.val sourceCall.origin
    have beforeDisjointTail := (List.nodup_append.mp (by
      simpa only [CompiledItems.origins_append] using sourceNodup)).2.2
    have selectedNotBefore : LocalOccurrence.child origin ∉ before.origins := by
      intro member
      exact beforeDisjointTail _ member _ (by
        simp [CompiledItem.origin]) rfl
    have tailNodup : (CompiledItems.cons (.cut body) suffix).origins.Nodup :=
      (List.nodup_append.mp (by
        simpa only [CompiledItems.origins_append] using sourceNodup)).2.1
    have selectedNotSuffix : LocalOccurrence.child origin ∉ suffix.origins :=
      (List.nodup_cons.mp (by
        simpa only [CompiledItems.origins, CompiledItem.origin] using
          tailNodup)).1
    let beforeDirect : ∀ occurrence, occurrence ∈ before.origins →
        occurrence ∈ localOccurrences host.val sourceCall.origin := by
      intro occurrence member
      exact sourceDirect occurrence (by
        rw [CompiledItems.origins_append]
        exact List.mem_append_left _ member)
    let suffixDirect : ∀ occurrence, occurrence ∈ suffix.origins →
        occurrence ∈ localOccurrences host.val sourceCall.origin := by
      intro occurrence member
      exact sourceDirect occurrence (by
        rw [CompiledItems.origins_append, CompiledItems.origins]
        exact List.mem_append_right _ (List.mem_cons_of_mem _ member))
    let beforeDifferent : ∀ child,
        LocalOccurrence.child child ∈ before.origins → child ≠ origin := by
      intro child member same
      subst child
      exact selectedNotBefore member
    let suffixDifferent : ∀ child,
        LocalOccurrence.child child ∈ suffix.origins → child ≠ origin := by
      intro child member same
      subst child
      exact selectedNotSuffix member
    let siblingOutside : ∀ sibling,
        (host.val.regions sibling).parent? = some sourceCall.origin →
          sibling ≠ origin →
          ¬ host.val.Encloses selection.val.anchor sibling := by
      intro sibling siblingParent different anchorEncloses
      have selectedEncloses := checked_encloses_trans host.property
        (by simpa only [siteEq] using childEncloses) anchorEncloses
      rcases encloses_direct_child siblingParent selectedEncloses with
        same | selectedParentEncloses
      · exact different same.symm
      · exact checked_direct_child_not_encloses_parent host.property
          sourceParent selectedParentEncloses
    let compileBlock := fun
        (block : CompiledItems host.val sourceCall.fullContext
          sourceCall.rels sourceCall.binders)
        (direct : ∀ occurrence, occurrence ∈ block.origins →
          occurrence ∈ localOccurrences host.val sourceCall.origin)
        (different : ∀ child,
          LocalOccurrence.child child ∈ block.origins → child ≠ origin)
        (compiled : compileItems? host.val host.property sourceCall.origin
          sourceCall.fullContext sourceCall.binders block.origins direct =
            some block) =>
      domains.compileAboveBlock host selection sourceCall.origin
        sourceCall.fullContext sourceCall.binders frame.originSurvives above
        parentAway childTargetOuter childOuterEq targetBinders frame.bindersEq
        frame.sourceExact frame.sourceCovers block direct
        (fun child member => sibling_not_encloses host sourceParent
          ((mem_localOccurrences_child host.val sourceCall.origin child).mp
            (direct (.child child) member)) (different child member)
          (by simpa only [siteEq] using childEncloses))
        (fun child member => siblingOutside child
          ((mem_localOccurrences_child host.val sourceCall.origin child).mp
            (direct (.child child) member)) (different child member)) compiled
    let beforeResult := Classical.choice
      (compileBlock before beforeDirect beforeDifferent beforeCompiled)
    let suffixResult := Classical.choice
      (compileBlock suffix suffixDirect suffixDifferent suffixCompiled)
    let targetBefore := beforeResult.1
    let targetSuffix := suffixResult.1
    have beforeTargetCompiled := beforeResult.2.1
    have suffixTargetCompiled := suffixResult.2.1
    have beforeIso := beforeResult.2.2
    have suffixIso := suffixResult.2.2
    let targetSelected : CompiledItem
        (host.val.removeRaw selection domains) childTargetOuter
          sourceCall.rels targetBinders := .cut childResult.targetBody
    have targetRegion : (host.val.removeRaw selection domains).regions
        (domains.regions.index origin childSurvives) =
          .cut (domains.regions.index sourceCall.origin
            frame.originSurvives) :=
      domains.removeRaw_cut host selection frame.originSurvives
        childSurvives sourceRegion
    have mappedSelectedEq : domains.indexOccurrence (.child origin) =
        .child (domains.regions.index origin childSurvives) := by
      apply domains.originOccurrence_injective
      rw [domains.originOccurrence_indexOccurrence (.child origin)
        childSurvives]
      exact congrArg LocalOccurrence.child
        (domains.regions.origin_index origin childSurvives).symm
    have selectedTargetDirect : LocalOccurrence.child
        (domains.regions.index origin childSurvives) ∈
          localOccurrences (host.val.removeRaw selection domains)
            (domains.regions.index sourceCall.origin frame.originSurvives) := by
      rw [domains.localOccurrences_removeRaw_eq_map_index host selection
        sourceCall.origin frame.originSurvives (fun occurrence member =>
          domains.localOccurrence_survives_above host selection
            sourceCall.origin above parentAway occurrence member)]
      exact List.mem_map.mpr ⟨.child origin, selectedDirect,
        mappedSelectedEq⟩
    have targetSelectedCompiled : compileOccurrence?
        (host.val.removeRaw selection domains)
        (Diagram.removeRaw_wellFormed host selection domains)
        (domains.regions.index sourceCall.origin frame.originSurvives)
        childTargetOuter targetBinders
        (.child (domains.regions.index origin childSurvives))
          selectedTargetDirect = some targetSelected := by
      rw [compileOccurrence?_child_cut
        (Diagram.removeRaw_wellFormed host selection domains)
        (domains.regions.index sourceCall.origin frame.originSurvives)
        (domains.regions.index origin childSurvives) childTargetOuter
        targetBinders selectedTargetDirect targetRegion]
      have childTargetCompiled : compileRegion?
          (host.val.removeRaw selection domains)
          (Diagram.removeRaw_wellFormed host selection domains)
          (domains.regions.index origin childSurvives) childTargetOuter
          targetBinders = some childResult.targetBody := by
        simpa [targetCall, childFrame] using childResult.targetCompiled
      rw [childTargetCompiled]
      rfl
    have beforeOrigins := compileItems?_origins
      (Diagram.removeRaw_wellFormed host selection domains)
      (domains.regions.index sourceCall.origin frame.originSurvives)
      childTargetOuter targetBinders beforeTargetCompiled
    have suffixOrigins := compileItems?_origins
      (Diagram.removeRaw_wellFormed host selection domains)
      (domains.regions.index sourceCall.origin frame.originSurvives)
      childTargetOuter targetBinders suffixTargetCompiled
    have selectedOrigin := compileOccurrence?_origin
      (Diagram.removeRaw_wellFormed host selection domains)
      (domains.regions.index sourceCall.origin frame.originSurvives)
      (.child (domains.regions.index origin childSurvives)) _
      targetSelectedCompiled
    have targetOrigins : (targetBefore.append
        (.cons targetSelected targetSuffix)).origins =
        localOccurrences (host.val.removeRaw selection domains)
          (domains.regions.index sourceCall.origin frame.originSurvives) := by
      rw [domains.localOccurrences_removeRaw_eq_map_index host selection
        sourceCall.origin frame.originSurvives (fun occurrence member =>
          domains.localOccurrence_survives_above host selection
            sourceCall.origin above parentAway occurrence member)]
      calc
        _ = (before.origins ++ .child origin :: suffix.origins).map
            domains.indexOccurrence := by
          dsimp only [targetBefore, targetSuffix]
          rw [CompiledItems.origins_append, CompiledItems.origins,
            beforeOrigins, suffixOrigins, selectedOrigin]
          simp only [List.map_append, List.map_cons, mappedSelectedEq]
          rfl
        _ = _ := by
          simpa [CompiledItems.origins_append, CompiledItems.origins,
            CompiledItem.origin] using
              congrArg (List.map domains.indexOccurrence) sourceOrigins
    have beforeCanonical : compileItems?
        (host.val.removeRaw selection domains)
        (Diagram.removeRaw_wellFormed host selection domains)
        (domains.regions.index sourceCall.origin frame.originSurvives)
        childTargetOuter targetBinders targetBefore.origins
        (fun occurrence member => by
          rw [← targetOrigins, CompiledItems.origins_append]
          exact List.mem_append_left _ member) = some targetBefore := by
      simpa only [targetBefore, beforeOrigins] using beforeTargetCompiled
    have suffixCanonical : compileItems?
        (host.val.removeRaw selection domains)
        (Diagram.removeRaw_wellFormed host selection domains)
        (domains.regions.index sourceCall.origin frame.originSurvives)
        childTargetOuter targetBinders targetSuffix.origins
        (fun occurrence member => by
          rw [← targetOrigins, CompiledItems.origins_append,
            CompiledItems.origins]
          exact List.mem_append_right _ (List.mem_cons_of_mem _ member)) =
        some targetSuffix := by
      simpa only [targetSuffix, suffixOrigins] using suffixTargetCompiled
    have selectedCanonical : compileOccurrence?
        (host.val.removeRaw selection domains)
        (Diagram.removeRaw_wellFormed host selection domains)
        (domains.regions.index sourceCall.origin frame.originSurvives)
        childTargetOuter targetBinders targetSelected.origin (by
          rw [← targetOrigins, CompiledItems.origins_append,
            CompiledItems.origins]
          exact List.mem_append_right _ List.mem_cons_self) =
        some targetSelected := by
      simpa only [selectedOrigin] using targetSelectedCompiled
    have beforeBack : ItemSeqIso childFrame.outerWire sourceCall.rels
        targetBefore.erase before.erase := by
      simpa [FrameEvidence.outerWire, childFrame, childOuterEq,
        targetBefore] using beforeIso.symm
    have suffixBack : ItemSeqIso childFrame.outerWire sourceCall.rels
        targetSuffix.erase suffix.erase := by
      simpa [FrameEvidence.outerWire, childFrame, childOuterEq,
        targetSuffix] using suffixIso.symm
    let blocks := compileFocusedItems
      (host.val.removeRaw selection domains)
      (Diagram.removeRaw_wellFormed host selection domains)
      (domains.regions.index sourceCall.origin frame.originSurvives)
      childTargetOuter targetBinders childFrame.outerWire before.erase
      suffix.erase (Item.cut body.erase) targetBefore targetSuffix
      targetSelected targetOrigins beforeCanonical suffixCanonical
      selectedCanonical beforeBack suffixBack
    let targetItems := targetBefore.append (.cons targetSelected targetSuffix)
    let targetBody := domains.targetBody sourceCall frame.originSurvives
      targetOuter targetLocal targetBinders frame.targetLocalCall targetItems
    have targetCompiled : (domains.targetCall sourceCall frame.originSurvives
        targetOuter targetLocal targetBinders).compile?
        (host.val.removeRaw selection domains)
          (Diagram.removeRaw_wellFormed host selection domains) =
        some targetBody :=
      domains.targetCall_compile_of_items host selection sourceCall
        frame.originSurvives targetOuter targetLocal targetBinders
        frame.targetLocalCall targetItems blocks.compiled
    let targetSplit : childTargetOuter.length =
        targetOuter.length + targetLocal.length := List.length_append
    let sourceSplit : sourceCall.fullContext.length =
        sourceCall.outerContext.length + sourceCall.localContext.length :=
      sourceCall.fullContext_length
    have fullWireAgreement : ∀ index,
        (childFrame.outerWire index).val =
          (extendWireEquiv frame.outerWire localWire
            (Fin.cast targetSplit index)).val := by
      intro index
      let split := Fin.cast targetSplit index
      have splitEq : Fin.cast targetSplit.symm split = index := by
        apply Fin.ext
        rfl
      rw [← splitEq]
      exact Fin.addCases
        (motive := fun position =>
          (childFrame.outerWire
            (Fin.cast targetSplit.symm position)).val =
          (extendWireEquiv frame.outerWire localWire
            (Fin.cast targetSplit
              (Fin.cast targetSplit.symm position))).val)
        (fun inherited => by
          simp [FrameEvidence.outerWire, localWire,
            FiniteEquiv.finCast, extendWireEquiv])
        (fun localIndex => by
          have outerLength : targetOuter.length =
              sourceCall.outerContext.length :=
            (congrArg List.length frame.outerEq).trans (by
              simpa using congrArg List.length
                (domains.mapWireContext_origin_eq
                  sourceCall.outerContext frame.outerSurvives))
          simp [FrameEvidence.outerWire, localWire,
            FiniteEquiv.finCast, extendWireEquiv]
          exact outerLength) split
    have childRebuild : childResult.targetContext.fill
        childResult.targetSite = childResult.targetBody.erase := by
      simpa only using childResult.targetRebuild
    have targetBodyEq : domains.targetErase sourceCall frame.originSurvives
        targetOuter targetLocal targetBinders targetBody =
          .mk targetLocal.length
            ((targetBefore.erase.append
              (.cons (.cut childResult.targetBody.erase)
                targetSuffix.erase)).castWiresEq targetSplit) := by
      rw [targetErase_targetBody]
      dsimp only [targetItems, targetSelected]
      rw [CompiledItems.erase_append]
      rfl
    let assembled := DiagramContextIso.cutCompilerFrameResult localWire
      sourceSplit targetSplit before.erase suffix.erase targetBefore.erase
      targetSuffix.erase nested.intrinsic.context childResult.targetContext
      childFrame.outerWire fullWireAgreement childResult.alignment blocks.frame
      childResult.targetSite childResult.targetBody.erase childRebuild
      (domains.targetErase sourceCall frame.originSurvives targetOuter
        targetLocal targetBinders targetBody) targetBodyEq
    exact ⟨{
      targetBody := targetBody
      targetCompiled := targetCompiled
      holeWires := childResult.holeWires
      holeWire := childResult.holeWire
      targetSite := childResult.targetSite
      targetContext := assembled.targetContext
      alignment := by
        simpa only [CompiledItemsZipper.intrinsic,
          CompiledZipper.intrinsic] using assembled.alignment
      targetRebuild := assembled.rebuild
    }⟩
  · intro sourceCall origin arity body before suffix items site endpointCall
      endpoint nested rebuild induction siteEq targetOuter targetLocal
      targetBinders frame
    subst items
    have sourceItemsCompiled := sourceCall.compile?_items_of_success
      host.property frame.sourceCompiled
    have sourceOrigins := compileItems?_origins host.property
      sourceCall.origin sourceCall.fullContext sourceCall.binders
      sourceItemsCompiled
    let sourceDirect : ∀ occurrence,
        occurrence ∈ (before.append (.cons (.bubble arity body) suffix)).origins →
          occurrence ∈ localOccurrences host.val sourceCall.origin := by
      intro occurrence member
      simpa only [sourceOrigins] using member
    have canonicalCompiled : compileItems? host.val host.property
        sourceCall.origin sourceCall.fullContext sourceCall.binders
        (before.append (.cons (.bubble arity body) suffix)).origins sourceDirect =
          some (before.append (.cons (.bubble arity body) suffix)) := by
      simpa only [sourceOrigins] using sourceItemsCompiled
    obtain ⟨beforeCompiled, selectedCompiled, suffixCompiled⟩ :=
      compileItems?_selected_inv host.property sourceCall.origin
        sourceCall.fullContext sourceCall.binders before (.bubble arity body)
        suffix sourceDirect canonicalCompiled
    let selectedDirect : LocalOccurrence.child origin ∈
        localOccurrences host.val sourceCall.origin :=
      sourceDirect (.child origin) (by
        simp [CompiledItems.origins_append, CompiledItems.origins,
          CompiledItem.origin])
    have selectedCompiled' : compileOccurrence? host.val host.property
        sourceCall.origin sourceCall.fullContext sourceCall.binders
        (.child origin) selectedDirect = some (.bubble arity body) := by
      simpa only [CompiledItem.origin] using selectedCompiled
    have sourceParent := (mem_localOccurrences_child host.val
      sourceCall.origin origin).mp selectedDirect
    have sourceRegion : host.val.regions origin =
        .bubble sourceCall.origin arity := by
      cases regionEq : host.val.regions origin with
      | sheet =>
          rw [compileOccurrence?_child_sheet host.property sourceCall.origin
            origin sourceCall.fullContext sourceCall.binders selectedDirect
            regionEq] at selectedCompiled'
          contradiction
      | cut parent =>
          have parentEq : parent = sourceCall.origin := by
            simpa [regionEq, CRegion.parent?] using sourceParent
          subst parent
          rw [compileOccurrence?_child_cut host.property sourceCall.origin
            origin sourceCall.fullContext sourceCall.binders selectedDirect
            regionEq] at selectedCompiled'
          cases childResult : compileRegion? host.val host.property origin
              sourceCall.fullContext sourceCall.binders <;>
            simp [childResult] at selectedCompiled'
      | bubble parent childArity =>
          have parentEq : parent = sourceCall.origin := by
            simpa [regionEq, CRegion.parent?] using sourceParent
          subst parent
          rw [compileOccurrence?_child_bubble host.property sourceCall.origin
            origin sourceCall.fullContext sourceCall.binders childArity
            selectedDirect regionEq] at selectedCompiled'
          cases childResult : compileRegion? host.val host.property origin
              sourceCall.fullContext
              (sourceCall.binders.push origin childArity) <;>
            simp [childResult] at selectedCompiled'
          rename_i childBody
          cases selectedCompiled'
          congr
    have childCompiled := compileOccurrence?_child_bubble_body host.property
      sourceCall.origin origin sourceCall.fullContext sourceCall.binders arity
      selectedDirect sourceRegion selectedCompiled'
    have childExact := frame.sourceExact.extend_child host.property sourceParent
    have childCovers := BinderContext.push_covers_bubble_child
      frame.sourceCovers sourceRegion
    have childEnumeration := frame.sourceEnumeration.bubbleChild host.property
      sourceRegion
    have childEncloses := nested.endpoint_encloses host.property childCompiled
      childExact childCovers childEnumeration
    have parentEnclosesChild : host.val.Encloses sourceCall.origin origin := by
      refine ⟨⟨1, by omega⟩, ?_⟩
      simp [Diagram.climb, sourceParent]
    have above : host.val.Encloses sourceCall.origin selection.val.anchor :=
      checked_encloses_trans host.property parentEnclosesChild
        (by simpa only [siteEq] using childEncloses)
    have parentAway : sourceCall.origin ≠ selection.val.anchor := by
      intro same
      rw [same] at sourceParent
      exact checked_direct_child_not_encloses_parent host.property sourceParent
        (by simpa only [siteEq] using childEncloses)
    have localSurvives : ∀ wire, wire ∈ sourceCall.localContext →
        domains.wires.survives wire = true := by
      intro wire member
      exact domains.visibleWire_survives_above host selection sourceCall.origin
        above parentAway sourceCall.fullContext frame.sourceExact wire
        (List.mem_append_right _ member)
    let localWire : FiniteEquiv (Fin targetLocal.length)
        (Fin sourceCall.localContext.length) :=
      (FiniteEquiv.finCast (congrArg List.length frame.localEq)).trans
        (domains.mapWireContextEquiv sourceCall.localContext localSurvives)
    let childTargetOuter := targetOuter ++ targetLocal
    let childTargetLocal := domains.mapWireContext
      (exactScopeWires host.val origin)
    let targetChild := domains.regions.index origin (by
      exact domains.localOccurrence_survives_above host selection
        sourceCall.origin above parentAway (.child origin) selectedDirect)
    have childSurvives : domains.regions.survives origin = true :=
      domains.localOccurrence_survives_above host selection sourceCall.origin
        above parentAway (.child origin) selectedDirect
    let childTargetBinders := targetBinders.push
      (domains.regions.index origin childSurvives) arity
    have childOuterEq : childTargetOuter =
        domains.mapWireContext sourceCall.fullContext := by
      dsimp only [childTargetOuter]
      rw [CompilerCall.fullContext, domains.mapWireContext_append,
        ← frame.outerEq, ← frame.localEq]
    have childLocalCall : exactScopeWires
        (host.val.removeRaw selection domains)
          (domains.regions.index origin childSurvives) = childTargetLocal := by
      dsimp only [childTargetLocal]
      rw [← domains.mapWireContext_exactScope host selection
        (domains.regions.index origin childSurvives),
        domains.regions.origin_index]
    have childOuterSurvives : ∀ wire, wire ∈ sourceCall.fullContext →
        domains.wires.survives wire = true := by
      intro wire member
      exact domains.visibleWire_survives_above host selection sourceCall.origin
        above parentAway sourceCall.fullContext frame.sourceExact wire member
    have childBindersEq : childTargetBinders =
        domains.mapBinderContext (sourceCall.binders.push origin arity) := by
      dsimp only [childTargetBinders]
      rw [frame.bindersEq]
      exact (domains.mapBinderContext_push sourceCall.binders origin
        childSurvives arity).symm
    let childFrame : FrameEvidence host selection domains
        (.nested origin sourceCall.fullContext (arity :: sourceCall.rels)
          (sourceCall.binders.push origin arity)) body childTargetOuter
          childTargetLocal childTargetBinders := {
      originSurvives := childSurvives
      outerEq := childOuterEq
      localEq := rfl
      outerSurvives := childOuterSurvives
      targetLocalCall := childLocalCall
      bindersEq := childBindersEq
      sourceExact := childExact
      sourceCovers := childCovers
      sourceEnumeration := childEnumeration
      sourceCompiled := childCompiled
    }
    obtain ⟨childResult⟩ := induction siteEq childTargetOuter
      childTargetLocal childTargetBinders childFrame
    have sourceNodup :
        (before.append (.cons (.bubble arity body) suffix)).origins.Nodup := by
      rw [sourceOrigins]
      exact localOccurrences_nodup host.val sourceCall.origin
    have beforeDisjointTail := (List.nodup_append.mp (by
      simpa only [CompiledItems.origins_append] using sourceNodup)).2.2
    have selectedNotBefore : LocalOccurrence.child origin ∉ before.origins := by
      intro member
      exact beforeDisjointTail _ member _ (by
        simp [CompiledItem.origin]) rfl
    have tailNodup :
        (CompiledItems.cons (.bubble arity body) suffix).origins.Nodup :=
      (List.nodup_append.mp (by
        simpa only [CompiledItems.origins_append] using sourceNodup)).2.1
    have selectedNotSuffix : LocalOccurrence.child origin ∉ suffix.origins :=
      (List.nodup_cons.mp (by
        simpa only [CompiledItems.origins, CompiledItem.origin] using
          tailNodup)).1
    let beforeDirect : ∀ occurrence, occurrence ∈ before.origins →
        occurrence ∈ localOccurrences host.val sourceCall.origin := by
      intro occurrence member
      exact sourceDirect occurrence (by
        rw [CompiledItems.origins_append]
        exact List.mem_append_left _ member)
    let suffixDirect : ∀ occurrence, occurrence ∈ suffix.origins →
        occurrence ∈ localOccurrences host.val sourceCall.origin := by
      intro occurrence member
      exact sourceDirect occurrence (by
        rw [CompiledItems.origins_append, CompiledItems.origins]
        exact List.mem_append_right _ (List.mem_cons_of_mem _ member))
    let beforeDifferent : ∀ child,
        LocalOccurrence.child child ∈ before.origins → child ≠ origin := by
      intro child member same
      subst child
      exact selectedNotBefore member
    let suffixDifferent : ∀ child,
        LocalOccurrence.child child ∈ suffix.origins → child ≠ origin := by
      intro child member same
      subst child
      exact selectedNotSuffix member
    let siblingOutside : ∀ sibling,
        (host.val.regions sibling).parent? = some sourceCall.origin →
          sibling ≠ origin →
          ¬ host.val.Encloses selection.val.anchor sibling := by
      intro sibling siblingParent different anchorEncloses
      have selectedEncloses := checked_encloses_trans host.property
        (by simpa only [siteEq] using childEncloses) anchorEncloses
      rcases encloses_direct_child siblingParent selectedEncloses with
        same | selectedParentEncloses
      · exact different same.symm
      · exact checked_direct_child_not_encloses_parent host.property
          sourceParent selectedParentEncloses
    let compileBlock := fun
        (block : CompiledItems host.val sourceCall.fullContext
          sourceCall.rels sourceCall.binders)
        (direct : ∀ occurrence, occurrence ∈ block.origins →
          occurrence ∈ localOccurrences host.val sourceCall.origin)
        (different : ∀ child,
          LocalOccurrence.child child ∈ block.origins → child ≠ origin)
        (compiled : compileItems? host.val host.property sourceCall.origin
          sourceCall.fullContext sourceCall.binders block.origins direct =
            some block) =>
      domains.compileAboveBlock host selection sourceCall.origin
        sourceCall.fullContext sourceCall.binders frame.originSurvives above
        parentAway childTargetOuter childOuterEq targetBinders frame.bindersEq
        frame.sourceExact frame.sourceCovers block direct
        (fun child member => sibling_not_encloses host sourceParent
          ((mem_localOccurrences_child host.val sourceCall.origin child).mp
            (direct (.child child) member)) (different child member)
          (by simpa only [siteEq] using childEncloses))
        (fun child member => siblingOutside child
          ((mem_localOccurrences_child host.val sourceCall.origin child).mp
            (direct (.child child) member)) (different child member)) compiled
    let beforeResult := Classical.choice
      (compileBlock before beforeDirect beforeDifferent beforeCompiled)
    let suffixResult := Classical.choice
      (compileBlock suffix suffixDirect suffixDifferent suffixCompiled)
    let targetBefore := beforeResult.1
    let targetSuffix := suffixResult.1
    have beforeTargetCompiled := beforeResult.2.1
    have suffixTargetCompiled := suffixResult.2.1
    have beforeIso := beforeResult.2.2
    have suffixIso := suffixResult.2.2
    let targetSelected : CompiledItem
        (host.val.removeRaw selection domains) childTargetOuter
          sourceCall.rels targetBinders := .bubble arity childResult.targetBody
    have targetRegion : (host.val.removeRaw selection domains).regions
        (domains.regions.index origin childSurvives) =
          .bubble (domains.regions.index sourceCall.origin
            frame.originSurvives) arity :=
      domains.removeRaw_bubble host selection frame.originSurvives
        childSurvives arity sourceRegion
    have mappedSelectedEq : domains.indexOccurrence (.child origin) =
        .child (domains.regions.index origin childSurvives) := by
      apply domains.originOccurrence_injective
      rw [domains.originOccurrence_indexOccurrence (.child origin)
        childSurvives]
      exact congrArg LocalOccurrence.child
        (domains.regions.origin_index origin childSurvives).symm
    have selectedTargetDirect : LocalOccurrence.child
        (domains.regions.index origin childSurvives) ∈
          localOccurrences (host.val.removeRaw selection domains)
            (domains.regions.index sourceCall.origin frame.originSurvives) := by
      rw [domains.localOccurrences_removeRaw_eq_map_index host selection
        sourceCall.origin frame.originSurvives (fun occurrence member =>
          domains.localOccurrence_survives_above host selection
            sourceCall.origin above parentAway occurrence member)]
      exact List.mem_map.mpr ⟨.child origin, selectedDirect,
        mappedSelectedEq⟩
    have targetSelectedCompiled : compileOccurrence?
        (host.val.removeRaw selection domains)
        (Diagram.removeRaw_wellFormed host selection domains)
        (domains.regions.index sourceCall.origin frame.originSurvives)
        childTargetOuter targetBinders
        (.child (domains.regions.index origin childSurvives))
          selectedTargetDirect = some targetSelected := by
      rw [compileOccurrence?_child_bubble
        (Diagram.removeRaw_wellFormed host selection domains)
        (domains.regions.index sourceCall.origin frame.originSurvives)
        (domains.regions.index origin childSurvives) childTargetOuter
        targetBinders arity selectedTargetDirect targetRegion]
      have childTargetCompiled : compileRegion?
          (host.val.removeRaw selection domains)
          (Diagram.removeRaw_wellFormed host selection domains)
          (domains.regions.index origin childSurvives) childTargetOuter
          childTargetBinders = some childResult.targetBody := by
        simpa [targetCall, childFrame] using childResult.targetCompiled
      rw [childTargetCompiled]
      rfl
    have beforeOrigins := compileItems?_origins
      (Diagram.removeRaw_wellFormed host selection domains)
      (domains.regions.index sourceCall.origin frame.originSurvives)
      childTargetOuter targetBinders beforeTargetCompiled
    have suffixOrigins := compileItems?_origins
      (Diagram.removeRaw_wellFormed host selection domains)
      (domains.regions.index sourceCall.origin frame.originSurvives)
      childTargetOuter targetBinders suffixTargetCompiled
    have selectedOrigin := compileOccurrence?_origin
      (Diagram.removeRaw_wellFormed host selection domains)
      (domains.regions.index sourceCall.origin frame.originSurvives)
      (.child (domains.regions.index origin childSurvives)) _
      targetSelectedCompiled
    have targetOrigins : (targetBefore.append
        (.cons targetSelected targetSuffix)).origins =
        localOccurrences (host.val.removeRaw selection domains)
          (domains.regions.index sourceCall.origin frame.originSurvives) := by
      rw [domains.localOccurrences_removeRaw_eq_map_index host selection
        sourceCall.origin frame.originSurvives (fun occurrence member =>
          domains.localOccurrence_survives_above host selection
            sourceCall.origin above parentAway occurrence member)]
      calc
        _ = (before.origins ++ .child origin :: suffix.origins).map
            domains.indexOccurrence := by
          dsimp only [targetBefore, targetSuffix]
          rw [CompiledItems.origins_append, CompiledItems.origins,
            beforeOrigins, suffixOrigins, selectedOrigin]
          simp only [List.map_append, List.map_cons, mappedSelectedEq]
          rfl
        _ = _ := by
          simpa [CompiledItems.origins_append, CompiledItems.origins,
            CompiledItem.origin] using
              congrArg (List.map domains.indexOccurrence) sourceOrigins
    have beforeCanonical : compileItems?
        (host.val.removeRaw selection domains)
        (Diagram.removeRaw_wellFormed host selection domains)
        (domains.regions.index sourceCall.origin frame.originSurvives)
        childTargetOuter targetBinders targetBefore.origins
        (fun occurrence member => by
          rw [← targetOrigins, CompiledItems.origins_append]
          exact List.mem_append_left _ member) = some targetBefore := by
      simpa only [targetBefore, beforeOrigins] using beforeTargetCompiled
    have suffixCanonical : compileItems?
        (host.val.removeRaw selection domains)
        (Diagram.removeRaw_wellFormed host selection domains)
        (domains.regions.index sourceCall.origin frame.originSurvives)
        childTargetOuter targetBinders targetSuffix.origins
        (fun occurrence member => by
          rw [← targetOrigins, CompiledItems.origins_append,
            CompiledItems.origins]
          exact List.mem_append_right _ (List.mem_cons_of_mem _ member)) =
        some targetSuffix := by
      simpa only [targetSuffix, suffixOrigins] using suffixTargetCompiled
    have selectedCanonical : compileOccurrence?
        (host.val.removeRaw selection domains)
        (Diagram.removeRaw_wellFormed host selection domains)
        (domains.regions.index sourceCall.origin frame.originSurvives)
        childTargetOuter targetBinders targetSelected.origin (by
          rw [← targetOrigins, CompiledItems.origins_append,
            CompiledItems.origins]
          exact List.mem_append_right _ List.mem_cons_self) =
        some targetSelected := by
      simpa only [selectedOrigin] using targetSelectedCompiled
    have beforeBack : ItemSeqIso childFrame.outerWire sourceCall.rels
        targetBefore.erase before.erase := by
      simpa [FrameEvidence.outerWire, childFrame, childOuterEq,
        targetBefore] using beforeIso.symm
    have suffixBack : ItemSeqIso childFrame.outerWire sourceCall.rels
        targetSuffix.erase suffix.erase := by
      simpa [FrameEvidence.outerWire, childFrame, childOuterEq,
        targetSuffix] using suffixIso.symm
    let blocks := compileFocusedItems
      (host.val.removeRaw selection domains)
      (Diagram.removeRaw_wellFormed host selection domains)
      (domains.regions.index sourceCall.origin frame.originSurvives)
      childTargetOuter targetBinders childFrame.outerWire before.erase
      suffix.erase (Item.bubble arity body.erase) targetBefore targetSuffix
      targetSelected targetOrigins beforeCanonical suffixCanonical
      selectedCanonical beforeBack suffixBack
    let targetItems := targetBefore.append (.cons targetSelected targetSuffix)
    let targetBody := domains.targetBody sourceCall frame.originSurvives
      targetOuter targetLocal targetBinders frame.targetLocalCall targetItems
    have targetCompiled : (domains.targetCall sourceCall frame.originSurvives
        targetOuter targetLocal targetBinders).compile?
        (host.val.removeRaw selection domains)
          (Diagram.removeRaw_wellFormed host selection domains) =
        some targetBody :=
      domains.targetCall_compile_of_items host selection sourceCall
        frame.originSurvives targetOuter targetLocal targetBinders
        frame.targetLocalCall targetItems blocks.compiled
    let targetSplit : childTargetOuter.length =
        targetOuter.length + targetLocal.length := List.length_append
    let sourceSplit : sourceCall.fullContext.length =
        sourceCall.outerContext.length + sourceCall.localContext.length :=
      sourceCall.fullContext_length
    have fullWireAgreement : ∀ index,
        (childFrame.outerWire index).val =
          (extendWireEquiv frame.outerWire localWire
            (Fin.cast targetSplit index)).val := by
      intro index
      let split := Fin.cast targetSplit index
      have splitEq : Fin.cast targetSplit.symm split = index := by
        apply Fin.ext
        rfl
      rw [← splitEq]
      exact Fin.addCases
        (motive := fun position =>
          (childFrame.outerWire
            (Fin.cast targetSplit.symm position)).val =
          (extendWireEquiv frame.outerWire localWire
            (Fin.cast targetSplit
              (Fin.cast targetSplit.symm position))).val)
        (fun inherited => by
          simp [FrameEvidence.outerWire, localWire,
            FiniteEquiv.finCast, extendWireEquiv])
        (fun localIndex => by
          have outerLength : targetOuter.length =
              sourceCall.outerContext.length :=
            (congrArg List.length frame.outerEq).trans (by
              simpa using congrArg List.length
                (domains.mapWireContext_origin_eq
                  sourceCall.outerContext frame.outerSurvives))
          simp [FrameEvidence.outerWire, localWire,
            FiniteEquiv.finCast, extendWireEquiv]
          exact outerLength) split
    have childRebuild : childResult.targetContext.fill
        childResult.targetSite = childResult.targetBody.erase := by
      simpa only using childResult.targetRebuild
    have targetBodyEq : domains.targetErase sourceCall frame.originSurvives
        targetOuter targetLocal targetBinders targetBody =
          .mk targetLocal.length
            ((targetBefore.erase.append
              (.cons (.bubble arity childResult.targetBody.erase)
                targetSuffix.erase)).castWiresEq targetSplit) := by
      rw [targetErase_targetBody]
      dsimp only [targetItems, targetSelected]
      rw [CompiledItems.erase_append]
      rfl
    let assembled := DiagramContextIso.bubbleCompilerFrameResult localWire
      sourceSplit targetSplit before.erase suffix.erase targetBefore.erase
      targetSuffix.erase nested.intrinsic.context childResult.targetContext
      childFrame.outerWire fullWireAgreement childResult.alignment blocks.frame
      childResult.targetSite childResult.targetBody.erase childRebuild
      (domains.targetErase sourceCall frame.originSurvives targetOuter
        targetLocal targetBinders targetBody) targetBodyEq
    exact ⟨{
      targetBody := targetBody
      targetCompiled := targetCompiled
      holeWires := childResult.holeWires
      holeWire := childResult.holeWire
      targetSite := childResult.targetSite
      targetContext := assembled.targetContext
      alignment := by
        simpa only [CompiledItemsZipper.intrinsic,
          CompiledZipper.intrinsic] using assembled.alignment
      targetRebuild := assembled.rebuild
    }⟩

/-- The compact removal frame at the checked root, retaining the selected
anchor as one unfilled aligned context. -/
structure FrameRootResult
    (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram)
    (domains : FrameDomains source.checked.val.diagram selection) where
  body : CompiledRegion (source.checked.val.diagram.removeRaw selection domains)
    (.root (domains.mapWireContext source.checked.val.exposedWires)
      (domains.mapWireContext source.checked.val.hiddenWires))
  compiled : compileRoot?
    (source.checked.val.diagram.removeRaw selection domains)
    (Diagram.removeRaw_wellFormed source.diagram selection domains)
    (domains.mapWireContext source.checked.val.exposedWires)
    (domains.mapWireContext source.checked.val.hiddenWires) = some body
  holeWires : Nat
  holeWire : FiniteEquiv (Fin holeWires)
    (Fin (CompiledSite.endpointCall source selection.val.anchor
      ).outerContext.length)
  targetSite : Region holeWires
    (CompiledSite.endpointCall source selection.val.anchor).rels
  targetContext : DiagramContext
    (domains.mapWireContext source.checked.val.exposedWires).length holeWires
    [] (CompiledSite.endpointCall source selection.val.anchor).rels
  externalWire : FiniteEquiv
    (Fin (domains.mapWireContext source.checked.val.exposedWires).length)
    (Fin source.checked.val.exposedWires.length)
  alignment : DiagramContextIso externalWire holeWire []
    (CompiledSite.endpointCall source selection.val.anchor).rels targetContext
    (CompiledSite.context source selection.val.anchor)
  rebuild : targetContext.fill targetSite = body.erase

theorem compileRootFrame
    (source : State arity)
    (selection : CheckedSelection source.checked.val.diagram)
    (domains : FrameDomains source.checked.val.diagram selection)
    (exposedSurvives : ∀ wire, wire ∈ source.checked.val.exposedWires →
      domains.wires.survives wire = true) :
    Nonempty (FrameRootResult source selection domains) := by
  let sourceCall : CompilerCall source.checked.val.diagram :=
    .root source.checked.val.exposedWires source.checked.val.hiddenWires
  let targetOuter := domains.mapWireContext source.checked.val.exposedWires
  let targetLocal := domains.mapWireContext source.checked.val.hiddenWires
  have sourceExact : sourceCall.fullContext.Exact
      source.checked.val.diagram.root := by
    simpa [sourceCall, CompilerCall.fullContext, OpenDiagram.rootWires] using
      openRootWires_exact source.checked.property
  let frame : FrameEvidence source.diagram selection domains
      sourceCall source.checked.compilation targetOuter targetLocal
      BinderContext.empty := {
    originSurvives := domains.root_survives
    outerEq := rfl
    localEq := rfl
    outerSurvives := exposedSurvives
    targetLocalCall := rfl
    bindersEq := by
      exact domains.mapBinderContext_empty.symm
    sourceExact := sourceExact
    sourceCovers := by
      simpa [sourceCall] using BinderContext.empty_covers_root
        source.checked.property.diagram_well_formed
    sourceEnumeration := by
      simpa [sourceCall] using BinderContext.Enumeration.empty
        source.checked.val.diagram
    sourceCompiled := by
      simpa [sourceCall] using source.checked.compilation_computation
  }
  obtain ⟨result⟩ := domains.compileAlongFocus source.diagram
    selection (CompiledSite.zipper source selection.val.anchor) rfl
    targetOuter targetLocal BinderContext.empty frame
  refine ⟨{
    body := result.targetBody
    compiled := ?_
    holeWires := result.holeWires
    holeWire := result.holeWire
    targetSite := result.targetSite
    targetContext := result.targetContext
    externalWire := frame.outerWire
    alignment := result.alignment
    rebuild := ?_
  }⟩
  · simpa [sourceCall, targetOuter, targetLocal, targetCall, frame] using
      result.targetCompiled
  · simpa [sourceCall, targetOuter, targetLocal, targetErase, frame] using
      result.targetRebuild

end FrameDomains

end VisualProof.Concrete
