import VisualProof.Concrete.Elaboration.SpliceSiteCompilation

/-! Lift the splice endpoint through the canonical source compiler zipper. -/

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

private noncomputable def awayLocalWire
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (parent : Fin input.frame.val.regionCount)
    (away : parent ≠ input.site) :
    FiniteEquiv
      (Fin (exactScopeWires layout.plugRaw
        (layout.frameRegion parent)).length)
      (Fin (exactScopeWires input.frame.val parent).length) := by
  have localEq : exactScopeWires layout.plugRaw
      (layout.frameRegion parent) =
        (exactScopeWires input.frame.val parent).map layout.frameWireMap := by
    rw [layout.exactScopeWires_frameRegion consistent terminal parent,
      if_neg away, List.append_nil]
    rfl
  exact FiniteEquiv.finCast
    ((congrArg List.length localEq).trans
      (List.length_map layout.frameWireMap))

private theorem awayLocalWire_get
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (parent : Fin input.frame.val.regionCount)
    (away : parent ≠ input.site)
    (index : Fin (exactScopeWires input.frame.val parent).length) :
    (exactScopeWires layout.plugRaw (layout.frameRegion parent)).get
        ((layout.awayLocalWire consistent terminal parent away).symm index) =
      layout.frameWireMap
        ((exactScopeWires input.frame.val parent).get index) := by
  have localEq : exactScopeWires layout.plugRaw
      (layout.frameRegion parent) =
        (exactScopeWires input.frame.val parent).map layout.frameWireMap := by
    rw [layout.exactScopeWires_frameRegion consistent terminal parent,
      if_neg away, List.append_nil]
    rfl
  rw [List.get_of_eq localEq]
  change ((exactScopeWires input.frame.val parent).map
      layout.frameWireMap).get
        (Fin.cast (List.length_map layout.frameWireMap).symm index) = _
  exact List.getElem_map layout.frameWireMap

private theorem canonicalOuterWire_get
    (layout : PlugLayout input) (sourceCall : CompilerCall input.frame.val)
    (targetOuter : WireContext layout.plugRaw)
    (outerEq : targetOuter =
      sourceCall.outerContext.map layout.frameWireMap)
    (index : Fin sourceCall.outerContext.length) :
    targetOuter.get
        ((layout.canonicalOuterWire sourceCall targetOuter outerEq).symm index) =
      layout.frameWireMap (sourceCall.outerContext.get index) := by
  rw [List.get_of_eq outerEq]
  exact List.getElem_map layout.frameWireMap

private noncomputable def mappedLocalWire
    (layout : PlugLayout input) (sourceCall : CompilerCall input.frame.val)
    (targetLocal : WireContext layout.plugRaw)
    (localEq : targetLocal =
      sourceCall.localContext.map layout.frameWireMap) :
    FiniteEquiv (Fin targetLocal.length)
      (Fin sourceCall.localContext.length) :=
  FiniteEquiv.finCast ((congrArg List.length localEq).trans
    (List.length_map layout.frameWireMap))

private noncomputable def mappedFullWire
    (layout : PlugLayout input) (sourceCall : CompilerCall input.frame.val)
    (targetOuter targetLocal : WireContext layout.plugRaw)
    (outerEq : targetOuter =
      sourceCall.outerContext.map layout.frameWireMap)
    (localEq : targetLocal =
      sourceCall.localContext.map layout.frameWireMap) :
    FiniteEquiv (Fin (targetOuter ++ targetLocal).length)
      (Fin sourceCall.fullContext.length) :=
  castFinEquiv (by exact List.length_append)
    sourceCall.fullContext_length
    (extendWireEquiv
      (layout.canonicalOuterWire sourceCall targetOuter outerEq)
      (layout.mappedLocalWire sourceCall targetLocal localEq))

private theorem mappedLocalWire_get
    (layout : PlugLayout input) (sourceCall : CompilerCall input.frame.val)
    (targetLocal : WireContext layout.plugRaw)
    (localEq : targetLocal =
      sourceCall.localContext.map layout.frameWireMap)
    (index : Fin sourceCall.localContext.length) :
    targetLocal.get
        ((layout.mappedLocalWire sourceCall targetLocal localEq).symm index) =
      layout.frameWireMap (sourceCall.localContext.get index) := by
  rw [List.get_of_eq localEq]
  exact List.getElem_map layout.frameWireMap

private theorem mappedFullWire_get
    (layout : PlugLayout input) (sourceCall : CompilerCall input.frame.val)
    (targetOuter targetLocal : WireContext layout.plugRaw)
    (outerEq : targetOuter =
      sourceCall.outerContext.map layout.frameWireMap)
    (localEq : targetLocal =
      sourceCall.localContext.map layout.frameWireMap)
    (index : Fin sourceCall.fullContext.length) :
    (targetOuter ++ targetLocal).get
        ((layout.mappedFullWire sourceCall targetOuter targetLocal outerEq
          localEq).symm index) =
      layout.frameWireMap (sourceCall.fullContext.get index) := by
  let split := Fin.cast sourceCall.fullContext_length index
  have indexEq : Fin.cast sourceCall.fullContext_length.symm split = index := by
    apply Fin.ext
    rfl
  rw [← indexEq]
  exact Fin.addCases (motive := fun position =>
      (targetOuter ++ targetLocal).get
          ((layout.mappedFullWire sourceCall targetOuter targetLocal outerEq
            localEq).symm
            (Fin.cast sourceCall.fullContext_length.symm position)) =
        layout.frameWireMap (sourceCall.fullContext.get
          (Fin.cast sourceCall.fullContext_length.symm position)))
    (fun inherited => by
      simpa [mappedFullWire, mappedLocalWire, canonicalOuterWire,
        castFinEquiv, extendWireEquiv, CompilerCall.fullContext] using
          layout.canonicalOuterWire_get sourceCall targetOuter outerEq inherited)
    (fun localIndex => by
      simpa [mappedFullWire, mappedLocalWire, canonicalOuterWire,
        castFinEquiv, extendWireEquiv, CompilerCall.fullContext] using
          layout.mappedLocalWire_get sourceCall targetLocal localEq
            localIndex) split

private noncomputable def endpointAfter
    (input : Splice.Input)
    (sourceCall : CompilerCall input.frame.val)
    (sourceBody : CompiledRegion input.frame.val sourceCall)
    (materialWireMap : Fin (CompiledSite.endpointCall
      (State.ofOpen input.pattern) input.binderSpine.bodyContainer
        ).outerContext.length → Fin sourceCall.fullContext.length)
    (relationMap : RelationRenaming
      (CompiledSite.endpointCall (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).rels sourceCall.rels) :
    Region sourceCall.outerContext.length sourceCall.rels :=
  match sourceBody with
  | .mk items =>
      Region.spliceAt sourceCall.localContext.length
        (items.erase.castWiresEq sourceCall.fullContext_length)
        (CompiledSite.body (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer)
        (fun wire => Fin.cast sourceCall.fullContext_length
          (materialWireMap wire)) relationMap

/-- One result for every compiler call. The target body is indexed by the
actual target call, while the aligned context keeps the endpoint unfilled.
The endpoint isomorphism is filled only once by the root theorem. -/
private structure GraftResult
    (layout : PlugLayout input) (targetWf : layout.plugRaw.WellFormed)
    {sourceCall endpointCall : CompilerCall input.frame.val}
    {sourceBody : CompiledRegion input.frame.val sourceCall}
    {endpoint : CompiledRegion input.frame.val endpointCall}
    (targetOuter targetLocal : WireContext layout.plugRaw)
    (targetBinders : BinderContext layout.plugRaw sourceCall.rels)
    (outerEq : targetOuter =
      sourceCall.outerContext.map layout.frameWireMap)
    (site : Fin input.frame.val.regionCount)
    (focus : CompiledZipper input.frame.val sourceBody site
      endpointCall endpoint)
    (after : Region endpointCall.outerContext.length endpointCall.rels) where
  targetBody : CompiledRegion layout.plugRaw
    (layout.frameTargetCall sourceCall targetOuter targetLocal targetBinders)
  targetCompiled : (layout.frameTargetCall sourceCall targetOuter targetLocal
    targetBinders).compile? layout.plugRaw targetWf = some targetBody
  holeWires : Nat
  holeWire : FiniteEquiv (Fin holeWires)
    (Fin endpointCall.outerContext.length)
  targetSite : Region holeWires endpointCall.rels
  targetContext : DiagramContext targetOuter.length holeWires
    sourceCall.rels endpointCall.rels
  alignment : DiagramContextIso
    (layout.canonicalOuterWire sourceCall targetOuter outerEq) holeWire
    sourceCall.rels endpointCall.rels targetContext focus.intrinsic.context
  targetRebuild : targetContext.fill targetSite =
    layout.frameTargetErase sourceCall targetOuter targetLocal targetBinders
      targetBody
  endpointIso : RegionIso holeWire endpointCall.rels targetSite after

private structure AwayBlockResult
    (layout : PlugLayout input) (targetWf : layout.plugRaw.WellFormed)
    {sourceCall : CompilerCall input.frame.val}
    (targetOuter targetLocal : WireContext layout.plugRaw)
    (targetBinders : BinderContext layout.plugRaw sourceCall.rels)
    (outerEq : targetOuter =
      sourceCall.outerContext.map layout.frameWireMap)
    (localEq : targetLocal =
      sourceCall.localContext.map layout.frameWireMap)
    (parentAway : sourceCall.origin ≠ input.site)
    (source : CompiledItems input.frame.val sourceCall.fullContext
      sourceCall.rels sourceCall.binders) where
  sourceDirect : ∀ occurrence, occurrence ∈ source.origins →
    occurrence ∈ localOccurrences input.frame.val sourceCall.origin
  target : CompiledItems layout.plugRaw (targetOuter ++ targetLocal)
    sourceCall.rels targetBinders
  compiled : compileItems? layout.plugRaw targetWf
    (layout.frameRegion sourceCall.origin) (targetOuter ++ targetLocal)
    targetBinders (source.origins.map layout.mapFrameOccurrence)
    (fun occurrence member => by
      rw [layout.localOccurrences_frameRegion_of_ne_site sourceCall.origin
        parentAway]
      obtain ⟨sourceOccurrence, sourceMember, rfl⟩ := List.mem_map.mp member
      exact List.mem_map.mpr
        ⟨sourceOccurrence, sourceDirect _ sourceMember, rfl⟩) = some target
  iso : ItemSeqIso
    (layout.mappedFullWire sourceCall targetOuter targetLocal outerEq localEq)
    sourceCall.rels target.erase source.erase

private noncomputable def compileAwayBlock
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody) (targetWf : layout.plugRaw.WellFormed)
    (sourceCall : CompilerCall input.frame.val)
    (targetOuter targetLocal : WireContext layout.plugRaw)
    (targetBinders : BinderContext layout.plugRaw sourceCall.rels)
    (outerEq : targetOuter =
      sourceCall.outerContext.map layout.frameWireMap)
    (localEq : targetLocal =
      sourceCall.localContext.map layout.frameWireMap)
    (parentAway : sourceCall.origin ≠ input.site)
    (sourceExact : sourceCall.fullContext.Exact sourceCall.origin)
    (targetExact : (targetOuter ++ targetLocal).Exact
      (layout.frameRegion sourceCall.origin))
    (frameBindersMapped : ∀ binder,
      targetBinders (layout.frameRegion binder) = sourceCall.binders binder)
    (selected : Fin input.frame.val.regionCount)
    (selectedParent : (input.frame.val.regions selected).parent? =
      some sourceCall.origin)
    (selectedEncloses : input.frame.val.Encloses selected input.site)
    (source : CompiledItems input.frame.val sourceCall.fullContext
      sourceCall.rels sourceCall.binders)
    (sourceDirect : ∀ occurrence, occurrence ∈ source.origins →
      occurrence ∈ localOccurrences input.frame.val sourceCall.origin)
    (different : ∀ child,
      LocalOccurrence.child child ∈ source.origins → child ≠ selected)
    (sourceCompiled : compileItems? input.frame.val input.frame.property
      sourceCall.origin sourceCall.fullContext sourceCall.binders
      source.origins sourceDirect = some source) :
    AwayBlockResult layout targetWf targetOuter targetLocal targetBinders
      outerEq localEq parentAway source := by
  let fullWire := layout.mappedFullWire sourceCall targetOuter targetLocal
    outerEq localEq
  have binderMapped : ∀ binder,
      targetBinders (layout.frameRegion binder) =
        (sourceCall.binders binder).map fun relation =>
          ⟨relation.1, relation.2⟩ := by
    intro binder
    rw [frameBindersMapped]
    cases sourceCall.binders binder <;> rfl
  let childrenAway : ∀ child,
      LocalOccurrence.child child ∈ source.origins →
        ¬ input.frame.val.Encloses child input.site := by
    intro child member
    have childParent := (mem_localOccurrences_child input.frame.val
      sourceCall.origin child).mp (sourceDirect _ member)
    exact sibling_not_encloses input.frame.property selectedParent childParent
      (different child member) selectedEncloses
  have existsTarget := layout.compileFrameItemsAway consistent terminal targetWf
      sourceCall.origin parentAway sourceCall.fullContext
      (targetOuter ++ targetLocal) sourceCall.binders targetBinders
      fullWire.symm (fun relation => relation) sourceExact targetExact
      (layout.mappedFullWire_get sourceCall targetOuter targetLocal outerEq
        localEq) binderMapped sourceDirect childrenAway sourceCompiled
  let target := Classical.choose existsTarget
  have targetSpec := Classical.choose_spec existsTarget
  refine {
    sourceDirect := sourceDirect
    target := target
    compiled := ?_
    iso := ?_
  }
  · exact targetSpec.1
  · have erased' : target.erase = source.erase.renameWires fullWire.symm := by
      simpa only [target, ItemSeq.renameRelations_id] using targetSpec.2
    rw [erased']
    exact (ItemSeqIso.renameWiresEquiv source.erase fullWire.symm).symm

private noncomputable def compileHere
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (admissible : input.Admissible)
    (targetWf : layout.plugRaw.WellFormed)
    (sourceCall : CompilerCall input.frame.val)
    (sourceBody : CompiledRegion input.frame.val sourceCall)
    (targetOuter targetLocal : WireContext layout.plugRaw)
    (targetBinders : BinderContext layout.plugRaw sourceCall.rels)
    (atSite : sourceCall.origin = input.site)
    (outerEq : targetOuter =
      sourceCall.outerContext.map layout.frameWireMap)
    (targetLocalCall :
      (layout.frameTargetCall sourceCall targetOuter targetLocal
        targetBinders).localContext = targetLocal)
    (targetFullEq : targetOuter ++ targetLocal =
      sourceCall.fullContext.map layout.frameWireMap ++
        (CompiledSite.endpointCall (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).localContext.map
            layout.patternWireMap)
    (sourceExact : sourceCall.fullContext.Exact input.site)
    (targetExact : (targetOuter ++ targetLocal).Exact
      (layout.frameRegion input.site))
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
        ).outerContext.length → Fin sourceCall.fullContext.length)
    (materialGet : ∀ index,
      sourceCall.fullContext.get (materialWireMap index) =
        input.attachment (layout.exposedPosition
          (Fin.cast (congrArg List.length (patternTerminal_outerContext input
            admissible.terminal_body)) index)))
    (sourceCompiled : sourceCall.compile? input.frame.val
      input.frame.property = some sourceBody)
    (after : Region sourceCall.outerContext.length sourceCall.rels)
    (afterEq : after = endpointAfter input sourceCall sourceBody
      materialWireMap relationMap) :
    GraftResult layout targetWf targetOuter targetLocal targetBinders outerEq
      sourceCall.origin (CompiledZipper.here sourceBody) after := by
  cases sourceCall with
  | root sourceOuter sourceLocal =>
      change input.frame.val.root = input.site at atSite
      have targetBindersEq : targetBinders = BinderContext.empty := by
        funext binder
        cases lookup : targetBinders binder with
        | none => rfl
        | some value =>
            obtain ⟨arity, relation⟩ := value
            exact Fin.elim0 relation.index
      subst targetBinders
      change targetLocal = targetLocal at targetLocalCall
      have targetEq : (layout.frameTargetCall
          (.root sourceOuter sourceLocal) targetOuter targetLocal
            BinderContext.empty).fullContext =
          (sourceOuter ++ sourceLocal).map layout.frameWireMap ++
            (CompiledSite.endpointCall (State.ofOpen input.pattern)
              input.binderSpine.bodyContainer).localContext.map
                layout.patternWireMap := by
        simpa [frameTargetCall, CompilerCall.fullContext] using targetFullEq
      cases sourceBody
      rename_i sourceItems
      have semantic := layout.compileSpliceSite
          (terminal := admissible.terminal_body) consistent admissible targetWf
          (.root sourceOuter sourceLocal) targetOuter targetLocal
          BinderContext.empty
          atSite outerEq targetEq sourceExact frameBindersMapped relationMap
          hostLookup materialWireMap materialGet sourceCompiled
      dsimp only [SpliceSiteSemantic] at semantic
      obtain ⟨targetBody, targetCompiled, endpointIso⟩ :=
        Classical.choice semantic
      refine {
        targetBody := targetBody
        targetCompiled := targetCompiled
        holeWires := targetOuter.length
        holeWire := layout.canonicalOuterWire
          (.root sourceOuter sourceLocal) targetOuter outerEq
        targetSite := targetBody.erase
        targetContext := .hole
        alignment := .hole _
        targetRebuild := rfl
        endpointIso := ?_
      }
      rw [afterEq]
      simpa [endpointAfter, CompilerCall.localContext] using endpointIso

  | nested origin sourceOuter sourceRels sourceBinders =>
      change origin = input.site at atSite
      change exactScopeWires layout.plugRaw (layout.frameRegion origin) =
        targetLocal at targetLocalCall
      subst targetLocal
      have targetEq : (layout.frameTargetCall
          (.nested origin sourceOuter sourceRels sourceBinders) targetOuter
            (exactScopeWires layout.plugRaw (layout.frameRegion origin))
              targetBinders).fullContext =
          (sourceOuter ++ exactScopeWires input.frame.val origin).map
              layout.frameWireMap ++
            (CompiledSite.endpointCall (State.ofOpen input.pattern)
              input.binderSpine.bodyContainer).localContext.map
                layout.patternWireMap := by
        simpa [frameTargetCall, CompilerCall.fullContext] using targetFullEq
      cases sourceBody
      rename_i sourceItems
      have semantic := layout.compileSpliceSite
          (terminal := admissible.terminal_body) consistent admissible targetWf
          (.nested origin sourceOuter sourceRels sourceBinders) targetOuter
          (exactScopeWires layout.plugRaw (layout.frameRegion origin))
          targetBinders atSite outerEq targetEq sourceExact frameBindersMapped
          relationMap hostLookup materialWireMap materialGet sourceCompiled
      dsimp only [SpliceSiteSemantic] at semantic
      obtain ⟨targetBody, targetCompiled, endpointIso⟩ :=
        Classical.choice semantic
      refine {
        targetBody := targetBody
        targetCompiled := targetCompiled
        holeWires := targetOuter.length
        holeWire := layout.canonicalOuterWire
          (.nested origin sourceOuter sourceRels sourceBinders)
            targetOuter outerEq
        targetSite := targetBody.erase
        targetContext := .hole
        alignment := .hole _
        targetRebuild := rfl
        endpointIso := ?_
      }
      rw [afterEq]
      simpa [endpointAfter, CompilerCall.localContext] using endpointIso

end Splice.Input.PlugLayout

end VisualProof.Concrete
