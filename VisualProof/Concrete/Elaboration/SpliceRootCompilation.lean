import VisualProof.Concrete.Elaboration.SpliceSiteCompilation
import VisualProof.Concrete.Operation.Structural.Flat
import VisualProof.Diagram.Replacement

/-! Lift the splice endpoint through the canonical source compiler zipper. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Diagram
open Theory
open Elaboration

namespace Splice.Input.PlugLayout

@[simp] private theorem fin_cast_self
    (equality : count = count) (index : Fin count) :
    Fin.cast equality index = index := by
  have equalityRefl : equality = rfl := Subsingleton.elim _ _
  rw [equalityRefl]
  rfl

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

private theorem canonicalOuterWire_boundaryClass
    (layout : PlugLayout input)
    (boundary : List (Fin input.frame.val.wireCount))
    (hidden : WireContext input.frame.val)
    (outerEq : (layout.outputOpenRoot input boundary).exposedWires =
      (frameOpen input boundary).exposedWires.map layout.frameWireMap)
    (position : Fin boundary.length) :
    layout.canonicalOuterWire
        (.root (frameOpen input boundary).exposedWires hidden)
        (layout.outputOpenRoot input boundary).exposedWires outerEq
        ((layout.outputOpenRoot input boundary).boundaryClass
          (Fin.cast (List.length_map
            (layout.frameWire ∘ input.quotientWire)).symm position)) =
      (frameOpen input boundary).boundaryClass position := by
  let sourceOpen := frameOpen input boundary
  let targetOpen := layout.outputOpenRoot input boundary
  let sourceCall : CompilerCall input.frame.val :=
    .root sourceOpen.exposedWires hidden
  let wire := layout.canonicalOuterWire sourceCall targetOpen.exposedWires
    outerEq
  let targetPosition : Fin targetOpen.boundary.length :=
    Fin.cast (List.length_map
      (layout.frameWire ∘ input.quotientWire)).symm position
  have candidateEq :
      wire.symm (sourceOpen.boundaryClass position) =
        targetOpen.boundaryClass targetPosition := by
    apply targetOpen.boundaryClass_complete
    have mapped := layout.canonicalOuterWire_get sourceCall
      targetOpen.exposedWires outerEq (sourceOpen.boundaryClass position)
    change targetOpen.exposedWires.get
      (wire.symm (sourceOpen.boundaryClass position)) = _ at mapped
    rw [mapped]
    change layout.frameWireMap
      (sourceOpen.exposedWires.get (sourceOpen.boundaryClass position)) = _
    rw [sourceOpen.boundaryClass_sound position]
    simp [sourceOpen, targetOpen, targetPosition,
      frameOpen, PlugLayout.outputOpenRoot,
      PlugLayout.frameWireMap, Function.comp_def]
  calc
    wire (targetOpen.boundaryClass targetPosition) =
        wire (wire.symm (sourceOpen.boundaryClass position)) :=
      congrArg wire candidateEq.symm
    _ = sourceOpen.boundaryClass position := wire.apply_symm_apply _

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

noncomputable def spliceEndpointAfter
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
  Region.spliceAt sourceCall.localContext.length
    (sourceCall.castFullItems sourceBody.items.erase)
    (CompiledSite.body (State.ofOpen input.pattern)
      input.binderSpine.bodyContainer)
    (fun wire => Fin.cast sourceCall.fullContext_length
      (materialWireMap wire)) relationMap

theorem spliceEndpointAfter_eq
    (input : Splice.Input)
    (sourceCall : CompilerCall input.frame.val)
    (sourceBody : CompiledRegion input.frame.val sourceCall)
    (materialWireMap : Fin (CompiledSite.endpointCall
      (State.ofOpen input.pattern) input.binderSpine.bodyContainer
        ).outerContext.length → Fin sourceCall.fullContext.length)
    (relationMap : RelationRenaming
      (CompiledSite.endpointCall (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).rels sourceCall.rels) :
    spliceEndpointAfter input sourceCall sourceBody materialWireMap relationMap =
      Region.spliceAt sourceCall.localContext.length
        (sourceCall.castFullItems sourceBody.items.erase)
        (CompiledSite.body (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer)
        (fun wire => Fin.cast sourceCall.fullContext_length
          (materialWireMap wire)) relationMap := by
  rfl

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

private structure FrameEvidence
    (layout : PlugLayout input) (targetWf : layout.plugRaw.WellFormed)
    (sourceCall : CompilerCall input.frame.val)
    (targetOuter targetLocal : WireContext layout.plugRaw)
    (targetBinders : BinderContext layout.plugRaw sourceCall.rels)
    (sourceBody : CompiledRegion input.frame.val sourceCall) where
  outerEq : targetOuter =
    sourceCall.outerContext.map layout.frameWireMap
  fullEq : targetOuter ++ targetLocal =
    sourceCall.fullContext.map layout.frameWireMap ++
      (if sourceCall.origin = input.site then
        (CompiledSite.endpointCall (State.ofOpen input.pattern)
          input.binderSpine.bodyContainer).localContext.map
            layout.patternWireMap
      else [])
  targetLocalCall : (layout.frameTargetCall sourceCall targetOuter targetLocal
    targetBinders).localContext = targetLocal
  sourceExact : sourceCall.fullContext.Exact sourceCall.origin
  sourceCovers : sourceCall.binders.Covers sourceCall.origin
  sourceEnumeration : BinderContext.Enumeration input.frame.val
    sourceCall.binders sourceCall.origin
  targetExact : (targetOuter ++ targetLocal).Exact
    (layout.frameRegion sourceCall.origin)
  frameBindersMapped : ∀ binder,
    targetBinders (layout.frameRegion binder) = sourceCall.binders binder
  sourceCompiled : sourceCall.compile? input.frame.val input.frame.property =
    some sourceBody

private structure EndpointGraftInput
    (layout : PlugLayout input) (admissible : input.Admissible)
    (endpointCall : CompilerCall input.frame.val)
    (endpoint : CompiledRegion input.frame.val endpointCall) where
  relationMap : RelationRenaming
    (CompiledSite.endpointCall (State.ofOpen input.pattern)
      input.binderSpine.bodyContainer).rels endpointCall.rels
  hostLookup : ∀ {arity} (relation : RelVar
    (CompiledSite.endpointCall (State.ofOpen input.pattern)
      input.binderSpine.bodyContainer).rels arity),
    endpointCall.binders (input.binderTarget
      (terminalRelationProxyEquiv input relation.index)) =
        some ⟨arity, relationMap relation⟩
  materialWireMap : Fin (CompiledSite.endpointCall
    (State.ofOpen input.pattern) input.binderSpine.bodyContainer
      ).outerContext.length → Fin endpointCall.fullContext.length
  materialGet : ∀ index,
    endpointCall.fullContext.get (materialWireMap index) =
      input.attachment (layout.exposedPosition
        (Fin.cast (congrArg List.length (patternTerminal_outerContext input
          admissible.terminal_body)) index))
  after : Region endpointCall.outerContext.length endpointCall.rels
  afterEq : after = spliceEndpointAfter input endpointCall endpoint materialWireMap
    relationMap

structure AwayBlockResult
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

noncomputable def compileAwayBlock
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
    (afterEq : after = spliceEndpointAfter input sourceCall sourceBody
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
      simpa [spliceEndpointAfter, CompilerCall.localContext] using endpointIso

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
      simpa [spliceEndpointAfter, CompilerCall.localContext] using endpointIso

/-- Compile one focused parent sequence after its two sibling blocks have been
transported. The distinguished item is deliberately absent from `frame`;
cut/bubble callers supply its replacement isomorphism only when they build the
enclosing `DiagramContextIso`. -/
private structure FocusedBlocksResult
    (layout : PlugLayout input) (targetWf : layout.plugRaw.WellFormed)
    {sourceCall : CompilerCall input.frame.val}
    (targetOuter targetLocal : WireContext layout.plugRaw)
    (targetBinders : BinderContext layout.plugRaw sourceCall.rels)
    (outerEq : targetOuter =
      sourceCall.outerContext.map layout.frameWireMap)
    (localEq : targetLocal =
      sourceCall.localContext.map layout.frameWireMap)
    (sourceBefore sourceSuffix : CompiledItems input.frame.val
      sourceCall.fullContext sourceCall.rels sourceCall.binders)
    (sourceSelected : Item sourceCall.fullContext.length sourceCall.rels)
    (targetSelected : CompiledItem layout.plugRaw (targetOuter ++ targetLocal)
      sourceCall.rels targetBinders) where
  targetBefore : CompiledItems layout.plugRaw (targetOuter ++ targetLocal)
    sourceCall.rels targetBinders
  targetSuffix : CompiledItems layout.plugRaw (targetOuter ++ targetLocal)
    sourceCall.rels targetBinders
  compiled : compileItems? layout.plugRaw targetWf
    (layout.frameRegion sourceCall.origin) (targetOuter ++ targetLocal)
    targetBinders (localOccurrences layout.plugRaw
      (layout.frameRegion sourceCall.origin)) (fun _ member => member) =
      some (targetBefore.append (.cons targetSelected targetSuffix))
  frame : ∀ {targetReplacement : Item (targetOuter ++ targetLocal).length
      sourceCall.rels}
      {sourceReplacement : Item sourceCall.fullContext.length sourceCall.rels},
    ItemIso (layout.mappedFullWire sourceCall targetOuter targetLocal outerEq
      localEq) sourceCall.rels targetReplacement sourceReplacement →
      ItemSeqIso (layout.mappedFullWire sourceCall targetOuter targetLocal
        outerEq localEq) sourceCall.rels
        (targetBefore.erase.append (.cons targetReplacement targetSuffix.erase))
        (sourceBefore.erase.append (.cons sourceReplacement sourceSuffix.erase))

private noncomputable def assembleFocusedBlocks
    (layout : PlugLayout input) (targetWf : layout.plugRaw.WellFormed)
    (sourceCall : CompilerCall input.frame.val)
    (targetOuter targetLocal : WireContext layout.plugRaw)
    (targetBinders : BinderContext layout.plugRaw sourceCall.rels)
    (outerEq : targetOuter =
      sourceCall.outerContext.map layout.frameWireMap)
    (localEq : targetLocal =
      sourceCall.localContext.map layout.frameWireMap)
    (parentAway : sourceCall.origin ≠ input.site)
    (sourceBefore sourceSuffix : CompiledItems input.frame.val
      sourceCall.fullContext sourceCall.rels sourceCall.binders)
    (sourceSelected : CompiledItem input.frame.val sourceCall.fullContext
      sourceCall.rels sourceCall.binders)
    (targetSelected : CompiledItem layout.plugRaw (targetOuter ++ targetLocal)
      sourceCall.rels targetBinders)
    (sourceOrigins :
      (sourceBefore.append (.cons sourceSelected sourceSuffix)).origins =
        localOccurrences input.frame.val sourceCall.origin)
    (beforeResult : AwayBlockResult layout targetWf targetOuter targetLocal
      targetBinders outerEq localEq parentAway sourceBefore)
    (suffixResult : AwayBlockResult layout targetWf targetOuter targetLocal
      targetBinders outerEq localEq parentAway sourceSuffix)
    (selectedCompiled : compileOccurrence? layout.plugRaw targetWf
      (layout.frameRegion sourceCall.origin) (targetOuter ++ targetLocal)
      targetBinders (layout.mapFrameOccurrence sourceSelected.origin)
      (by
        rw [layout.localOccurrences_frameRegion_of_ne_site sourceCall.origin
          parentAway]
        exact List.mem_map.mpr ⟨sourceSelected.origin, by
          rw [← sourceOrigins]
          simp [CompiledItems.origins_append, CompiledItems.origins], rfl⟩) =
        some targetSelected) :
    FocusedBlocksResult layout targetWf targetOuter targetLocal targetBinders
      outerEq localEq sourceBefore sourceSuffix sourceSelected.erase
      targetSelected := by
  let targetItems := beforeResult.target.append
    (.cons targetSelected suffixResult.target)
  have beforeOrigins := compileItems?_origins targetWf
    (layout.frameRegion sourceCall.origin) (targetOuter ++ targetLocal)
    targetBinders beforeResult.compiled
  have suffixOrigins := compileItems?_origins targetWf
    (layout.frameRegion sourceCall.origin) (targetOuter ++ targetLocal)
    targetBinders suffixResult.compiled
  have selectedOrigin := compileOccurrence?_origin targetWf
    (layout.frameRegion sourceCall.origin)
    (layout.mapFrameOccurrence sourceSelected.origin) _ selectedCompiled
  have targetOrigins : targetItems.origins =
      localOccurrences layout.plugRaw (layout.frameRegion sourceCall.origin) := by
    rw [layout.localOccurrences_frameRegion_of_ne_site sourceCall.origin
      parentAway]
    dsimp only [targetItems]
    rw [CompiledItems.origins_append, CompiledItems.origins,
      beforeOrigins, suffixOrigins, selectedOrigin, ← sourceOrigins]
    simp [CompiledItems.origins_append, CompiledItems.origins,
      List.map_append]
    rfl
  let targetDirect : ∀ occurrence, occurrence ∈ targetItems.origins →
      occurrence ∈ localOccurrences layout.plugRaw
        (layout.frameRegion sourceCall.origin) := by
    intro occurrence member
    simpa only [targetOrigins] using member
  have beforeCompiled : compileItems? layout.plugRaw targetWf
      (layout.frameRegion sourceCall.origin) (targetOuter ++ targetLocal)
      targetBinders beforeResult.target.origins
      (fun occurrence member => targetDirect occurrence (by
        dsimp only [targetItems]
        rw [CompiledItems.origins_append]
        exact List.mem_append_left _ member)) = some beforeResult.target := by
    simpa only [beforeOrigins] using beforeResult.compiled
  have suffixCompiled : compileItems? layout.plugRaw targetWf
      (layout.frameRegion sourceCall.origin) (targetOuter ++ targetLocal)
      targetBinders suffixResult.target.origins
      (fun occurrence member => targetDirect occurrence (by
        dsimp only [targetItems]
        rw [CompiledItems.origins_append]
        exact List.mem_append_right _ (by
          simp [CompiledItems.origins, member]))) = some suffixResult.target := by
    simpa only [suffixOrigins] using suffixResult.compiled
  have selectedCompiled' : compileOccurrence? layout.plugRaw targetWf
      (layout.frameRegion sourceCall.origin) (targetOuter ++ targetLocal)
      targetBinders targetSelected.origin
      (targetDirect targetSelected.origin (by
        dsimp only [targetItems]
        rw [CompiledItems.origins_append]
        exact List.mem_append_right _ (by simp [CompiledItems.origins]))) =
        some targetSelected := by
    simpa only [selectedOrigin] using selectedCompiled
  have tailCompiled : compileItems? layout.plugRaw targetWf
      (layout.frameRegion sourceCall.origin) (targetOuter ++ targetLocal)
      targetBinders (CompiledItems.cons targetSelected suffixResult.target).origins
      (fun occurrence member => targetDirect occurrence (by
        dsimp only [targetItems]
        rw [CompiledItems.origins_append]
        exact List.mem_append_right _ member)) =
        some (CompiledItems.cons targetSelected suffixResult.target) := by
    change compileItems? layout.plugRaw targetWf
      (layout.frameRegion sourceCall.origin) (targetOuter ++ targetLocal)
      targetBinders (targetSelected.origin :: suffixResult.target.origins) _ =
        some (CompiledItems.cons targetSelected suffixResult.target)
    rw [compileItems?_cons, selectedCompiled', suffixCompiled]
    rfl
  let combinedDirect : ∀ occurrence,
      occurrence ∈ beforeResult.target.origins ++
          (CompiledItems.cons targetSelected suffixResult.target).origins →
        occurrence ∈ localOccurrences layout.plugRaw
          (layout.frameRegion sourceCall.origin) := by
    intro occurrence member
    exact targetDirect occurrence (by
      dsimp only [targetItems]
      simpa only [CompiledItems.origins_append] using member)
  have combinedCompiled : compileItems? layout.plugRaw targetWf
      (layout.frameRegion sourceCall.origin) (targetOuter ++ targetLocal)
      targetBinders targetItems.origins targetDirect = some targetItems := by
    simpa only [targetItems, CompiledItems.origins_append] using
      compileItems?_append targetWf (layout.frameRegion sourceCall.origin)
        (targetOuter ++ targetLocal) targetBinders beforeResult.target.origins
        (CompiledItems.cons targetSelected suffixResult.target).origins
        combinedDirect beforeCompiled tailCompiled
  refine {
    targetBefore := beforeResult.target
    targetSuffix := suffixResult.target
    compiled := ?_
    frame := ?_
  }
  · exact (compileItems?_congr_occurrences targetWf
      (layout.frameRegion sourceCall.origin) (targetOuter ++ targetLocal)
      targetBinders targetOrigins targetDirect (fun _ member => member)).symm.trans
        combinedCompiled
  · intro targetReplacement sourceReplacement replacement
    exact beforeResult.iso.append
      ((ItemSeqIso.singleton replacement).append suffixResult.iso)

private abbrev GraftRegionFold
    (layout : PlugLayout input) (admissible : input.Admissible)
    (targetWf : layout.plugRaw.WellFormed)
    {sourceCall endpointCall : CompilerCall input.frame.val}
    (sourceBody : CompiledRegion input.frame.val sourceCall)
    (site : Fin input.frame.val.regionCount)
    (endpoint : CompiledRegion input.frame.val endpointCall)
    (focus : CompiledZipper input.frame.val sourceBody site endpointCall
      endpoint) :=
  (siteEq : site = input.site) →
  (endpointInput : EndpointGraftInput layout admissible endpointCall endpoint) →
  (targetOuter targetLocal : WireContext layout.plugRaw) →
  (targetBinders : BinderContext layout.plugRaw sourceCall.rels) →
  (frame : FrameEvidence layout targetWf sourceCall targetOuter targetLocal
    targetBinders sourceBody) →
  GraftResult layout targetWf targetOuter targetLocal targetBinders
    frame.outerEq site focus endpointInput.after

private abbrev GraftItemsFold
    (layout : PlugLayout input) (admissible : input.Admissible)
    (targetWf : layout.plugRaw.WellFormed)
    {sourceCall endpointCall : CompilerCall input.frame.val}
    (items : CompiledItems input.frame.val sourceCall.fullContext
      sourceCall.rels sourceCall.binders)
    (site : Fin input.frame.val.regionCount)
    (endpoint : CompiledRegion input.frame.val endpointCall)
    (focus : CompiledItemsZipper input.frame.val items site endpointCall
      endpoint) :=
  (siteEq : site = input.site) →
  (endpointInput : EndpointGraftInput layout admissible endpointCall endpoint) →
  (targetOuter targetLocal : WireContext layout.plugRaw) →
  (targetBinders : BinderContext layout.plugRaw sourceCall.rels) →
  (frame : FrameEvidence layout targetWf sourceCall targetOuter targetLocal
    targetBinders (.mk items)) →
  GraftResult layout targetWf targetOuter targetLocal targetBinders
    frame.outerEq site (.child focus) endpointInput.after

/-- The sole source zipper fold constructs one actual target compiler result
and one aligned enclosing context. -/
private noncomputable def compileAlongZipper
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (admissible : input.Admissible)
    (targetWf : layout.plugRaw.WellFormed)
    {sourceCall endpointCall : CompilerCall input.frame.val}
    {sourceBody : CompiledRegion input.frame.val sourceCall}
    {site : Fin input.frame.val.regionCount}
    {endpoint : CompiledRegion input.frame.val endpointCall}
    (focus : CompiledZipper input.frame.val sourceBody site endpointCall
      endpoint) :
    GraftRegionFold layout admissible targetWf sourceBody site endpoint focus := by
  apply CompiledZipper.rec
    (motive_1 := fun sourceBody site _ endpoint focus =>
      GraftRegionFold layout admissible targetWf sourceBody site endpoint focus)
    (motive_2 := fun items site _ endpoint focus =>
      GraftItemsFold layout admissible targetWf items site endpoint focus)
  · intro sourceCall source siteEq endpointInput targetOuter targetLocal
      targetBinders frame
    have originEq : sourceCall.origin = input.site := siteEq
    have sourceExact := frame.sourceExact
    rw [originEq] at sourceExact
    have targetExact := frame.targetExact
    rw [originEq] at targetExact
    have fullEq := frame.fullEq
    simp only [originEq, if_pos] at fullEq
    exact layout.compileHere consistent admissible targetWf sourceCall source
      targetOuter targetLocal targetBinders originEq frame.outerEq
      frame.targetLocalCall fullEq sourceExact targetExact
      frame.frameBindersMapped endpointInput.relationMap
      endpointInput.hostLookup endpointInput.materialWireMap
      endpointInput.materialGet frame.sourceCompiled endpointInput.after
      endpointInput.afterEq
  · intro sourceCall endpointCall items site endpoint nested induction siteEq
      endpointInput targetOuter targetLocal targetBinders frame
    exact induction siteEq endpointInput targetOuter targetLocal targetBinders
      frame
  · intro sourceCall origin body before suffix items site endpointCall
      endpoint nested rebuild induction siteEq endpointInput targetOuter
      targetLocal targetBinders frame
    subst items
    have sourceItemsCompiled := sourceCall.compile?_items_of_success
      input.frame.property frame.sourceCompiled
    have sourceOrigins := compileItems?_origins input.frame.property
      sourceCall.origin sourceCall.fullContext sourceCall.binders
      sourceItemsCompiled
    let sourceDirect : ∀ occurrence,
        occurrence ∈ (before.append (.cons (.cut body) suffix)).origins →
          occurrence ∈ localOccurrences input.frame.val sourceCall.origin := by
      intro occurrence member
      simpa only [sourceOrigins] using member
    have canonicalCompiled : compileItems? input.frame.val
        input.frame.property sourceCall.origin sourceCall.fullContext
        sourceCall.binders
        (before.append (.cons (.cut body) suffix)).origins sourceDirect =
          some (before.append (.cons (.cut body) suffix)) := by
      simpa only [sourceOrigins] using sourceItemsCompiled
    obtain ⟨beforeCompiled, selectedCompiled, suffixCompiled⟩ :=
      compileItems?_selected_inv input.frame.property sourceCall.origin
        sourceCall.fullContext sourceCall.binders before (.cut body) suffix
        sourceDirect canonicalCompiled
    let selectedDirect : LocalOccurrence.child origin ∈
        localOccurrences input.frame.val sourceCall.origin :=
      sourceDirect (.child origin) (by
        simp [CompiledItems.origins_append, CompiledItems.origins,
          CompiledItem.origin])
    have selectedCompiled' : compileOccurrence? input.frame.val
        input.frame.property sourceCall.origin sourceCall.fullContext
        sourceCall.binders (.child origin) selectedDirect = some (.cut body) := by
      simpa only [CompiledItem.origin] using selectedCompiled
    have sourceParent := (mem_localOccurrences_child input.frame.val
      sourceCall.origin origin).mp selectedDirect
    have sourceRegion : input.frame.val.regions origin =
        .cut sourceCall.origin := by
      cases regionEq : input.frame.val.regions origin with
      | sheet =>
          rw [compileOccurrence?_child_sheet input.frame.property
            sourceCall.origin origin sourceCall.fullContext sourceCall.binders
            selectedDirect regionEq] at selectedCompiled'
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
          rw [compileOccurrence?_child_bubble input.frame.property
            sourceCall.origin origin sourceCall.fullContext sourceCall.binders
            arity selectedDirect regionEq] at selectedCompiled'
          cases childResult : compileRegion? input.frame.val
              input.frame.property origin sourceCall.fullContext
              (sourceCall.binders.push origin arity) <;>
            simp [childResult] at selectedCompiled'
    have childCompiled := compileOccurrence?_child_cut_body
      input.frame.property sourceCall.origin origin sourceCall.fullContext
      sourceCall.binders selectedDirect sourceRegion selectedCompiled'
    have childExact := frame.sourceExact.extend_child input.frame.property
      sourceParent
    have childCovers := BinderContext.covers_cut_child frame.sourceCovers
      sourceRegion
    have childEnumeration := frame.sourceEnumeration.cutChild
      input.frame.property sourceRegion
    have childEncloses := nested.endpoint_encloses input.frame.property
      childCompiled childExact childCovers childEnumeration
    have parentAway : sourceCall.origin ≠ input.site := by
      intro same
      rw [siteEq] at childEncloses
      rw [same] at sourceParent
      exact checked_direct_child_not_encloses_parent input.frame.property
        sourceParent childEncloses
    have localEq : targetLocal =
        sourceCall.localContext.map layout.frameWireMap := by
      have fullEq := frame.fullEq
      simp only [parentAway, if_false, List.append_nil,
        CompilerCall.fullContext, List.map_append] at fullEq
      rw [frame.outerEq] at fullEq
      exact (List.append_right_inj _).mp fullEq
    let childTargetOuter := targetOuter ++ targetLocal
    let childTargetLocal := exactScopeWires layout.plugRaw
      (layout.frameRegion origin)
    have childOuterEq : childTargetOuter =
        sourceCall.fullContext.map layout.frameWireMap := by
      dsimp only [childTargetOuter]
      have fullEq := frame.fullEq
      simpa only [parentAway, if_false, List.append_nil] using fullEq
    have childFullEq : childTargetOuter ++ childTargetLocal =
        (sourceCall.fullContext.extend origin).map layout.frameWireMap ++
          (if origin = input.site then
            (CompiledSite.endpointCall (State.ofOpen input.pattern)
              input.binderSpine.bodyContainer).localContext.map
                layout.patternWireMap
          else []) := by
      dsimp only [childTargetLocal]
      rw [layout.exactScopeWires_frameRegion consistent
        admissible.terminal_body origin,
        layout.bodyLocalWires_eq_endpointLocalMap]
      simp only [PlugLayout.frameLocalWires, WireContext.extend,
        List.map_append]
      rw [childOuterEq]
      simp only [List.append_assoc]
      rfl
    have targetParent : (layout.plugRaw.regions
        (layout.frameRegion origin)).parent? =
          some (layout.frameRegion sourceCall.origin) := by
      rw [layout.plugRaw_regions_frame]
      exact (layout.mapFrameRegion_parent_eq_some_iff origin
        sourceCall.origin).2 sourceParent
    let childFrame : FrameEvidence layout targetWf
        (.nested origin sourceCall.fullContext sourceCall.rels
          sourceCall.binders) childTargetOuter childTargetLocal targetBinders
          body := {
      outerEq := childOuterEq
      fullEq := childFullEq
      targetLocalCall := rfl
      sourceExact := childExact
      sourceCovers := childCovers
      sourceEnumeration := childEnumeration
      targetExact := frame.targetExact.extend_child targetWf targetParent
      frameBindersMapped := frame.frameBindersMapped
      sourceCompiled := childCompiled
    }
    let childResult := induction siteEq endpointInput
      childTargetOuter childTargetLocal targetBinders childFrame
    have sourceNodup :
        (before.append (.cons (.cut body) suffix)).origins.Nodup := by
      rw [sourceOrigins]
      exact localOccurrences_nodup input.frame.val sourceCall.origin
    have beforeDisjointTail :=
      (List.nodup_append.mp (by
        simpa only [CompiledItems.origins_append] using sourceNodup)).2.2
    have selectedNotBefore : LocalOccurrence.child origin ∉ before.origins := by
      intro member
      exact beforeDisjointTail _ member _ (by
        simp [CompiledItem.origin]) rfl
    have tailNodup :
        (CompiledItems.cons (.cut body) suffix).origins.Nodup :=
      (List.nodup_append.mp (by
        simpa only [CompiledItems.origins_append] using sourceNodup)).2.1
    have selectedNotSuffix : LocalOccurrence.child origin ∉ suffix.origins :=
      (List.nodup_cons.mp (by
        simpa only [CompiledItems.origins, CompiledItem.origin] using
          tailNodup)).1
    let beforeDirect : ∀ occurrence, occurrence ∈ before.origins →
        occurrence ∈ localOccurrences input.frame.val sourceCall.origin := by
      intro occurrence member
      exact sourceDirect occurrence (by
        simp only [CompiledItems.origins_append]
        exact List.mem_append_left _ member)
    let suffixDirect : ∀ occurrence, occurrence ∈ suffix.origins →
        occurrence ∈ localOccurrences input.frame.val sourceCall.origin := by
      intro occurrence member
      exact sourceDirect occurrence (by
        simp only [CompiledItems.origins_append, CompiledItems.origins,
          CompiledItem.origin]
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
    let beforeResult := layout.compileAwayBlock consistent
      admissible.terminal_body targetWf sourceCall targetOuter targetLocal
      targetBinders frame.outerEq localEq parentAway frame.sourceExact
      frame.targetExact frame.frameBindersMapped origin sourceParent
      (by simpa only [siteEq] using childEncloses) before beforeDirect
      beforeDifferent beforeCompiled
    let suffixResult := layout.compileAwayBlock consistent
      admissible.terminal_body targetWf sourceCall targetOuter targetLocal
      targetBinders frame.outerEq localEq parentAway frame.sourceExact
      frame.targetExact frame.frameBindersMapped origin sourceParent
      (by simpa only [siteEq] using childEncloses) suffix suffixDirect
      suffixDifferent suffixCompiled
    let targetSelected : CompiledItem layout.plugRaw
        (targetOuter ++ targetLocal) sourceCall.rels targetBinders :=
      .cut childResult.targetBody
    have targetRegion : layout.plugRaw.regions (layout.frameRegion origin) =
        .cut (layout.frameRegion sourceCall.origin) := by
      rw [layout.plugRaw_regions_frame, sourceRegion]
      rfl
    have selectedTargetDirect : LocalOccurrence.child
        (layout.frameRegion origin) ∈ localOccurrences layout.plugRaw
          (layout.frameRegion sourceCall.origin) := by
      rw [layout.localOccurrences_frameRegion_of_ne_site sourceCall.origin
        parentAway]
      exact List.mem_map.mpr ⟨.child origin, selectedDirect, rfl⟩
    have targetSelectedCompiled : compileOccurrence? layout.plugRaw targetWf
        (layout.frameRegion sourceCall.origin) (targetOuter ++ targetLocal)
        targetBinders (.child (layout.frameRegion origin))
          selectedTargetDirect = some targetSelected := by
      have childTargetCompiled : compileRegion? layout.plugRaw targetWf
          (layout.frameRegion origin) (targetOuter ++ targetLocal)
          targetBinders = some childResult.targetBody := by
        simpa only [childTargetOuter, frameTargetCall] using
          childResult.targetCompiled
      rw [compileOccurrence?_child_cut targetWf
        (layout.frameRegion sourceCall.origin) (layout.frameRegion origin)
        (targetOuter ++ targetLocal) targetBinders selectedTargetDirect
        targetRegion, childTargetCompiled]
      rfl
    let blocks := layout.assembleFocusedBlocks targetWf sourceCall
      targetOuter targetLocal targetBinders frame.outerEq localEq parentAway
      before suffix (.cut body) targetSelected sourceOrigins beforeResult
      suffixResult targetSelectedCompiled
    let targetItems := blocks.targetBefore.append
      (.cons targetSelected blocks.targetSuffix)
    let targetBody := layout.frameTargetBody sourceCall targetOuter targetLocal
      targetBinders frame.targetLocalCall targetItems
    have targetCompiled : (layout.frameTargetCall sourceCall targetOuter
        targetLocal targetBinders).compile? layout.plugRaw targetWf =
          some targetBody := by
      exact layout.frameTargetCall_compile_of_items targetWf sourceCall
        targetOuter targetLocal targetBinders frame.targetLocalCall targetItems
        blocks.compiled
    let targetSplit : (targetOuter ++ targetLocal).length =
        targetOuter.length + targetLocal.length := List.length_append
    let sourceSplit : sourceCall.fullContext.length =
        sourceCall.outerContext.length + sourceCall.localContext.length :=
      sourceCall.fullContext_length
    let targetContext : DiagramContext targetOuter.length
        childResult.holeWires sourceCall.rels endpointCall.rels :=
      .cut targetLocal.length
        (blocks.targetBefore.erase.castWiresEq targetSplit)
        (blocks.targetSuffix.erase.castWiresEq targetSplit)
        (targetSplit ▸ childResult.targetContext)
    have alignment : DiagramContextIso
        (layout.canonicalOuterWire sourceCall targetOuter frame.outerEq)
        childResult.holeWire sourceCall.rels endpointCall.rels targetContext
        (.cut sourceCall.localContext.length
          (before.erase.castWiresEq sourceSplit)
          (suffix.erase.castWiresEq sourceSplit)
          (sourceSplit ▸ nested.intrinsic.context)) := by
      let localWire := layout.mappedLocalWire sourceCall targetLocal localEq
      have childOuterWireEq :
          layout.canonicalOuterWire
              (.nested origin sourceCall.fullContext sourceCall.rels
                sourceCall.binders) childTargetOuter childOuterEq =
            layout.mappedFullWire sourceCall targetOuter targetLocal
              frame.outerEq localEq := by
        apply FiniteEquiv.ext
        intro index
        apply Fin.ext
        let split := Fin.cast List.length_append index
        have splitEq : Fin.cast List.length_append.symm split = index := by
          apply Fin.ext
          rfl
        rw [← splitEq]
        exact Fin.addCases
          (motive := fun position =>
            ((layout.canonicalOuterWire
              (.nested origin sourceCall.fullContext sourceCall.rels
                sourceCall.binders) childTargetOuter childOuterEq)
                (Fin.cast List.length_append.symm position)).val =
              ((layout.mappedFullWire sourceCall targetOuter targetLocal
                frame.outerEq localEq)
                (Fin.cast List.length_append.symm position)).val)
          (fun inherited => by
            simp [canonicalOuterWire, mappedFullWire, mappedLocalWire,
              castFinEquiv, extendWireEquiv, FiniteEquiv.finCast])
          (fun localIndex => by
            have outerLength : targetOuter.length =
                sourceCall.outerContext.length :=
              (congrArg List.length frame.outerEq).trans
                (List.length_map layout.frameWireMap)
            simp [canonicalOuterWire, mappedFullWire, mappedLocalWire,
              castFinEquiv, extendWireEquiv, FiniteEquiv.finCast,
              outerLength]) split
      have childAlignment := childResult.alignment
      rw [childOuterWireEq] at childAlignment
      exact DiagramContextIso.cutCompilerFrame localWire targetSplit
        sourceSplit blocks.targetBefore.erase blocks.targetSuffix.erase
        before.erase suffix.erase childResult.targetContext
        nested.intrinsic.context
        (layout.mappedFullWire sourceCall targetOuter targetLocal
          frame.outerEq localEq) (by
            intro index
            change (Fin.cast sourceSplit (Fin.cast sourceSplit.symm
              (extendWireEquiv
                (layout.canonicalOuterWire sourceCall targetOuter
                  frame.outerEq)
                localWire (Fin.cast targetSplit index)))).val = _
            rfl)
        childAlignment blocks.frame
    have targetRebuild : targetContext.fill childResult.targetSite =
        layout.frameTargetErase sourceCall targetOuter targetLocal targetBinders
          targetBody := by
      have childRebuild : childResult.targetContext.fill
          childResult.targetSite = childResult.targetBody.erase := by
        simpa [frameTargetErase] using childResult.targetRebuild
      have nestedEq : (targetSplit ▸ childResult.targetContext).fill
          childResult.targetSite =
            childResult.targetBody.erase.castWiresEq targetSplit :=
        (DiagramContext.castOuterWires_fill targetSplit
          childResult.targetContext childResult.targetSite).trans
            (congrArg (Region.castWiresEq targetSplit) childRebuild)
      dsimp only [targetContext]
      simp only [DiagramContext.fill]
      calc
        _ = .mk targetLocal.length
            ((blocks.targetBefore.erase.castWiresEq targetSplit).append
              (.cons (.cut
                (childResult.targetBody.erase.castWiresEq targetSplit))
                (blocks.targetSuffix.erase.castWiresEq targetSplit))) := by
          exact congrArg (fun sequence => Region.mk targetLocal.length
            ((blocks.targetBefore.erase.castWiresEq targetSplit).append
              (.cons (.cut sequence)
                (blocks.targetSuffix.erase.castWiresEq targetSplit)))) nestedEq
        _ = _ := by
          rw [frameTargetErase_frameTargetBody]
          dsimp only [targetItems, targetSelected]
          rw [CompiledItems.erase_append]
          simp only [CompiledItems.erase_cons,
            ItemSeq.castWiresEq_append, ItemSeq.castWiresEq_cons]
          apply congrArg (Region.mk targetLocal.length)
          rw [ItemSeq.castWiresEq_proof_irrel targetSplit _
            blocks.targetBefore.erase]
          rw [ItemSeq.castWiresEq_proof_irrel targetSplit _
            blocks.targetSuffix.erase]
          change _ = _
          simp only [CompiledItem.erase, Item.castWiresEq_cut]
          congr 1
          all_goals exact targetSplit
    exact {
      targetBody := targetBody
      targetCompiled := targetCompiled
      holeWires := childResult.holeWires
      holeWire := childResult.holeWire
      targetSite := childResult.targetSite
      targetContext := targetContext
      alignment := by
        simpa only [CompiledItemsZipper.intrinsic,
          CompiledZipper.intrinsic] using alignment
      targetRebuild := targetRebuild
      endpointIso := childResult.endpointIso
    }

  · intro sourceCall origin arity body before suffix items site endpointCall
      endpoint nested rebuild induction siteEq endpointInput targetOuter
      targetLocal targetBinders frame
    subst items
    have sourceItemsCompiled := sourceCall.compile?_items_of_success
      input.frame.property frame.sourceCompiled
    have sourceOrigins := compileItems?_origins input.frame.property
      sourceCall.origin sourceCall.fullContext sourceCall.binders
      sourceItemsCompiled
    let sourceDirect : ∀ occurrence,
        occurrence ∈ (before.append (.cons (.bubble arity body) suffix)).origins →
          occurrence ∈ localOccurrences input.frame.val sourceCall.origin := by
      intro occurrence member
      simpa only [sourceOrigins] using member
    have canonicalCompiled : compileItems? input.frame.val
        input.frame.property sourceCall.origin sourceCall.fullContext
        sourceCall.binders
        (before.append (.cons (.bubble arity body) suffix)).origins sourceDirect =
          some (before.append (.cons (.bubble arity body) suffix)) := by
      simpa only [sourceOrigins] using sourceItemsCompiled
    obtain ⟨beforeCompiled, selectedCompiled, suffixCompiled⟩ :=
      compileItems?_selected_inv input.frame.property sourceCall.origin
        sourceCall.fullContext sourceCall.binders before (.bubble arity body)
        suffix sourceDirect canonicalCompiled
    let selectedDirect : LocalOccurrence.child origin ∈
        localOccurrences input.frame.val sourceCall.origin :=
      sourceDirect (.child origin) (by
        simp [CompiledItems.origins_append, CompiledItems.origins,
          CompiledItem.origin])
    have selectedCompiled' : compileOccurrence? input.frame.val
        input.frame.property sourceCall.origin sourceCall.fullContext
        sourceCall.binders (.child origin) selectedDirect =
          some (.bubble arity body) := by
      simpa only [CompiledItem.origin] using selectedCompiled
    have sourceParent := (mem_localOccurrences_child input.frame.val
      sourceCall.origin origin).mp selectedDirect
    have sourceRegion : input.frame.val.regions origin =
        .bubble sourceCall.origin arity := by
      cases regionEq : input.frame.val.regions origin with
      | sheet =>
          rw [compileOccurrence?_child_sheet input.frame.property
            sourceCall.origin origin sourceCall.fullContext sourceCall.binders
            selectedDirect regionEq] at selectedCompiled'
          contradiction
      | cut parent =>
          have parentEq : parent = sourceCall.origin := by
            simpa [regionEq, CRegion.parent?] using sourceParent
          subst parent
          rw [compileOccurrence?_child_cut input.frame.property
            sourceCall.origin origin sourceCall.fullContext sourceCall.binders
            selectedDirect regionEq] at selectedCompiled'
          cases childResult : compileRegion? input.frame.val
              input.frame.property origin sourceCall.fullContext
              sourceCall.binders <;> simp [childResult] at selectedCompiled'
      | bubble parent childArity =>
          have parentEq : parent = sourceCall.origin := by
            simpa [regionEq, CRegion.parent?] using sourceParent
          subst parent
          rw [compileOccurrence?_child_bubble input.frame.property
            sourceCall.origin origin sourceCall.fullContext sourceCall.binders
            childArity selectedDirect regionEq] at selectedCompiled'
          cases childResult : compileRegion? input.frame.val
              input.frame.property origin sourceCall.fullContext
              (sourceCall.binders.push origin childArity) <;>
            simp [childResult] at selectedCompiled'
          rename_i childBody
          cases selectedCompiled'
          congr
    have childCompiled := compileOccurrence?_child_bubble_body
      input.frame.property sourceCall.origin origin sourceCall.fullContext
      sourceCall.binders arity selectedDirect sourceRegion selectedCompiled'
    have childExact := frame.sourceExact.extend_child input.frame.property
      sourceParent
    have childCovers := BinderContext.push_covers_bubble_child
      frame.sourceCovers sourceRegion
    have childEnumeration := frame.sourceEnumeration.bubbleChild
      input.frame.property sourceRegion
    have childEncloses := nested.endpoint_encloses input.frame.property
      childCompiled childExact childCovers childEnumeration
    have parentAway : sourceCall.origin ≠ input.site := by
      intro same
      rw [siteEq] at childEncloses
      rw [same] at sourceParent
      exact checked_direct_child_not_encloses_parent input.frame.property
        sourceParent childEncloses
    have localEq : targetLocal =
        sourceCall.localContext.map layout.frameWireMap := by
      have fullEq := frame.fullEq
      simp only [parentAway, if_false, List.append_nil,
        CompilerCall.fullContext, List.map_append] at fullEq
      rw [frame.outerEq] at fullEq
      exact (List.append_right_inj _).mp fullEq
    let childTargetOuter := targetOuter ++ targetLocal
    let childTargetLocal := exactScopeWires layout.plugRaw
      (layout.frameRegion origin)
    let childTargetBinders := targetBinders.push
      (layout.frameRegion origin) arity
    have childOuterEq : childTargetOuter =
        sourceCall.fullContext.map layout.frameWireMap := by
      dsimp only [childTargetOuter]
      simpa only [parentAway, if_false, List.append_nil] using frame.fullEq
    have childFullEq : childTargetOuter ++ childTargetLocal =
        (sourceCall.fullContext.extend origin).map layout.frameWireMap ++
          (if origin = input.site then
            (CompiledSite.endpointCall (State.ofOpen input.pattern)
              input.binderSpine.bodyContainer).localContext.map
                layout.patternWireMap else []) := by
      dsimp only [childTargetLocal]
      rw [layout.exactScopeWires_frameRegion consistent
        admissible.terminal_body origin,
        layout.bodyLocalWires_eq_endpointLocalMap]
      simp only [PlugLayout.frameLocalWires, WireContext.extend,
        List.map_append]
      rw [childOuterEq]
      simp only [List.append_assoc]
      rfl
    have targetParent : (layout.plugRaw.regions
        (layout.frameRegion origin)).parent? =
          some (layout.frameRegion sourceCall.origin) := by
      rw [layout.plugRaw_regions_frame]
      exact (layout.mapFrameRegion_parent_eq_some_iff origin
        sourceCall.origin).2 sourceParent
    let childFrame : FrameEvidence layout targetWf
        (.nested origin sourceCall.fullContext (arity :: sourceCall.rels)
          (sourceCall.binders.push origin arity)) childTargetOuter
          childTargetLocal childTargetBinders body := {
      outerEq := childOuterEq
      fullEq := childFullEq
      targetLocalCall := rfl
      sourceExact := childExact
      sourceCovers := childCovers
      sourceEnumeration := childEnumeration
      targetExact := frame.targetExact.extend_child targetWf targetParent
      frameBindersMapped := by
        simpa [childTargetBinders, RelationRenaming.lift_id_fun] using
          layout.frameBindersMapped_push sourceCall.binders targetBinders
            (fun relation => relation)
            (by intro binder; simpa using frame.frameBindersMapped binder)
            origin arity
      sourceCompiled := childCompiled
    }
    let childResult := induction siteEq endpointInput
      childTargetOuter childTargetLocal childTargetBinders childFrame
    have sourceNodup :
        (before.append (.cons (.bubble arity body) suffix)).origins.Nodup := by
      rw [sourceOrigins]
      exact localOccurrences_nodup input.frame.val sourceCall.origin
    have beforeDisjointTail := (List.nodup_append.mp (by
      simpa only [CompiledItems.origins_append] using sourceNodup)).2.2
    have selectedNotBefore : LocalOccurrence.child origin ∉ before.origins := by
      intro member
      exact beforeDisjointTail _ member _ (by simp [CompiledItem.origin]) rfl
    have tailNodup : (CompiledItems.cons (.bubble arity body)
        suffix).origins.Nodup :=
      (List.nodup_append.mp (by
        simpa only [CompiledItems.origins_append] using sourceNodup)).2.1
    have selectedNotSuffix : LocalOccurrence.child origin ∉ suffix.origins :=
      (List.nodup_cons.mp (by
        simpa only [CompiledItems.origins, CompiledItem.origin] using
          tailNodup)).1
    let beforeDirect : ∀ occurrence, occurrence ∈ before.origins →
        occurrence ∈ localOccurrences input.frame.val sourceCall.origin := by
      intro occurrence member
      exact sourceDirect occurrence (by
        simp only [CompiledItems.origins_append]
        exact List.mem_append_left _ member)
    let suffixDirect : ∀ occurrence, occurrence ∈ suffix.origins →
        occurrence ∈ localOccurrences input.frame.val sourceCall.origin := by
      intro occurrence member
      exact sourceDirect occurrence (by
        simp only [CompiledItems.origins_append, CompiledItems.origins,
          CompiledItem.origin]
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
    let beforeResult := layout.compileAwayBlock consistent
      admissible.terminal_body targetWf sourceCall targetOuter targetLocal
      targetBinders frame.outerEq localEq parentAway frame.sourceExact
      frame.targetExact frame.frameBindersMapped origin sourceParent
      (by simpa only [siteEq] using childEncloses) before beforeDirect
      beforeDifferent beforeCompiled
    let suffixResult := layout.compileAwayBlock consistent
      admissible.terminal_body targetWf sourceCall targetOuter targetLocal
      targetBinders frame.outerEq localEq parentAway frame.sourceExact
      frame.targetExact frame.frameBindersMapped origin sourceParent
      (by simpa only [siteEq] using childEncloses) suffix suffixDirect
      suffixDifferent suffixCompiled
    let targetSelected : CompiledItem layout.plugRaw
        (targetOuter ++ targetLocal) sourceCall.rels targetBinders :=
      .bubble arity childResult.targetBody
    have targetRegion : layout.plugRaw.regions (layout.frameRegion origin) =
        .bubble (layout.frameRegion sourceCall.origin) arity := by
      rw [layout.plugRaw_regions_frame, sourceRegion]
      rfl
    have selectedTargetDirect : LocalOccurrence.child
        (layout.frameRegion origin) ∈ localOccurrences layout.plugRaw
          (layout.frameRegion sourceCall.origin) := by
      rw [layout.localOccurrences_frameRegion_of_ne_site sourceCall.origin
        parentAway]
      exact List.mem_map.mpr ⟨.child origin, selectedDirect, rfl⟩
    have targetSelectedCompiled : compileOccurrence? layout.plugRaw targetWf
        (layout.frameRegion sourceCall.origin) (targetOuter ++ targetLocal)
        targetBinders (.child (layout.frameRegion origin))
          selectedTargetDirect = some targetSelected := by
      have childTargetCompiled : compileRegion? layout.plugRaw targetWf
          (layout.frameRegion origin) (targetOuter ++ targetLocal)
          childTargetBinders = some childResult.targetBody := by
        simpa only [childTargetOuter, childTargetBinders, frameTargetCall] using
          childResult.targetCompiled
      rw [compileOccurrence?_child_bubble targetWf
        (layout.frameRegion sourceCall.origin) (layout.frameRegion origin)
        (targetOuter ++ targetLocal) targetBinders arity selectedTargetDirect
        targetRegion, childTargetCompiled]
      rfl
    let blocks := layout.assembleFocusedBlocks targetWf sourceCall
      targetOuter targetLocal targetBinders frame.outerEq localEq parentAway
      before suffix (.bubble arity body) targetSelected sourceOrigins
      beforeResult suffixResult targetSelectedCompiled
    let targetItems := blocks.targetBefore.append
      (.cons targetSelected blocks.targetSuffix)
    let targetBody := layout.frameTargetBody sourceCall targetOuter targetLocal
      targetBinders frame.targetLocalCall targetItems
    have targetCompiled : (layout.frameTargetCall sourceCall targetOuter
        targetLocal targetBinders).compile? layout.plugRaw targetWf =
          some targetBody :=
      layout.frameTargetCall_compile_of_items targetWf sourceCall targetOuter
        targetLocal targetBinders frame.targetLocalCall targetItems
        blocks.compiled
    let targetSplit : (targetOuter ++ targetLocal).length =
        targetOuter.length + targetLocal.length := List.length_append
    let sourceSplit : sourceCall.fullContext.length =
        sourceCall.outerContext.length + sourceCall.localContext.length :=
      sourceCall.fullContext_length
    let targetContext : DiagramContext targetOuter.length
        childResult.holeWires sourceCall.rels endpointCall.rels :=
      .bubble targetLocal.length
        (blocks.targetBefore.erase.castWiresEq targetSplit)
        (blocks.targetSuffix.erase.castWiresEq targetSplit) arity
        (targetSplit ▸ childResult.targetContext)
    have alignment : DiagramContextIso
        (layout.canonicalOuterWire sourceCall targetOuter frame.outerEq)
        childResult.holeWire sourceCall.rels endpointCall.rels targetContext
        (.bubble sourceCall.localContext.length
          (before.erase.castWiresEq sourceSplit)
          (suffix.erase.castWiresEq sourceSplit) arity
          (sourceSplit ▸ nested.intrinsic.context)) := by
      let localWire := layout.mappedLocalWire sourceCall targetLocal localEq
      have childOuterWireEq : layout.canonicalOuterWire
          (.nested origin sourceCall.fullContext (arity :: sourceCall.rels)
            (sourceCall.binders.push origin arity)) childTargetOuter
            childOuterEq = layout.mappedFullWire sourceCall targetOuter
              targetLocal frame.outerEq localEq := by
        apply FiniteEquiv.ext
        intro index
        apply Fin.ext
        let split := Fin.cast List.length_append index
        have splitEq : Fin.cast List.length_append.symm split = index := by
          apply Fin.ext
          rfl
        rw [← splitEq]
        exact Fin.addCases
          (motive := fun position =>
            ((layout.canonicalOuterWire
              (.nested origin sourceCall.fullContext (arity :: sourceCall.rels)
                (sourceCall.binders.push origin arity)) childTargetOuter
                childOuterEq) (Fin.cast List.length_append.symm position)).val =
              ((layout.mappedFullWire sourceCall targetOuter targetLocal
                frame.outerEq localEq)
                (Fin.cast List.length_append.symm position)).val)
          (fun inherited => by simp [canonicalOuterWire, mappedFullWire,
            mappedLocalWire, castFinEquiv, extendWireEquiv,
            FiniteEquiv.finCast])
          (fun localIndex => by
            have outerLength : targetOuter.length =
                sourceCall.outerContext.length :=
              (congrArg List.length frame.outerEq).trans
                (List.length_map layout.frameWireMap)
            simp [canonicalOuterWire, mappedFullWire, mappedLocalWire,
              castFinEquiv, extendWireEquiv, FiniteEquiv.finCast,
              outerLength]) split
      have childAlignment := childResult.alignment
      rw [childOuterWireEq] at childAlignment
      exact DiagramContextIso.bubbleCompilerFrame
        (layout.mappedLocalWire sourceCall targetLocal localEq) targetSplit
        sourceSplit blocks.targetBefore.erase blocks.targetSuffix.erase
        before.erase suffix.erase childResult.targetContext
        nested.intrinsic.context
        (layout.mappedFullWire sourceCall targetOuter targetLocal
          frame.outerEq localEq) (by
            intro index
            change (Fin.cast sourceSplit (Fin.cast sourceSplit.symm
              (extendWireEquiv
                (layout.canonicalOuterWire sourceCall targetOuter frame.outerEq)
                (layout.mappedLocalWire sourceCall targetLocal localEq)
                (Fin.cast targetSplit index)))).val = _
            rfl)
        childAlignment blocks.frame
    have targetRebuild : targetContext.fill childResult.targetSite =
        layout.frameTargetErase sourceCall targetOuter targetLocal targetBinders
          targetBody := by
      have childRebuild : childResult.targetContext.fill
          childResult.targetSite = childResult.targetBody.erase := by
        simpa [frameTargetErase] using childResult.targetRebuild
      have nestedEq : (targetSplit ▸ childResult.targetContext).fill
          childResult.targetSite =
            childResult.targetBody.erase.castWiresEq targetSplit :=
        (DiagramContext.castOuterWires_fill targetSplit
          childResult.targetContext childResult.targetSite).trans
            (congrArg (Region.castWiresEq targetSplit) childRebuild)
      dsimp only [targetContext]
      simp only [DiagramContext.fill]
      calc
        _ = .mk targetLocal.length
            ((blocks.targetBefore.erase.castWiresEq targetSplit).append
              (.cons (.bubble arity
                (childResult.targetBody.erase.castWiresEq targetSplit))
                (blocks.targetSuffix.erase.castWiresEq targetSplit))) := by
          exact congrArg (fun sequence => Region.mk targetLocal.length
            ((blocks.targetBefore.erase.castWiresEq targetSplit).append
              (.cons (.bubble arity sequence)
                (blocks.targetSuffix.erase.castWiresEq targetSplit)))) nestedEq
        _ = _ := by
          rw [frameTargetErase_frameTargetBody]
          dsimp only [targetItems, targetSelected]
          rw [CompiledItems.erase_append]
          simp only [CompiledItems.erase_cons,
            ItemSeq.castWiresEq_append, ItemSeq.castWiresEq_cons]
          apply congrArg (Region.mk targetLocal.length)
          rw [ItemSeq.castWiresEq_proof_irrel targetSplit _
            blocks.targetBefore.erase]
          rw [ItemSeq.castWiresEq_proof_irrel targetSplit _
            blocks.targetSuffix.erase]
          change _ = _
          simp only [CompiledItem.erase, Item.castWiresEq_bubble]
          congr 1
          all_goals exact targetSplit
    exact {
      targetBody := targetBody
      targetCompiled := targetCompiled
      holeWires := childResult.holeWires
      holeWire := childResult.holeWire
      targetSite := childResult.targetSite
      targetContext := targetContext
      alignment := by
        simpa only [CompiledItemsZipper.intrinsic,
          CompiledZipper.intrinsic] using alignment
      targetRebuild := targetRebuild
      endpointIso := childResult.endpointIso
    }

end Splice.Input.PlugLayout

namespace Elaboration.CompiledSite

private theorem state_eq_of_checked
    {arity : Nat} {left right : State arity}
    (equality : left.checked = right.checked) : left = right := by
  cases left with
  | mk leftChecked leftBoundaryLength =>
      cases right with
      | mk rightChecked rightBoundaryLength =>
          simp only at equality
          subst rightChecked
          rfl

private noncomputable def state_elaboration_iso
    {arity : Nat} {left right : State arity} (equality : left = right) :
    OpenDiagramIso
      (left.checked.elaborate.castArity left.boundary_length)
      (right.checked.elaborate.castArity right.boundary_length) := by
  subst right
  exact OpenDiagramIso.refl _

/-- Compile one successful splice from an already-derived source root result
and its sole structural focus.  This is the neutral composition boundary used
by larger flat primitives: it never searches the splice target, and it does
not require the source focus to have been selected by `CompiledSite.focus`. -/
noncomputable def spliceFromFocus
    {arity : Nat} {source : State arity} (input : Splice.Input)
    (frameEq : input.frame = source.diagram)
    {operation : OperationReceipt input.frame}
    (success : spliceRaw input = .ok operation)
    {receipt : Receipt source}
    (packed : (operation.castInput frameEq).toReceipt source = some receipt)
    (consistent : input.AttachmentConsistent)
    (sourceBody : CompiledRegion source.checked.val.diagram
      (.root source.checked.val.exposedWires source.checked.val.hiddenWires))
    (sourceCompiled :
      (CompilerCall.root source.checked.val.exposedWires
          source.checked.val.hiddenWires).compile?
        source.checked.val.diagram source.checked.property.diagram_well_formed =
          some sourceBody)
    (sourceFocus : CompiledFocus sourceBody (spliceSite input frameEq))
    (materialWireMap : Fin (endpointCall (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).outerContext.length →
      Fin sourceFocus.endpointCall.fullContext.length)
    (materialGet : ∀ index,
      sourceFocus.endpointCall.fullContext.get (materialWireMap index) =
        Fin.cast (congrArg (fun checked : Checked => checked.val.wireCount)
          frameEq) (input.attachment (({} : input.PlugLayout).exposedPosition
            (Fin.cast (congrArg List.length (patternTerminal_outerContext input
              (spliceRaw_admissible success).terminal_body)) index))))
    (relationMap : RelationRenaming
      (endpointCall (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).rels sourceFocus.endpointCall.rels)
    (relationLookup : ∀ {relationArity}
      (relation : RelVar (endpointCall (State.ofOpen input.pattern)
        input.binderSpine.bodyContainer).rels relationArity),
      sourceFocus.endpointCall.binders
          (Fin.cast (congrArg (fun checked : Checked =>
            checked.val.regionCount) frameEq) (input.binderTarget
              (terminalRelationProxyEquiv input relation.index))) =
        some ⟨relationArity, relationMap relation⟩) :
    ContextReplacement
      (source.checked.elaborate.castArity source.boundary_length)
      (receipt.target.checked.elaborate.castArity
        receipt.target.boundary_length)
      sourceFocus.endpointCall.outerContext.length
      sourceFocus.endpointCall.rels := by
  rcases input with ⟨frame, pattern, site, attachment, binderSpine,
    binderTarget⟩
  dsimp only at frameEq
  subst frame
  let input : Splice.Input := {
    frame := source.diagram
    pattern := pattern
    site := site
    attachment := attachment
    binderSpine := binderSpine
    binderTarget := binderTarget
  }
  let layout : input.PlugLayout := {}
  have admissible : input.Admissible := spliceRaw_admissible success
  have targetWf : layout.plugRaw.WellFormed := by
    rw [← spliceRaw_result_plugRaw success]
    exact operation.result.property
  let sourceCall : CompilerCall source.checked.val.diagram :=
    .root source.checked.val.exposedWires source.checked.val.hiddenWires
  have sourceBoundaryEq : spliceSourceBoundary source input rfl =
      source.checked.val.boundary := by
    simp [spliceSourceBoundary, input]
  let targetOpen := layout.outputOpenRoot input
    source.checked.val.boundary
  have frameExposedEq : (Splice.Input.PlugLayout.frameOpen input
      source.checked.val.boundary).exposedWires =
        source.checked.val.exposedWires := rfl
  have frameRootEq : (Splice.Input.PlugLayout.frameOpen input
      source.checked.val.boundary).rootWires =
        source.checked.val.rootWires := rfl
  have packedOpen : receipt.target.checked.val = targetOpen := by
    simpa [input, layout, targetOpen, sourceBoundaryEq] using
      spliceRaw_packed_open (source := source) (input := input) rfl success packed
  have targetOpenWf : targetOpen.WellFormed := by
    rw [← packedOpen]
    exact receipt.target.checked.property
  let targetChecked : CheckedOpen := ⟨targetOpen, targetOpenWf⟩
  have targetBoundaryLength : targetOpen.boundary.length = arity := by
    rw [← packedOpen]
    exact receipt.target.boundary_length
  let targetState : State arity := ⟨targetChecked, targetBoundaryLength⟩
  have packedChecked : receipt.target.checked = targetChecked :=
    Subtype.ext packedOpen
  have packedState : receipt.target = targetState :=
    state_eq_of_checked packedChecked
  let targetOuter : WireContext layout.plugRaw := targetOpen.exposedWires
  let targetLocal : WireContext layout.plugRaw := targetOpen.hiddenWires
  have outerEq : targetOuter =
      sourceCall.outerContext.map layout.frameWireMap := by
    have exposed := layout.outputOpenRoot_exposedWires consistent
      source.checked.val.boundary
    rw [frameExposedEq] at exposed
    simpa [targetOuter, targetOpen, sourceCall] using exposed
  have fullEq : targetOuter ++ targetLocal =
      sourceCall.fullContext.map layout.frameWireMap ++
        (if sourceCall.origin = input.site then
          (endpointCall (State.ofOpen input.pattern)
            input.binderSpine.bodyContainer).localContext.map
              layout.patternWireMap else []) := by
    have rootWires := layout.outputOpenRoot_rootWires consistent
      admissible.terminal_body source.checked.val.boundary
    rw [frameRootEq] at rootWires
    rw [layout.bodyLocalWires_eq_endpointLocalMap] at rootWires
    simpa [targetOuter, targetLocal, targetOpen, sourceCall,
      CompilerCall.fullContext,
      OpenDiagram.rootWires] using rootWires
  let frame : layout.FrameEvidence targetWf sourceCall targetOuter targetLocal
      BinderContext.empty sourceBody := {
    outerEq := outerEq
    fullEq := fullEq
    targetLocalCall := rfl
    sourceExact := by
      simpa [sourceCall, CompilerCall.fullContext, OpenDiagram.rootWires] using
        openRootWires_exact source.checked.property
    sourceCovers := by
      simpa [sourceCall] using BinderContext.empty_covers_root
        source.checked.property.diagram_well_formed
    sourceEnumeration := by
      simpa [sourceCall] using BinderContext.Enumeration.empty
        source.checked.val.diagram
    targetExact := by
      simpa [targetOuter, targetLocal, targetOpen, OpenDiagram.rootWires] using
        openRootWires_exact targetOpenWf
    frameBindersMapped := by intro binder; rfl
    sourceCompiled := by
      simpa [sourceCall] using sourceCompiled
  }
  let after := Splice.Input.PlugLayout.spliceEndpointAfter input
    sourceFocus.endpointCall
    sourceFocus.endpoint materialWireMap relationMap
  let endpointInput : layout.EndpointGraftInput admissible
      sourceFocus.endpointCall sourceFocus.endpoint := {
    relationMap := relationMap
    hostLookup := relationLookup
    materialWireMap := materialWireMap
    materialGet := materialGet
    after := after
    afterEq := rfl
  }
  let result := layout.compileAlongZipper consistent admissible targetWf
    sourceFocus.zipper rfl endpointInput targetOuter targetLocal BinderContext.empty
      frame
  have targetBodyEq : result.targetBody.erase =
      targetChecked.compilation.erase := by
    have resultCompiled : compileRoot? layout.plugRaw targetWf targetOuter
        targetLocal = some result.targetBody := by
      simpa [sourceCall, Splice.Input.PlugLayout.frameTargetCall] using
        result.targetCompiled
    have canonicalCompiled := targetChecked.compilation_computation
    have same : result.targetBody = targetChecked.compilation := by
      apply Option.some.inj
      exact resultCompiled.symm.trans (by
        simpa [targetChecked, targetOuter, targetLocal, targetOpen] using
          canonicalCompiled)
    exact congrArg CompiledRegion.erase same
  let interface := source.checked.elaborate.castArity source.boundary_length
  let replacementContext : DiagramContext interface.externalClasses
      sourceFocus.endpointCall.outerContext.length []
      sourceFocus.endpointCall.rels :=
    sourceFocus.zipper.context
  let interfaceWire :=
    layout.canonicalOuterWire sourceCall targetOuter outerEq
  have sourceBodyEq : sourceBody.erase = source.checked.compilation.erase := by
    have same : sourceBody = source.checked.compilation := by
      apply Option.some.inj
      exact sourceCompiled.symm.trans (by
        simpa using source.checked.compilation_computation)
    exact congrArg CompiledRegion.erase same
  have sourceRebuild : replacementContext.fill sourceFocus.endpoint.erase =
      interface.body := by
    simpa [replacementContext, interface] using
      sourceFocus.zipper.intrinsic.rebuild.trans sourceBodyEq
  let targetInterface :=
    targetChecked.elaborate.castArity targetBoundaryLength
  have frameTargetErase_eq :
      layout.frameTargetErase sourceCall targetOuter targetLocal
          BinderContext.empty result.targetBody = result.targetBody.erase := by
    rfl
  have targetRebuild : result.targetContext.fill result.targetSite =
      targetInterface.body := by
    exact result.targetRebuild.trans <|
      frameTargetErase_eq.trans <| targetBodyEq.trans rfl
  have boundaryAligned : forall position,
      interfaceWire (targetInterface.boundary position) =
        interface.boundary position := by
    intro position
    apply Fin.ext
    let sourcePosition := Fin.cast source.boundary_length.symm position
    have boundaryEq := layout.canonicalOuterWire_boundaryClass
      source.checked.val.boundary source.checked.val.hiddenWires
      outerEq sourcePosition
    have targetPositionEq :
        Fin.cast (List.length_map
          (layout.frameWire ∘ input.quotientWire)).symm
            sourcePosition = Fin.cast targetBoundaryLength.symm position := by
      apply Fin.ext
      rfl
    have boundaryEq' :
        layout.canonicalOuterWire sourceCall targetOuter outerEq
            (targetOpen.boundaryClass
              (Fin.cast targetBoundaryLength.symm position)) =
          source.checked.val.boundaryClass sourcePosition := by
      rw [← targetPositionEq]
      exact boundaryEq
    simpa [targetInterface, targetChecked, targetOuter, targetOpen,
        interface, FiniteEquiv.finCast, FiniteEquiv.trans,
        sourcePosition] using congrArg Fin.val boundaryEq'
  let rawReplacement : ContextReplacement
      (source.checked.elaborate.castArity source.boundary_length)
      (targetState.checked.elaborate.castArity
        targetState.boundary_length)
      sourceFocus.endpointCall.outerContext.length
      sourceFocus.endpointCall.rels :=
    ContextReplacement.ofContextAlignment interface targetInterface
      replacementContext result.targetContext sourceFocus.endpoint.erase
      endpointInput.after result.targetSite interfaceWire result.holeWire
      sourceRebuild targetRebuild result.alignment result.endpointIso
      boundaryAligned
  let targetRebase : OpenDiagramIso
      (targetState.checked.elaborate.castArity targetState.boundary_length)
      (receipt.target.checked.elaborate.castArity
        receipt.target.boundary_length) :=
    state_elaboration_iso packedState.symm
  exact ContextReplacement.iso
    (OpenDiagramIso.refl _) rawReplacement targetRebase

/-- A successful concrete splice is one canonical contextual replacement.
The canonical source compiler result and focus are merely the ordinary
instantiation of `spliceFromFocus`. -/
noncomputable def splice
    {arity : Nat} {source : State arity} (input : Splice.Input)
    (frameEq : input.frame = source.diagram)
    {operation : OperationReceipt input.frame}
    (success : spliceRaw input = .ok operation)
    {receipt : Receipt source}
    (packed : (operation.castInput frameEq).toReceipt source = some receipt)
    (consistent : input.AttachmentConsistent) :
    ContextReplacement
      (source.checked.elaborate.castArity source.boundary_length)
      (receipt.target.checked.elaborate.castArity
        receipt.target.boundary_length)
      (endpointCall source (spliceSite input frameEq)).outerContext.length
      (endpointCall source (spliceSite input frameEq)).rels :=
  spliceFromFocus input frameEq success packed consistent
    source.checked.compilation (by
      simpa using source.checked.compilation_computation)
    (focus source (spliceSite input frameEq))
    (spliceWireMap input frameEq (spliceRaw_admissible success) {})
    (by
      intro index
      exact spliceWireMap_get input frameEq (spliceRaw_admissible success) {}
        index)
    (spliceRelationMap input frameEq (spliceRaw_admissible success))
    (by
      intro relationArity relation
      exact spliceRelationMap_lookup input frameEq
        (spliceRaw_admissible success) relation)

@[simp] theorem splice_interface_externalClasses
    {arity : Nat} {source : State arity} (input : Splice.Input)
    (frameEq : input.frame = source.diagram)
    {operation : OperationReceipt input.frame}
    (success : spliceRaw input = .ok operation)
    {receipt : Receipt source}
    (packed : (operation.castInput frameEq).toReceipt source = some receipt)
    (consistent : input.AttachmentConsistent) :
    (splice input frameEq success packed consistent).interface.externalClasses =
      source.checked.val.exposedWires.length := by
  rcases input with ⟨frame, pattern, site, attachment, binderSpine,
    binderTarget⟩
  dsimp only at frameEq
  cases frameEq
  simp [splice, spliceFromFocus, ContextReplacement.iso,
    ContextReplacement.ofContextAlignment]

/-- The source focus context, transported only across the existential indices
of `ContextReplacement`. -/
noncomputable def spliceContext
    {arity : Nat} {source : State arity} (input : Splice.Input)
    (frameEq : input.frame = source.diagram)
    {operation : OperationReceipt input.frame}
    (success : spliceRaw input = .ok operation)
    {receipt : Receipt source}
    (packed : (operation.castInput frameEq).toReceipt source = some receipt)
    (consistent : input.AttachmentConsistent) :
    DiagramContext
      (splice input frameEq success packed consistent).interface.externalClasses
      (endpointCall source (spliceSite input frameEq)).outerContext.length []
      (endpointCall source (spliceSite input frameEq)).rels := by
  rw [splice_interface_externalClasses]
  exact context source (spliceSite input frameEq)

/-- The original focused body at the splice's existential hole indices. -/
noncomputable def spliceBefore
    {arity : Nat} {source : State arity} (input : Splice.Input)
    (frameEq : input.frame = source.diagram)
    {operation : OperationReceipt input.frame}
    (_success : spliceRaw input = .ok operation)
    {receipt : Receipt source}
    (_packed : (operation.castInput frameEq).toReceipt source = some receipt)
    (_consistent : input.AttachmentConsistent) :
    Region (endpointCall source (spliceSite input frameEq)).outerContext.length
      (endpointCall source (spliceSite input frameEq)).rels := by
  exact body source (spliceSite input frameEq)

/-- The source-derived local splice body at the replacement's existential
hole indices. -/
noncomputable def spliceAfterBody
    {arity : Nat} {source : State arity} (input : Splice.Input)
    (frameEq : input.frame = source.diagram)
    {operation : OperationReceipt input.frame}
    (success : spliceRaw input = .ok operation)
    {receipt : Receipt source}
    (_packed : (operation.castInput frameEq).toReceipt source = some receipt)
    (_consistent : input.AttachmentConsistent) :
    Region (endpointCall source (spliceSite input frameEq)).outerContext.length
      (endpointCall source (spliceSite input frameEq)).rels := by
  rcases input with ⟨frame, pattern, site, attachment, binderSpine,
    binderTarget⟩
  dsimp only at frameEq
  subst frame
  let input : Splice.Input := {
    frame := source.diagram
    pattern := pattern
    site := site
    attachment := attachment
    binderSpine := binderSpine
    binderTarget := binderTarget
  }
  let layout : input.PlugLayout := {}
  let admissible : input.Admissible := spliceRaw_admissible success
  exact spliceAfter input rfl admissible layout

@[simp] theorem splice_context
    {arity : Nat} {source : State arity} (input : Splice.Input)
    (frameEq : input.frame = source.diagram)
    {operation : OperationReceipt input.frame}
    (success : spliceRaw input = .ok operation)
    {receipt : Receipt source}
    (packed : (operation.castInput frameEq).toReceipt source = some receipt)
    (consistent : input.AttachmentConsistent) :
    (splice input frameEq success packed consistent).context =
      spliceContext input frameEq success packed consistent := by
  rcases input with ⟨frame, pattern, site, attachment, binderSpine,
    binderTarget⟩
  dsimp only at frameEq
  cases frameEq
  simp [spliceContext, splice, spliceFromFocus, spliceSite]
  exact (cast_eq _ _).symm

theorem splice_context_cutDepth
    {arity : Nat} {source : State arity} (input : Splice.Input)
    (frameEq : input.frame = source.diagram)
    {operation : OperationReceipt input.frame}
    (success : spliceRaw input = .ok operation)
    {receipt : Receipt source}
    (packed : (operation.castInput frameEq).toReceipt source = some receipt)
    (consistent : input.AttachmentConsistent) :
    (splice input frameEq success packed consistent).context.cutDepth =
      concreteCutDepth source.checked.val.diagram
        (spliceSite input frameEq) := by
  rcases input with ⟨frame, pattern, site, attachment, binderSpine,
    binderTarget⟩
  dsimp only at frameEq
  cases frameEq
  simpa [splice_context, spliceContext, spliceSite] using
    context_cutDepth source site

@[simp] theorem splice_before
    {arity : Nat} {source : State arity} (input : Splice.Input)
    (frameEq : input.frame = source.diagram)
    {operation : OperationReceipt input.frame}
    (success : spliceRaw input = .ok operation)
    {receipt : Receipt source}
    (packed : (operation.castInput frameEq).toReceipt source = some receipt)
    (consistent : input.AttachmentConsistent) :
    (splice input frameEq success packed consistent).before =
      spliceBefore input frameEq success packed consistent := by
  rcases input with ⟨frame, pattern, site, attachment, binderSpine,
    binderTarget⟩
  dsimp only at frameEq
  cases frameEq
  simp [spliceBefore, splice, spliceFromFocus, spliceSite]
  congr 1

@[simp] theorem splice_after
    {arity : Nat} {source : State arity} (input : Splice.Input)
    (frameEq : input.frame = source.diagram)
    {operation : OperationReceipt input.frame}
    (success : spliceRaw input = .ok operation)
    {receipt : Receipt source}
    (packed : (operation.castInput frameEq).toReceipt source = some receipt)
    (consistent : input.AttachmentConsistent) :
    (splice input frameEq success packed consistent).after =
      spliceAfterBody input frameEq success packed consistent := by
  rcases input with ⟨frame, pattern, site, attachment, binderSpine,
    binderTarget⟩
  dsimp only at frameEq
  cases frameEq
  simp [spliceAfterBody, splice, spliceFromFocus, spliceSite,
    ContextReplacement.iso, spliceAfter,
    Splice.Input.PlugLayout.spliceEndpointAfter, endpointCall, endpoint,
    directItems]
  congr 1

end Elaboration.CompiledSite

end VisualProof.Concrete
