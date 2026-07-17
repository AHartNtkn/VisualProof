import VisualProof.Rule.Soundness.Iteration.CoalescedRoute

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

/-- Equal lexical relation contexts and equal binder states make lookup at a
fixed concrete binder determine the transported relation variable uniquely. -/
theorem relationRenamingOfEq_eq_of_binderLookup
    {diagram : ConcreteDiagram}
    {sourceRels targetRels : RelCtx}
    (hrels : sourceRels = targetRels)
    (sourceBinders : ConcreteElaboration.BinderContext diagram sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext diagram targetRels)
    (hbinders : HEq sourceBinders targetBinders)
    (binder : Fin diagram.regionCount)
    {arity : Nat} (sourceRelation : RelVar sourceRels arity)
    (targetRelation : RelVar targetRels arity)
    (sourceLookup : sourceBinders binder = some ⟨arity, sourceRelation⟩)
    (targetLookup : targetBinders binder = some ⟨arity, targetRelation⟩) :
    Splice.Input.relationRenamingOfEq hrels sourceRelation =
      targetRelation := by
  subst targetRels
  have bindersEq : targetBinders = sourceBinders :=
    (eq_of_heq hbinders).symm
  rw [bindersEq, sourceLookup] at targetLookup
  have sigmaEq := Option.some.inj targetLookup
  simpa [Splice.Input.relationRenamingOfEq] using
    (eq_of_heq (Sigma.ext_iff.mp sigmaEq).2)

/-- At one concrete target, equality of the represented wire forces the
executable full-context index to be the inherited index transported from the
retained route. -/
theorem compiledRouteTerminal_hostIndex_eq
    (checked : CheckedDiagram signature)
    {start target : Fin checked.val.regionCount}
    {startOuter : Nat} {startRels : RelCtx}
    {startBody : Region signature startOuter startRels}
    (startLeaf : Splice.Region.ContextPath.CompilerLeaf checked.val start
      (.here startBody))
    (compiledItems : ItemSeq signature
      (startLeaf.inheritedWires.extend start).length startRels)
    {routePath : List Nat}
    (route : Splice.RegionRoute checked.val start target routePath)
    {compiledPath : List Nat}
    {routeWitness : Region.ContextPath (Region.mk 0 compiledItems) compiledPath}
    (terminal : CompiledRouteTerminal checked startLeaf compiledItems route
      compiledPath routeWitness)
    {hostOuter : Nat} {hostRels : RelCtx}
    {hostBody : Region signature hostOuter hostRels}
    {hostPath : List Nat}
    (hostWitness : Region.ContextPath hostBody hostPath)
    (hostLeaf : Splice.Region.ContextPath.CompilerLeaf checked.val target
      hostWitness)
    (sourceIndex : Fin (startLeaf.inheritedWires.extend start).length)
    (hostIndex : Fin (hostLeaf.inheritedWires.extend target).length)
    (sameWire : (hostLeaf.inheritedWires.extend target).get hostIndex =
      (startLeaf.inheritedWires.extend start).get sourceIndex) :
    hostIndex = hostLeaf.inheritedWires.outerIndex target
      (Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
        routeWitness terminal.leaf hostWitness hostLeaf
        (terminal.inheritedIndex sourceIndex)) := by
  let inherited :=
    Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
      routeWitness terminal.leaf hostWitness hostLeaf
        (terminal.inheritedIndex sourceIndex)
  apply Fin.ext
  apply (List.getElem_inj hostLeaf.wiresExact.nodup).mp
  change (hostLeaf.inheritedWires.extend target).get hostIndex =
    (hostLeaf.inheritedWires.extend target).get
      (hostLeaf.inheritedWires.outerIndex target inherited)
  calc
    _ = (startLeaf.inheritedWires.extend start).get sourceIndex := sameWire
    _ = terminal.leaf.inheritedWires.get
          (terminal.inheritedIndex sourceIndex) :=
      (terminal.inheritedIndex_get sourceIndex).symm
    _ = hostLeaf.inheritedWires.get inherited := by
      exact (Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv_spec
        routeWitness terminal.leaf hostWitness hostLeaf
        (terminal.inheritedIndex sourceIndex)).symm
    _ = _ := (ConcreteElaboration.WireContext.extend_outer
      hostLeaf.inheritedWires target inherited).symm

/-- Iteration's exposed pattern attachment is exactly the quotient of the
host wire from which that extracted boundary wire originated. -/
theorem iterationExposedAttachment_eq_fragmentOrigin
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (external : Fin
      (iterationInput input selection target).pattern.val.exposedWires.length) :
    let layout : FragmentLayout input.val selection := {}
    let spliceInput := iterationInput input selection target
    spliceInput.plugLayout.exposedAttachment external =
      spliceInput.quotientWire
        (input.val.fragmentWireOrigin selection layout
          (spliceInput.pattern.val.exposedWires.get external)) := by
  dsimp only
  let layout : FragmentLayout input.val selection := {}
  let spliceInput := iterationInput input selection target
  let position := spliceInput.plugLayout.exposedPosition external
  have exposedAtPosition :=
    spliceInput.plugLayout.exposedPosition_sound external
  change spliceInput.quotientWire
      (selection.touchingWires.get
        (Fin.cast (input.val.extractBoundaryRaw_length selection layout)
          position)) = _
  have boundaryGet : spliceInput.pattern.val.boundary.get position =
      layout.boundaryWire
        (Fin.cast (input.val.extractBoundaryRaw_length selection layout)
          position) := by
    simp only [spliceInput, iterationInput, ConcreteDiagram.extractOpenRaw,
      ConcreteDiagram.extractBoundaryRaw, List.get_eq_getElem,
      List.getElem_ofFn]
    apply Fin.ext
    rfl
  rw [← exposedAtPosition, boundaryGet]
  apply congrArg spliceInput.quotientWire
  simp [ConcreteDiagram.fragmentWireOrigin, FragmentLayout.boundaryWire,
    FragmentLayout.internalWireCount]

/-- In the empty-spine branch, the executable exposed-wire substitution and
the extraction context relation select the same coalesced anchor wire. -/
theorem iterationRootWire_sameWire
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (patternIndex : Fin
      (iterationInput input selection target).pattern.val.exposedWires.length)
    (hostIndex : Fin
      (((iterationCoalescedAnchorView input selection target hadmissible
        ).compilerLeaf.inheritedWires.extend selection.val.anchor).map
          (iterationCoalescedFrameIso input selection target).wires).length)
    (related : (extractionContextRelation input selection
      ({} : FragmentLayout input.val selection)
      (iterationInput input selection target).pattern.val.exposedWires
      (((iterationCoalescedAnchorView input selection target hadmissible
        ).compilerLeaf.inheritedWires.extend selection.val.anchor).map
          (iterationCoalescedFrameIso input selection target).wires)
      ).Rel patternIndex hostIndex) :
    let spliceInput := iterationInput input selection target
    let anchorView := iterationCoalescedAnchorView input selection target
      hadmissible
    let sourceContext :=
      anchorView.compilerLeaf.inheritedWires.extend selection.val.anchor
    let iso := iterationCoalescedFrameIso input selection target
    let targetContext := sourceContext.map iso.wires
    let wireEquiv : FiniteEquiv (Fin sourceContext.length)
        (Fin targetContext.length) :=
      FiniteEquiv.finCast (List.length_map iso.wires).symm
    let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
    (host.compilerLeaf.inheritedWires.extend target).get
        (spliceInput.plugLayout.exposedWireRenaming hadmissible host
          patternIndex) =
      sourceContext.get (wireEquiv.symm hostIndex) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let layout : FragmentLayout input.val selection := {}
  let anchorView := iterationCoalescedAnchorView input selection target
    hadmissible
  let sourceContext :=
    anchorView.compilerLeaf.inheritedWires.extend selection.val.anchor
  let iso := iterationCoalescedFrameIso input selection target
  let targetContext := sourceContext.map iso.wires
  let wireEquiv : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length) :=
    FiniteEquiv.finCast (List.length_map iso.wires).symm
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  have actualGet := spliceInput.plugLayout.exposedWireRenaming_spec
    hadmissible host patternIndex
  have attachmentOrigin := iterationExposedAttachment_eq_fragmentOrigin input
    selection target patternIndex
  dsimp only at attachmentOrigin
  have originEq : input.val.fragmentWireOrigin selection layout
      (spliceInput.pattern.val.exposedWires.get patternIndex) =
        targetContext.get hostIndex := related
  have targetGet : targetContext.get hostIndex =
      iso.wires (sourceContext.get (wireEquiv.symm hostIndex)) := by
    simp only [targetContext, List.get_eq_getElem, List.getElem_map]
    apply congrArg iso.wires
    congr 1
  have quotientSource : spliceInput.quotientWire
      (targetContext.get hostIndex) =
        sourceContext.get (wireEquiv.symm hostIndex) := by
    apply iso.wires.injective
    change iterationQuotientWireEquiv input selection target
        (spliceInput.quotientWire (targetContext.get hostIndex)) =
      iterationQuotientWireEquiv input selection target
        (sourceContext.get (wireEquiv.symm hostIndex))
    rw [iterationQuotientWireEquiv_quotientWire]
    exact targetGet
  exact actualGet.trans
    (attachmentOrigin.trans
      ((congrArg spliceInput.quotientWire originEq).trans quotientSource))

/-- The executable empty-spine wire map factors through the retained route's
terminal inherited-wire map. -/
theorem iterationRootWireFactor
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    {keptItems : ItemSeq signature
      ((iterationCoalescedAnchorView input selection target hadmissible)
        |>.compilerLeaf.inheritedWires.extend selection.val.anchor).length
      (iterationCoalescedAnchorView input selection target hadmissible
        ).focus.holeRels}
    {path : List Nat}
    (route : Splice.RegionRoute
      (iterationInput input selection target).coalesceFrameRaw
      selection.val.anchor target path)
    {compiledPath : List Nat}
    {witness : Region.ContextPath (Region.mk 0 keptItems) compiledPath}
    (terminal : CompiledRouteTerminal
      ((iterationInput input selection target).coalesceFrame hadmissible)
      (Splice.Region.ContextPath.CompilerLeaf.hereOfItemsComputation
        (iterationInput input selection target).coalesceFrameRaw
        selection.val.anchor
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.inheritedWires
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.binders
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.fuel
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.items
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.itemsComputation
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.wiresExact
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.bindersCover
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.binderEnumeration)
      keptItems route compiledPath witness)
    (patternIndex : Fin
      (iterationInput input selection target).pattern.val.exposedWires.length)
    (hostIndex : Fin
      (((iterationCoalescedAnchorView input selection target hadmissible
        ).compilerLeaf.inheritedWires.extend selection.val.anchor).map
          (iterationCoalescedFrameIso input selection target).wires).length)
    (related : (extractionContextRelation input selection
      ({} : FragmentLayout input.val selection)
      (iterationInput input selection target).pattern.val.exposedWires
      (((iterationCoalescedAnchorView input selection target hadmissible
        ).compilerLeaf.inheritedWires.extend selection.val.anchor).map
          (iterationCoalescedFrameIso input selection target).wires)
      ).Rel patternIndex hostIndex) :
    let spliceInput := iterationInput input selection target
    let anchorView := iterationCoalescedAnchorView input selection target
      hadmissible
    let sourceContext :=
      anchorView.compilerLeaf.inheritedWires.extend selection.val.anchor
    let iso := iterationCoalescedFrameIso input selection target
    let targetContext := sourceContext.map iso.wires
    let wireEquiv : FiniteEquiv (Fin sourceContext.length)
        (Fin targetContext.length) :=
      FiniteEquiv.finCast (List.length_map iso.wires).symm
    let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
    spliceInput.plugLayout.exposedWireRenaming hadmissible host patternIndex =
      host.compilerLeaf.inheritedWires.outerIndex target
        (Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
          witness terminal.leaf host.intrinsicPath host.compilerLeaf
          (terminal.inheritedIndex (wireEquiv.symm hostIndex))) := by
  dsimp only
  apply compiledRouteTerminal_hostIndex_eq
    ((iterationInput input selection target).coalesceFrame hadmissible)
    (Splice.Region.ContextPath.CompilerLeaf.hereOfItemsComputation
      (iterationInput input selection target).coalesceFrameRaw
      selection.val.anchor
      (iterationCoalescedAnchorView input selection target hadmissible
        ).compilerLeaf.inheritedWires
      (iterationCoalescedAnchorView input selection target hadmissible
        ).compilerLeaf.binders
      (iterationCoalescedAnchorView input selection target hadmissible
        ).compilerLeaf.fuel
      (iterationCoalescedAnchorView input selection target hadmissible
        ).compilerLeaf.items
      (iterationCoalescedAnchorView input selection target hadmissible
        ).compilerLeaf.itemsComputation
      (iterationCoalescedAnchorView input selection target hadmissible
        ).compilerLeaf.wiresExact
      (iterationCoalescedAnchorView input selection target hadmissible
        ).compilerLeaf.bindersCover
      (iterationCoalescedAnchorView input selection target hadmissible
        ).compilerLeaf.binderEnumeration)
    keptItems route terminal
    (Splice.Input.compiledSpliceHostView
      (iterationInput input selection target) hadmissible).intrinsicPath
    (Splice.Input.compiledSpliceHostView
      (iterationInput input selection target) hadmissible).compilerLeaf
    ((FiniteEquiv.finCast (List.length_map
      (iterationCoalescedFrameIso input selection target).wires).symm).symm
        hostIndex)
    ((iterationInput input selection target).plugLayout.exposedWireRenaming
      hadmissible
      (Splice.Input.compiledSpliceHostView
        (iterationInput input selection target) hadmissible) patternIndex)
  exact iterationRootWire_sameWire input selection target hadmissible
    patternIndex hostIndex related

/-- The concrete wire selected by the executable terminal wire map is the
same coalesced anchor wire selected by extraction's context relation. -/
theorem iterationTerminalWire_sameWire
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    (patternIndex : Fin
      (Splice.Input.compiledSpliceTerminalView
        (iterationInput input selection target) hnonempty
      ).leaf.inheritedWires.length)
    (hostIndex : Fin
      (((iterationCoalescedAnchorView input selection target hadmissible
        ).compilerLeaf.inheritedWires.extend selection.val.anchor).map
          (iterationCoalescedFrameIso input selection target).wires).length)
    (related : (extractionContextRelation input selection
      ({} : FragmentLayout input.val selection)
      (Splice.Input.compiledSpliceTerminalView
        (iterationInput input selection target) hnonempty
      ).leaf.inheritedWires
      (((iterationCoalescedAnchorView input selection target hadmissible
        ).compilerLeaf.inheritedWires.extend selection.val.anchor).map
          (iterationCoalescedFrameIso input selection target).wires)
      ).Rel patternIndex hostIndex) :
    let spliceInput := iterationInput input selection target
    let layout : FragmentLayout input.val selection := {}
    let anchorView := iterationCoalescedAnchorView input selection target
      hadmissible
    let sourceContext :=
      anchorView.compilerLeaf.inheritedWires.extend selection.val.anchor
    let iso := iterationCoalescedFrameIso input selection target
    let targetContext := sourceContext.map iso.wires
    let wireEquiv : FiniteEquiv (Fin sourceContext.length)
        (Fin targetContext.length) :=
      FiniteEquiv.finCast (List.length_map iso.wires).symm
    let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
    let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
    (host.compilerLeaf.inheritedWires.extend target).get
        (spliceInput.plugLayout.bodyTerminalWireRenaming hadmissible host
          pattern.witness pattern.leaf hnonempty patternIndex) =
      sourceContext.get (wireEquiv.symm hostIndex) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let layout : FragmentLayout input.val selection := {}
  let anchorView := iterationCoalescedAnchorView input selection target
    hadmissible
  let sourceContext :=
    anchorView.compilerLeaf.inheritedWires.extend selection.val.anchor
  let iso := iterationCoalescedFrameIso input selection target
  let targetContext := sourceContext.map iso.wires
  let wireEquiv : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length) :=
    FiniteEquiv.finCast (List.length_map iso.wires).symm
  let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  let patternWire := pattern.leaf.inheritedWires.get patternIndex
  let exposed := Splice.Input.PlugLayout.exposedWireIndex spliceInput
    patternWire
    ((spliceInput.plugLayout.terminalBody_inherited_mem_iff_exposed
      pattern.witness pattern.leaf hnonempty patternWire).1
      (List.get_mem _ patternIndex))
  have actualGet := spliceInput.plugLayout.bodyTerminalWireRenaming_spec
    hadmissible host pattern.witness pattern.leaf hnonempty patternIndex
  have attachmentOrigin :=
    iterationExposedAttachment_eq_fragmentOrigin input selection target exposed
  dsimp only at attachmentOrigin
  have exposedGet : spliceInput.pattern.val.exposedWires.get exposed =
      patternWire := Splice.Input.PlugLayout.exposedWireIndex_get
        spliceInput patternWire _
  rw [exposedGet] at attachmentOrigin
  have originEq : input.val.fragmentWireOrigin selection layout patternWire =
      targetContext.get hostIndex := related
  have targetGet : targetContext.get hostIndex =
      iso.wires (sourceContext.get (wireEquiv.symm hostIndex)) := by
    simp only [targetContext, List.get_eq_getElem, List.getElem_map]
    apply congrArg iso.wires
    congr 1
  have quotientSource : spliceInput.quotientWire
      (targetContext.get hostIndex) =
        sourceContext.get (wireEquiv.symm hostIndex) := by
    apply iso.wires.injective
    change iterationQuotientWireEquiv input selection target
        (spliceInput.quotientWire (targetContext.get hostIndex)) =
      iterationQuotientWireEquiv input selection target
        (sourceContext.get (wireEquiv.symm hostIndex))
    rw [iterationQuotientWireEquiv_quotientWire]
    exact targetGet
  exact actualGet.trans
    (attachmentOrigin.trans
      ((congrArg spliceInput.quotientWire originEq).trans quotientSource))

/-- The extraction compiler and the splice compiler name the same concrete
host binder for every terminal pattern relation. -/
theorem iterationExtractionTerminalHostBinder_eq_terminalBinderTarget
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Splice.Region.ContextPath.CompilerLeaf
      (iterationInput input selection target).pattern.val.diagram
      (iterationInput input selection target).binderSpine.bodyContainer
      patternWitness)
    {arity : Nat}
    (relation : RelVar patternWitness.toFocus.holeRels arity) :
    let layout : FragmentLayout input.val selection := {}
    let spliceInput := iterationInput input selection target
    extractionTerminalHostBinder input selection layout patternLeaf.binders
        patternLeaf.binderEnumeration relation.index =
      spliceInput.plugLayout.terminalBinderTarget patternWitness patternLeaf
        hnonempty relation := by
  dsimp only
  let layout : FragmentLayout input.val selection := {}
  let spliceInput := iterationInput input selection target
  let extractionProxy := Classical.choose
    (extractionTerminalBinder_is_proxy input selection layout
      patternLeaf.binders patternLeaf.binderEnumeration relation.index)
  let terminalProxy := Classical.choose
    (spliceInput.plugLayout.terminalBodyBinder_is_proxy patternWitness
      patternLeaf hnonempty relation.index)
  have extractionProxySpec : patternLeaf.binderEnumeration.binder
      relation.index = layout.proxy extractionProxy :=
    extractionTerminalHostBinder_proxy input selection layout
      patternLeaf.binders patternLeaf.binderEnumeration relation.index
  have terminalProxySpec : patternLeaf.binderEnumeration.binder
      relation.index = layout.proxy terminalProxy := by
    simpa [spliceInput, iterationInput, layout] using
      (Classical.choose_spec
        (spliceInput.plugLayout.terminalBodyBinder_is_proxy patternWitness
          patternLeaf hnonempty relation.index))
  have proxyEq : extractionProxy = terminalProxy :=
    layout.proxy_injective (extractionProxySpec.symm.trans terminalProxySpec)
  unfold extractionTerminalHostBinder
  unfold Splice.Input.PlugLayout.terminalBinderTarget
  change layout.externalBinders.get extractionProxy =
    layout.externalBinders.get terminalProxy
  rw [proxyEq]

/-- The relation substitution used by the executable splice is exactly the
selected-anchor substitution transported down the retained route. -/
theorem iterationTerminalRelationFactor
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    {keptItems : ItemSeq signature
      ((iterationCoalescedAnchorView input selection target hadmissible)
        |>.compilerLeaf.inheritedWires.extend selection.val.anchor).length
      (iterationCoalescedAnchorView input selection target hadmissible
        ).focus.holeRels}
    {path : List Nat}
    (route : Splice.RegionRoute
      (iterationInput input selection target).coalesceFrameRaw
      selection.val.anchor target path)
    {compiledPath : List Nat}
    {witness : Region.ContextPath (Region.mk 0 keptItems) compiledPath}
    (terminal : CompiledRouteTerminal
      ((iterationInput input selection target).coalesceFrame hadmissible)
      (Splice.Region.ContextPath.CompilerLeaf.hereOfItemsComputation
        (iterationInput input selection target).coalesceFrameRaw
        selection.val.anchor
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.inheritedWires
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.binders
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.fuel
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.items
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.itemsComputation
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.wiresExact
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.bindersCover
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.binderEnumeration)
      keptItems route compiledPath witness)
    (hrels : witness.toFocus.holeRels =
      (Splice.Input.compiledSpliceHostView
        (iterationInput input selection target) hadmissible).focus.holeRels)
    (hbinders : HEq terminal.leaf.binders
      (Splice.Input.compiledSpliceHostView
        (iterationInput input selection target) hadmissible
      ).compilerLeaf.binders) :
    let spliceInput := iterationInput input selection target
    let layout : FragmentLayout input.val selection := {}
    let anchorView := iterationCoalescedAnchorView input selection target
      hadmissible
    let sourceLeaf := anchorView.compilerLeaf
    let iso := iterationCoalescedFrameIso input selection target
    let targetBinders : ConcreteElaboration.BinderContext input.val
        anchorView.focus.holeRels := fun binder => sourceLeaf.binders binder
    let targetCover : targetBinders.Covers selection.val.anchor :=
      sourceLeaf.bindersCover.mapIso iso (by intro binder; rfl)
    let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
    let binderWitness := ExtractionBinderWitness.terminal input selection layout
      pattern.leaf.binders pattern.leaf.binderEnumeration targetBinders
      targetCover
    let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
    ∀ {arity : Nat}
      (relation : RelVar pattern.witness.toFocus.holeRels arity),
      spliceInput.plugLayout.coalescedTerminalRelationRenaming hadmissible
          host.intrinsicPath host.compilerLeaf pattern.witness pattern.leaf
          hnonempty relation =
        Splice.Input.relationRenamingOfEq hrels
          (witness.toFocus.context.outerRelation
            (binderWitness.relationMap relation)) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let layout : FragmentLayout input.val selection := {}
  let anchorView := iterationCoalescedAnchorView input selection target
    hadmissible
  let sourceLeaf := anchorView.compilerLeaf
  let iso := iterationCoalescedFrameIso input selection target
  let targetBinders : ConcreteElaboration.BinderContext input.val
      anchorView.focus.holeRels := fun binder => sourceLeaf.binders binder
  have binderAgreement : ConcreteElaboration.BinderContextsAgree iso
      sourceLeaf.binders targetBinders := by
    intro binder
    rfl
  let targetCover : targetBinders.Covers selection.val.anchor :=
    sourceLeaf.bindersCover.mapIso iso binderAgreement
  let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
  let binderWitness := ExtractionBinderWitness.terminal input selection layout
    pattern.leaf.binders pattern.leaf.binderEnumeration targetBinders
    targetCover
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  intro arity relation
  let selectedRelation := binderWitness.relationMap relation
  let binder := extractionTerminalHostBinder input selection layout
    pattern.leaf.binders pattern.leaf.binderEnumeration relation.index
  have extractionLookup : sourceLeaf.binders binder =
      some ⟨arity, selectedRelation⟩ := by
    simpa [targetBinders, binderWitness, selectedRelation, binder,
      ExtractionBinderWitness.terminal] using
      (extractionTerminalRelationRenaming_lookup input selection layout
        pattern.leaf.binders pattern.leaf.binderEnumeration targetBinders
        targetCover relation)
  have owner : sourceLeaf.binderEnumeration.binder selectedRelation.index =
      binder := sourceLeaf.binderEnumeration.lookup_owner selectedRelation
        extractionLookup
  have routeLookup := terminal.binder_lookup_outerRelation selectedRelation
  change terminal.leaf.binders
      (sourceLeaf.binderEnumeration.binder selectedRelation.index) =
        some ⟨arity,
          witness.toFocus.context.outerRelation selectedRelation⟩
    at routeLookup
  rw [owner] at routeLookup
  have binderTargetEq :=
    iterationExtractionTerminalHostBinder_eq_terminalBinderTarget input
      selection target hnonempty pattern.witness pattern.leaf relation
  have hostLookup :=
    spliceInput.plugLayout.coalescedTerminalRelationRenaming_lookup
      hadmissible host.intrinsicPath host.compilerLeaf pattern.witness
      pattern.leaf hnonempty relation
  rw [← binderTargetEq] at hostLookup
  exact (relationRenamingOfEq_eq_of_binderLookup hrels terminal.leaf.binders
    host.compilerLeaf.binders hbinders binder
    (witness.toFocus.context.outerRelation selectedRelation)
    (spliceInput.plugLayout.coalescedTerminalRelationRenaming hadmissible
      host.intrinsicPath host.compilerLeaf pattern.witness pattern.leaf
      hnonempty relation) routeLookup hostLookup).symm

/-- The executable terminal wire index is the retained route's inherited
anchor index, transported to the canonical host leaf at the target. -/
theorem iterationTerminalWireFactor
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    {keptItems : ItemSeq signature
      ((iterationCoalescedAnchorView input selection target hadmissible)
        |>.compilerLeaf.inheritedWires.extend selection.val.anchor).length
      (iterationCoalescedAnchorView input selection target hadmissible
        ).focus.holeRels}
    {path : List Nat}
    (route : Splice.RegionRoute
      (iterationInput input selection target).coalesceFrameRaw
      selection.val.anchor target path)
    {compiledPath : List Nat}
    {witness : Region.ContextPath (Region.mk 0 keptItems) compiledPath}
    (terminal : CompiledRouteTerminal
      ((iterationInput input selection target).coalesceFrame hadmissible)
      (Splice.Region.ContextPath.CompilerLeaf.hereOfItemsComputation
        (iterationInput input selection target).coalesceFrameRaw
        selection.val.anchor
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.inheritedWires
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.binders
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.fuel
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.items
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.itemsComputation
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.wiresExact
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.bindersCover
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.binderEnumeration)
      keptItems route compiledPath witness)
    (patternIndex : Fin
      (Splice.Input.compiledSpliceTerminalView
        (iterationInput input selection target) hnonempty
      ).leaf.inheritedWires.length)
    (hostIndex : Fin
      (((iterationCoalescedAnchorView input selection target hadmissible
        ).compilerLeaf.inheritedWires.extend selection.val.anchor).map
          (iterationCoalescedFrameIso input selection target).wires).length)
    (related : (extractionContextRelation input selection
      ({} : FragmentLayout input.val selection)
      (Splice.Input.compiledSpliceTerminalView
        (iterationInput input selection target) hnonempty
      ).leaf.inheritedWires
      (((iterationCoalescedAnchorView input selection target hadmissible
        ).compilerLeaf.inheritedWires.extend selection.val.anchor).map
          (iterationCoalescedFrameIso input selection target).wires)
      ).Rel patternIndex hostIndex) :
    let spliceInput := iterationInput input selection target
    let anchorView := iterationCoalescedAnchorView input selection target
      hadmissible
    let sourceContext :=
      anchorView.compilerLeaf.inheritedWires.extend selection.val.anchor
    let iso := iterationCoalescedFrameIso input selection target
    let targetContext := sourceContext.map iso.wires
    let wireEquiv : FiniteEquiv (Fin sourceContext.length)
        (Fin targetContext.length) :=
      FiniteEquiv.finCast (List.length_map iso.wires).symm
    let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
    let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
    spliceInput.plugLayout.bodyTerminalWireRenaming hadmissible host
        pattern.witness pattern.leaf hnonempty patternIndex =
      host.compilerLeaf.inheritedWires.outerIndex target
        (Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
          witness terminal.leaf host.intrinsicPath host.compilerLeaf
          (terminal.inheritedIndex (wireEquiv.symm hostIndex))) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let anchorView := iterationCoalescedAnchorView input selection target
    hadmissible
  let sourceContext :=
    anchorView.compilerLeaf.inheritedWires.extend selection.val.anchor
  let iso := iterationCoalescedFrameIso input selection target
  let targetContext := sourceContext.map iso.wires
  let wireEquiv : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length) :=
    FiniteEquiv.finCast (List.length_map iso.wires).symm
  let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  have sameWire := iterationTerminalWire_sameWire input selection target
    hadmissible hnonempty patternIndex hostIndex related
  apply compiledRouteTerminal_hostIndex_eq
    (spliceInput.coalesceFrame hadmissible)
    (Splice.Region.ContextPath.CompilerLeaf.hereOfItemsComputation
      spliceInput.coalesceFrameRaw selection.val.anchor
      anchorView.compilerLeaf.inheritedWires anchorView.compilerLeaf.binders
      anchorView.compilerLeaf.fuel anchorView.compilerLeaf.items
      anchorView.compilerLeaf.itemsComputation anchorView.compilerLeaf.wiresExact
      anchorView.compilerLeaf.bindersCover
      anchorView.compilerLeaf.binderEnumeration)
    keptItems route terminal host.intrinsicPath host.compilerLeaf
    (wireEquiv.symm hostIndex)
    (spliceInput.plugLayout.bodyTerminalWireRenaming hadmissible host
      pattern.witness pattern.leaf hnonempty patternIndex)
  exact sameWire

end VisualProof.Rule.IterationSoundness
