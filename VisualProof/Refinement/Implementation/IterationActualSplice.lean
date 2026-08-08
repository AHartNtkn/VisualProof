import VisualProof.Refinement.Implementation.IterationMaterialIndex
import VisualProof.Diagram.RenamingIsomorphism

namespace VisualProof.Refinement.Implementation.IterationActualSplice

open VisualProof.Concrete
open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Refinement.Implementation.IterationRoute
open VisualProof.Refinement.Implementation.IterationTransport
open VisualProof.Refinement.Implementation.IterationMaterialIndex

noncomputable def iterationActualSpliceOfNonempty
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0) :
    let spliceInput := iterationInput input selection target
    let host := Concrete.Splice.Input.compiledSpliceHostView spliceInput hadmissible
    Region  host.focus.holeWires host.focus.holeRels :=
  let spliceInput := iterationInput input selection target
  let host := Concrete.Splice.Input.compiledSpliceHostView spliceInput hadmissible
  let pattern := Concrete.Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
  let targetLocal :=
    (Concrete.Elaboration.exactScopeWires spliceInput.coalesceFrameRaw
      spliceInput.site).length
  let targetLength :
      (host.compilerLeaf.inheritedWires.extend spliceInput.site).length =
        host.focus.holeWires + targetLocal :=
    (Concrete.Elaboration.WireContext.length_extend
      host.compilerLeaf.inheritedWires spliceInput.site).trans
      (congrArg (fun outer => outer + targetLocal)
        host.compilerLeaf.inheritedLength)
  let targetItems : ItemSeq
      (host.focus.holeWires + targetLocal) host.focus.holeRels :=
    host.compilerLeaf.items.castWiresEq targetLength
  let material := Concrete.Elaboration.finishRegion
    spliceInput.pattern.val.diagram pattern.leaf.inheritedWires
    spliceInput.binderSpine.bodyContainer pattern.leaf.items
  let actualWire : Fin pattern.leaf.inheritedWires.length →
      Fin (host.focus.holeWires + targetLocal) := fun index =>
    Fin.cast targetLength
      (spliceInput.plugLayout.bodyTerminalWireRenaming hadmissible host
        pattern.witness pattern.leaf hnonempty index)
  let actualRelation : RelationRenaming pattern.witness.toFocus.holeRels
      host.focus.holeRels := fun {_arity} relation =>
    spliceInput.plugLayout.coalescedTerminalRelationRenaming hadmissible
      host.intrinsicPath host.compilerLeaf pattern.witness pattern.leaf
      hnonempty relation
  Region.spliceAt targetLocal targetItems material actualWire actualRelation

/-- Exact executor splice at the canonical host focus for an empty binder
spine.  The copied pattern is its compiled open root. -/
noncomputable def iterationActualSpliceOfEmpty
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible) :
    let spliceInput := iterationInput input selection target
    let host := Concrete.Splice.Input.compiledSpliceHostView spliceInput hadmissible
    Region  host.focus.holeWires host.focus.holeRels :=
  let spliceInput := iterationInput input selection target
  let host := Concrete.Splice.Input.compiledSpliceHostView spliceInput hadmissible
  let pattern := Concrete.Splice.Input.compiledSpliceOpenRootItems spliceInput.pattern
  let targetLocal :=
    (Concrete.Elaboration.exactScopeWires spliceInput.coalesceFrameRaw
      spliceInput.site).length
  let targetLength :
      (host.compilerLeaf.inheritedWires.extend spliceInput.site).length =
        host.focus.holeWires + targetLocal :=
    (Concrete.Elaboration.WireContext.length_extend
      host.compilerLeaf.inheritedWires spliceInput.site).trans
      (congrArg (fun outer => outer + targetLocal)
        host.compilerLeaf.inheritedLength)
  let targetItems : ItemSeq
      (host.focus.holeWires + targetLocal) host.focus.holeRels :=
    host.compilerLeaf.items.castWiresEq targetLength
  let material := Concrete.Elaboration.finishRoot
    spliceInput.pattern.val.exposedWires spliceInput.pattern.val.hiddenWires
    pattern.items
  let actualWire : Fin spliceInput.pattern.val.exposedWires.length →
      Fin (host.focus.holeWires + targetLocal) := fun index =>
    Fin.cast targetLength
      (spliceInput.plugLayout.exposedWireRenaming hadmissible host index)
  let actualRelation : RelationRenaming [] host.focus.holeRels :=
    Concrete.Splice.Input.PlugLayout.emptyRelationRenaming host.focus.holeRels
  Region.spliceAt targetLocal targetItems material actualWire actualRelation

theorem coalescedRouteTerminal_hostLexical
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hencloses : input.val.Encloses selection.val.anchor target)
    {keptItems : ItemSeq
      ((IterationAnchor.coalescedAnchorView input selection target hadmissible)
        |>.compilerLeaf.inheritedWires.extend selection.val.anchor).length
      (IterationAnchor.coalescedAnchorView input selection target hadmissible
        ).focus.holeRels}
    {path : List Nat}
    (route : Concrete.Splice.RegionRoute
      (iterationInput input selection target).coalesceFrameRaw
      selection.val.anchor target path)
    {compiledPath : List Nat}
    {witness : Region.ContextPath (Region.mk 0 keptItems) compiledPath}
    (terminal : CompiledRouteTerminal
      ((iterationInput input selection target).coalesceFrame hadmissible)
      (Concrete.Splice.Region.ContextPath.CompilerLeaf.hereOfItemsComputation
        (iterationInput input selection target).coalesceFrameRaw
        selection.val.anchor
        (IterationAnchor.coalescedAnchorView input selection target hadmissible
          ).compilerLeaf.inheritedWires
        (IterationAnchor.coalescedAnchorView input selection target hadmissible
          ).compilerLeaf.binders
        (IterationAnchor.coalescedAnchorView input selection target hadmissible
          ).compilerLeaf.fuel
        (IterationAnchor.coalescedAnchorView input selection target hadmissible
          ).compilerLeaf.items
        (IterationAnchor.coalescedAnchorView input selection target hadmissible
          ).compilerLeaf.itemsComputation
        (IterationAnchor.coalescedAnchorView input selection target hadmissible
          ).compilerLeaf.wiresExact
        (IterationAnchor.coalescedAnchorView input selection target hadmissible
          ).compilerLeaf.bindersCover
        (IterationAnchor.coalescedAnchorView input selection target hadmissible
          ).compilerLeaf.binderEnumeration)
      keptItems route compiledPath witness) :
    let spliceInput := iterationInput input selection target
    let host := Concrete.Splice.Input.compiledSpliceHostView spliceInput hadmissible
    ∃ _hrels : witness.toFocus.holeRels = host.focus.holeRels,
      HEq terminal.leaf.binders host.compilerLeaf.binders := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let anchorView := IterationAnchor.coalescedAnchorView input selection target
    hadmissible
  let host := Concrete.Splice.Input.compiledSpliceHostView spliceInput hadmissible
  have coalescedEncloses : spliceInput.coalesceFrameRaw.Encloses
      selection.val.anchor target :=
    (spliceInput.coalesceFrameRaw_encloses_iff selection.val.anchor target).2
      hencloses
  have rootBinders : anchorView.result.state.binders =
      host.result.state.binders :=
    anchorView.result.binders_eq.trans host.result.binders_eq.symm
  obtain ⟨tailPath, tailOuter, tailBody, tailRoute, tailWitness, tailState,
      tailTrace, tailStartBinders, tailRels, tailTerminalBinders⟩ :=
    Concrete.Splice.Input.CompilerTrace.tailAtEnclosed
      (spliceInput.coalesceFrameRaw_wellFormed hadmissible)
      anchorView.result.trace host.result.trace rootBinders coalescedEncloses
  have tailStartsAtAnchor : tailState.binders =
      (Concrete.Splice.Region.ContextPath.CompilerLeaf.hereOfItemsComputation
        spliceInput.coalesceFrameRaw selection.val.anchor
        anchorView.compilerLeaf.inheritedWires anchorView.compilerLeaf.binders
        anchorView.compilerLeaf.fuel anchorView.compilerLeaf.items
        anchorView.compilerLeaf.itemsComputation anchorView.compilerLeaf.wiresExact
        anchorView.compilerLeaf.bindersCover
        anchorView.compilerLeaf.binderEnumeration).binders := by
    simpa [anchorView, Concrete.Splice.SiteView.compilerLeaf] using tailStartBinders
  obtain ⟨routeRels, routeTerminalBinders⟩ :=
    terminal.terminalLexical tailTrace tailStartsAtAnchor
  refine ⟨routeRels.trans tailRels, ?_⟩
  exact (routeTerminalBinders.trans tailTerminalBinders)

noncomputable def Region.ContextPath.appendRootItemsRight_actualIso
    {items suffix : ItemSeq  wires rels}
    {index : Nat} {rest : List Nat}
    (witness : Region.ContextPath (Region.mk 0 items) (index :: rest))
    (replacement : Region  witness.toFocus.holeWires
      witness.toFocus.holeRels)
    {actualRels : RelCtx}
    (actualRelsEq : witness.toFocus.holeRels = actualRels)
    {actualWires : Nat}
    (actualWire : FiniteEquiv (Fin witness.toFocus.holeWires)
      (Fin actualWires))
    (actual : Region  actualWires actualRels)
    (iso : RegionIso  actualWire actualRels
      (replacement.renameRelations
        (Concrete.Splice.Input.relationRenamingOfEq actualRelsEq)) actual) :
    RegionIso
      ((witness.appendRootItemsRightHoleWire (suffix := suffix)).trans
        actualWire)
      actualRels
      ((witness.appendRootItemsRightReplacement
          (suffix := suffix) replacement).renameRelations
        (Concrete.Splice.Input.relationRenamingOfEq
          ((witness.appendRootItemsRightHoleRelsEq (suffix := suffix)).trans
            actualRelsEq)))
      actual := by
  cases witness <;> simpa [Region.ContextPath.appendRootItemsRightHoleWire,
    Region.ContextPath.appendRootItemsRightHoleRelsEq,
    Region.ContextPath.appendRootItemsRightReplacement,
    FiniteEquiv.trans, FiniteEquiv.refl] using iso

/-- The route-native splice used by the contraction proof is isomorphic to
the executable compiler's splice at the canonical host focus.  This theorem
combines the terminal lexical isomorphism with the previously proved exact
wire and relation factors. -/
noncomputable def properRoute_actualSpliceIso
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hencloses : input.val.Encloses selection.val.anchor target)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    {keptItems : ItemSeq
      ((IterationAnchor.coalescedAnchorView input selection target hadmissible)
        |>.compilerLeaf.inheritedWires.extend selection.val.anchor).length
      (IterationAnchor.coalescedAnchorView input selection target hadmissible
        ).focus.holeRels}
    {path : List Nat}
    (route : Concrete.Splice.RegionRoute
      (iterationInput input selection target).coalesceFrameRaw
      selection.val.anchor target path)
    {compiledPath : List Nat}
    {witness : Region.ContextPath (Region.mk 0 keptItems) compiledPath}
    (terminal : CompiledRouteTerminal
      ((iterationInput input selection target).coalesceFrame hadmissible)
      (Concrete.Splice.Region.ContextPath.CompilerLeaf.hereOfItemsComputation
        (iterationInput input selection target).coalesceFrameRaw
        selection.val.anchor
        (IterationAnchor.coalescedAnchorView input selection target hadmissible
          ).compilerLeaf.inheritedWires
        (IterationAnchor.coalescedAnchorView input selection target hadmissible
          ).compilerLeaf.binders
        (IterationAnchor.coalescedAnchorView input selection target hadmissible
          ).compilerLeaf.fuel
        (IterationAnchor.coalescedAnchorView input selection target hadmissible
          ).compilerLeaf.items
        (IterationAnchor.coalescedAnchorView input selection target hadmissible
          ).compilerLeaf.itemsComputation
        (IterationAnchor.coalescedAnchorView input selection target hadmissible
          ).compilerLeaf.wiresExact
        (IterationAnchor.coalescedAnchorView input selection target hadmissible
          ).compilerLeaf.bindersCover
        (IterationAnchor.coalescedAnchorView input selection target hadmissible
          ).compilerLeaf.binderEnumeration)
      keptItems route compiledPath witness) :
    let spliceInput := iterationInput input selection target
    let layout : FragmentLayout input.val selection := {}
    let anchorView := IterationAnchor.coalescedAnchorView input selection target
      hadmissible
    let sourceContext :=
      anchorView.compilerLeaf.inheritedWires.extend selection.val.anchor
    let iso := IterationQuotient.coalescedFrameIso input selection target
    let targetContext := sourceContext.map iso.wires
    let targetBinders : Concrete.Elaboration.BinderContext input.val
        anchorView.focus.holeRels := fun binder =>
      anchorView.compilerLeaf.binders binder
    let targetCover : targetBinders.Covers selection.val.anchor :=
      anchorView.compilerLeaf.bindersCover.mapIso iso (by intro binder; rfl)
    let pattern := Concrete.Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
    let binderWitness := IterationExtraction.ExtractionBinderWitness.terminal input selection layout
      pattern.leaf.binders pattern.leaf.binderEnumeration targetBinders
      targetCover
    let host := Concrete.Splice.Input.compiledSpliceHostView spliceInput hadmissible
    let hostIndex := iterationTerminalAnchorIndex input selection target
      hadmissible hnonempty
    let sourceContextWire : FiniteEquiv (Fin sourceContext.length)
        (Fin targetContext.length) :=
      FiniteEquiv.finCast (List.length_map iso.wires).symm
    let routeWire : Fin pattern.leaf.inheritedWires.length →
        Fin witness.toFocus.holeWires := fun index =>
      Fin.cast terminal.leaf.inheritedLength
        (terminal.inheritedIndex (sourceContextWire.symm (hostIndex index)))
    let routeRelation : RelationRenaming pattern.witness.toFocus.holeRels
        witness.toFocus.holeRels := fun {arity} relation =>
      witness.toFocus.context.outerRelation
        (binderWitness.relationMap relation)
    let material := Concrete.Elaboration.finishRegion
      spliceInput.pattern.val.diagram pattern.leaf.inheritedWires
      spliceInput.binderSpine.bodyContainer pattern.leaf.items
    Σ (sourceLocal : Nat)
      (sourceItems : ItemSeq
        (witness.toFocus.holeWires + sourceLocal)
        witness.toFocus.holeRels),
      PSigma fun _sourceBody :
          witness.toFocus.body = Region.mk sourceLocal sourceItems =>
      let hrels := Classical.choose
        (coalescedRouteTerminal_hostLexical input selection target hadmissible
          hencloses route terminal)
      let relationWire :=
        Concrete.Splice.Input.compilerLeafOuterWire witness terminal.leaf
          host.intrinsicPath host.compilerLeaf
          (Concrete.Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
            witness terminal.leaf host.intrinsicPath host.compilerLeaf)
      RegionIso  relationWire host.focus.holeRels
        ((Region.spliceAt sourceLocal sourceItems material
          (fun index => Fin.castAdd sourceLocal (routeWire index))
          routeRelation).renameRelations
            (Concrete.Splice.Input.relationRenamingOfEq hrels))
        (iterationActualSpliceOfNonempty input selection target hadmissible
          hnonempty) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let layout : FragmentLayout input.val selection := {}
  let anchorView := IterationAnchor.coalescedAnchorView input selection target
    hadmissible
  let sourceContext :=
    anchorView.compilerLeaf.inheritedWires.extend selection.val.anchor
  let iso := IterationQuotient.coalescedFrameIso input selection target
  let targetContext := sourceContext.map iso.wires
  let targetBinders : Concrete.Elaboration.BinderContext input.val
      anchorView.focus.holeRels := fun binder =>
    anchorView.compilerLeaf.binders binder
  have binderAgreement : Concrete.Elaboration.BinderContextsAgree iso
      anchorView.compilerLeaf.binders targetBinders := by
    intro binder
    rfl
  let targetCover : targetBinders.Covers selection.val.anchor :=
    anchorView.compilerLeaf.bindersCover.mapIso iso binderAgreement
  let pattern := Concrete.Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
  let binderWitness := IterationExtraction.ExtractionBinderWitness.terminal input selection layout
    pattern.leaf.binders pattern.leaf.binderEnumeration targetBinders
    targetCover
  let host := Concrete.Splice.Input.compiledSpliceHostView spliceInput hadmissible
  let hostIndex := iterationTerminalAnchorIndex input selection target
    hadmissible hnonempty
  let sourceContextWire : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length) :=
    FiniteEquiv.finCast (List.length_map iso.wires).symm
  let routeWire : Fin pattern.leaf.inheritedWires.length →
      Fin witness.toFocus.holeWires := fun index =>
    Fin.cast terminal.leaf.inheritedLength
      (terminal.inheritedIndex (sourceContextWire.symm (hostIndex index)))
  let routeRelation : RelationRenaming pattern.witness.toFocus.holeRels
      witness.toFocus.holeRels := fun {arity} relation =>
    witness.toFocus.context.outerRelation
      (binderWitness.relationMap relation)
  let targetLocal :=
    (Concrete.Elaboration.exactScopeWires spliceInput.coalesceFrameRaw
      spliceInput.site).length
  let targetLength :
      (host.compilerLeaf.inheritedWires.extend spliceInput.site).length =
        host.focus.holeWires + targetLocal :=
    (Concrete.Elaboration.WireContext.length_extend
      host.compilerLeaf.inheritedWires spliceInput.site).trans
      (congrArg (fun outer => outer + targetLocal)
        host.compilerLeaf.inheritedLength)
  let targetItems : ItemSeq
      (host.focus.holeWires + targetLocal) host.focus.holeRels :=
    host.compilerLeaf.items.castWiresEq targetLength
  let actualWire : Fin pattern.leaf.inheritedWires.length →
      Fin (host.focus.holeWires + targetLocal) := fun index =>
    Fin.cast targetLength
      (spliceInput.plugLayout.bodyTerminalWireRenaming hadmissible host
        pattern.witness pattern.leaf hnonempty index)
  let actualRelation : RelationRenaming pattern.witness.toFocus.holeRels
      host.focus.holeRels := fun {arity} relation =>
    spliceInput.plugLayout.coalescedTerminalRelationRenaming hadmissible
      host.intrinsicPath host.compilerLeaf pattern.witness pattern.leaf
      hnonempty relation
  let material := Concrete.Elaboration.finishRegion
    spliceInput.pattern.val.diagram pattern.leaf.inheritedWires
    spliceInput.binderSpine.bodyContainer pattern.leaf.items
  let lexical := coalescedRouteTerminal_hostLexical input selection target
    hadmissible hencloses route terminal
  let hrels := Classical.choose lexical
  have hbinders : HEq terminal.leaf.binders host.compilerLeaf.binders :=
    Classical.choose_spec lexical
  let inherited :=
    Concrete.Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
      witness terminal.leaf host.intrinsicPath host.compilerLeaf
  let relationWire := Concrete.Splice.Input.compilerLeafOuterWire witness terminal.leaf
    host.intrinsicPath host.compilerLeaf inherited
  have bodyIso := Concrete.Splice.Input.compilerLeaf_regionIso_sameDiagram
    (spliceInput.coalesceFrameRaw_wellFormed hadmissible)
    witness terminal.leaf host.intrinsicPath host.compilerLeaf hrels hbinders
  have targetBodyEq : host.intrinsicPath.toFocus.body =
      Region.mk targetLocal targetItems := by
    rw [host.compilerLeaf.bodyComputation]
    simp only [Concrete.Elaboration.finishRegion, Region.castWiresEq_mk,
      ItemSeq.castWiresEq_trans]
    rfl
  cases sourceBodyEq : witness.toFocus.body with
  | mk sourceLocal sourceItems =>
      rw [sourceBodyEq, targetBodyEq] at bodyIso
      cases bodyIso with
      | mk localWire hostItemsIso =>
          have wireFactor :
              (extendWireEquiv relationWire localWire).toFun ∘
                  (fun index => Fin.castAdd sourceLocal
                    (routeWire index)) = actualWire := by
            funext index
            have actualFactor := iterationTerminalWireFactor input
              selection target hadmissible hnonempty route terminal index
              (hostIndex index)
              (iterationTerminalAnchorIndex_related input selection target
                hadmissible hnonempty index)
            dsimp only [actualWire]
            dsimp only at actualFactor
            rw [actualFactor]
            apply Fin.ext
            simp [routeWire, relationWire,
              sourceContextWire, inherited, host, spliceInput,
              Concrete.Splice.Input.compilerLeafOuterWire,
              Concrete.Elaboration.WireContext.outerIndex,
              FiniteEquiv.finCast]
            congr 2
          have relationFactor : ∀ {arity}
              (relation : RelVar pattern.witness.toFocus.holeRels arity),
              actualRelation relation =
                Concrete.Splice.Input.relationRenamingOfEq hrels
                  (routeRelation relation) := by
            intro arity relation
            exact iterationTerminalRelationFactor input selection target
              hadmissible hnonempty route terminal hrels hbinders relation
          refine ⟨sourceLocal, sourceItems, rfl, ?_⟩
          simpa [iterationActualSpliceOfNonempty, spliceInput, host, pattern,
            targetLocal, targetLength, targetItems, material, actualWire,
            actualRelation] using
            (RegionIso.spliceAt_renameRelations hostItemsIso material
              (fun index => Fin.castAdd sourceLocal (routeWire index))
              actualWire wireFactor routeRelation actualRelation
              relationFactor)

/-- Empty-spine route-native splice identified with the executor's exact
canonical-host splice. -/
noncomputable def properRoute_rootActualSpliceIso
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hencloses : input.val.Encloses selection.val.anchor target)
    (hzero : (iterationInput input selection target).binderSpine.proxyCount =
      0)
    {keptItems : ItemSeq
      ((IterationAnchor.coalescedAnchorView input selection target hadmissible)
        |>.compilerLeaf.inheritedWires.extend selection.val.anchor).length
      (IterationAnchor.coalescedAnchorView input selection target hadmissible
        ).focus.holeRels}
    {path : List Nat}
    (route : Concrete.Splice.RegionRoute
      (iterationInput input selection target).coalesceFrameRaw
      selection.val.anchor target path)
    {compiledPath : List Nat}
    {witness : Region.ContextPath (Region.mk 0 keptItems) compiledPath}
    (terminal : CompiledRouteTerminal
      ((iterationInput input selection target).coalesceFrame hadmissible)
      (Concrete.Splice.Region.ContextPath.CompilerLeaf.hereOfItemsComputation
        (iterationInput input selection target).coalesceFrameRaw
        selection.val.anchor
        (IterationAnchor.coalescedAnchorView input selection target hadmissible
          ).compilerLeaf.inheritedWires
        (IterationAnchor.coalescedAnchorView input selection target hadmissible
          ).compilerLeaf.binders
        (IterationAnchor.coalescedAnchorView input selection target hadmissible
          ).compilerLeaf.fuel
        (IterationAnchor.coalescedAnchorView input selection target hadmissible
          ).compilerLeaf.items
        (IterationAnchor.coalescedAnchorView input selection target hadmissible
          ).compilerLeaf.itemsComputation
        (IterationAnchor.coalescedAnchorView input selection target hadmissible
          ).compilerLeaf.wiresExact
        (IterationAnchor.coalescedAnchorView input selection target hadmissible
          ).compilerLeaf.bindersCover
        (IterationAnchor.coalescedAnchorView input selection target hadmissible
          ).compilerLeaf.binderEnumeration)
      keptItems route compiledPath witness) :
    let spliceInput := iterationInput input selection target
    let anchorView := IterationAnchor.coalescedAnchorView input selection target
      hadmissible
    let sourceContext := anchorView.compilerLeaf.inheritedWires.extend
      selection.val.anchor
    let iso := IterationQuotient.coalescedFrameIso input selection target
    let targetContext := sourceContext.map iso.wires
    let pattern := Concrete.Splice.Input.compiledSpliceOpenRootItems spliceInput.pattern
    let host := Concrete.Splice.Input.compiledSpliceHostView spliceInput hadmissible
    let hostIndex := iterationRootAnchorIndex input selection target
      hadmissible hzero
    let sourceContextWire : FiniteEquiv (Fin sourceContext.length)
        (Fin targetContext.length) :=
      FiniteEquiv.finCast (List.length_map iso.wires).symm
    let routeWire : Fin spliceInput.pattern.val.exposedWires.length →
        Fin witness.toFocus.holeWires := fun index =>
      Fin.cast terminal.leaf.inheritedLength
        (terminal.inheritedIndex (sourceContextWire.symm (hostIndex index)))
    let routeRelation : RelationRenaming [] witness.toFocus.holeRels :=
      Concrete.Splice.Input.PlugLayout.emptyRelationRenaming witness.toFocus.holeRels
    let material := Concrete.Elaboration.finishRoot
      spliceInput.pattern.val.exposedWires spliceInput.pattern.val.hiddenWires
      pattern.items
    Σ (sourceLocal : Nat)
      (sourceItems : ItemSeq
        (witness.toFocus.holeWires + sourceLocal)
        witness.toFocus.holeRels),
      PSigma fun _sourceBody :
          witness.toFocus.body = Region.mk sourceLocal sourceItems =>
      let hrels := Classical.choose
        (coalescedRouteTerminal_hostLexical input selection target hadmissible
          hencloses route terminal)
      let relationWire :=
        Concrete.Splice.Input.compilerLeafOuterWire witness terminal.leaf
          host.intrinsicPath host.compilerLeaf
          (Concrete.Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
            witness terminal.leaf host.intrinsicPath host.compilerLeaf)
      RegionIso  relationWire host.focus.holeRels
        ((Region.spliceAt sourceLocal sourceItems material
          (fun index => Fin.castAdd sourceLocal (routeWire index))
          routeRelation).renameRelations
            (Concrete.Splice.Input.relationRenamingOfEq hrels))
        (iterationActualSpliceOfEmpty input selection target hadmissible) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let anchorView := IterationAnchor.coalescedAnchorView input selection target
    hadmissible
  let sourceContext := anchorView.compilerLeaf.inheritedWires.extend
    selection.val.anchor
  let iso := IterationQuotient.coalescedFrameIso input selection target
  let targetContext := sourceContext.map iso.wires
  let pattern := Concrete.Splice.Input.compiledSpliceOpenRootItems spliceInput.pattern
  let host := Concrete.Splice.Input.compiledSpliceHostView spliceInput hadmissible
  let hostIndex := iterationRootAnchorIndex input selection target
    hadmissible hzero
  let sourceContextWire : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length) :=
    FiniteEquiv.finCast (List.length_map iso.wires).symm
  let routeWire : Fin spliceInput.pattern.val.exposedWires.length →
      Fin witness.toFocus.holeWires := fun index =>
    Fin.cast terminal.leaf.inheritedLength
      (terminal.inheritedIndex (sourceContextWire.symm (hostIndex index)))
  let routeRelation : RelationRenaming [] witness.toFocus.holeRels :=
    Concrete.Splice.Input.PlugLayout.emptyRelationRenaming witness.toFocus.holeRels
  let targetLocal :=
    (Concrete.Elaboration.exactScopeWires spliceInput.coalesceFrameRaw
      spliceInput.site).length
  let targetLength :
      (host.compilerLeaf.inheritedWires.extend spliceInput.site).length =
        host.focus.holeWires + targetLocal :=
    (Concrete.Elaboration.WireContext.length_extend
      host.compilerLeaf.inheritedWires spliceInput.site).trans
      (congrArg (fun outer => outer + targetLocal)
        host.compilerLeaf.inheritedLength)
  let targetItems : ItemSeq
      (host.focus.holeWires + targetLocal) host.focus.holeRels :=
    host.compilerLeaf.items.castWiresEq targetLength
  let actualWire : Fin spliceInput.pattern.val.exposedWires.length →
      Fin (host.focus.holeWires + targetLocal) := fun index =>
    Fin.cast targetLength
      (spliceInput.plugLayout.exposedWireRenaming hadmissible host index)
  let actualRelation : RelationRenaming [] host.focus.holeRels :=
    Concrete.Splice.Input.PlugLayout.emptyRelationRenaming host.focus.holeRels
  let material := Concrete.Elaboration.finishRoot
    spliceInput.pattern.val.exposedWires spliceInput.pattern.val.hiddenWires
    pattern.items
  let lexical := coalescedRouteTerminal_hostLexical input selection target
    hadmissible hencloses route terminal
  let hrels := Classical.choose lexical
  have hbinders : HEq terminal.leaf.binders host.compilerLeaf.binders :=
    Classical.choose_spec lexical
  let inherited :=
    Concrete.Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
      witness terminal.leaf host.intrinsicPath host.compilerLeaf
  let relationWire := Concrete.Splice.Input.compilerLeafOuterWire witness terminal.leaf
    host.intrinsicPath host.compilerLeaf inherited
  have bodyIso := Concrete.Splice.Input.compilerLeaf_regionIso_sameDiagram
    (spliceInput.coalesceFrameRaw_wellFormed hadmissible)
    witness terminal.leaf host.intrinsicPath host.compilerLeaf hrels hbinders
  have targetBodyEq : host.intrinsicPath.toFocus.body =
      Region.mk targetLocal targetItems := by
    rw [host.compilerLeaf.bodyComputation]
    simp only [Concrete.Elaboration.finishRegion, Region.castWiresEq_mk,
      ItemSeq.castWiresEq_trans]
    rfl
  cases sourceBodyEq : witness.toFocus.body with
  | mk sourceLocal sourceItems =>
      rw [sourceBodyEq, targetBodyEq] at bodyIso
      cases bodyIso with
      | mk localWire hostItemsIso =>
          have wireFactor :
              (extendWireEquiv relationWire localWire).toFun ∘
                  (fun index => Fin.castAdd sourceLocal
                    (routeWire index)) = actualWire := by
            funext index
            have actualFactor := iterationRootWireFactor input selection target
              hadmissible route terminal index (hostIndex index)
              (iterationRootAnchorIndex_related input selection target
                hadmissible hzero index)
            dsimp only [actualWire]
            dsimp only at actualFactor
            rw [actualFactor]
            apply Fin.ext
            simp [routeWire, relationWire, sourceContextWire, inherited, host,
              spliceInput, Concrete.Splice.Input.compilerLeafOuterWire,
              Concrete.Elaboration.WireContext.outerIndex,
              FiniteEquiv.finCast]
            congr 2
          have relationFactor : ∀ {arity}
              (relation : RelVar [] arity),
              actualRelation relation =
                Concrete.Splice.Input.relationRenamingOfEq hrels
                  (routeRelation relation) := by
            intro arity relation
            exact Fin.elim0 relation.index
          refine ⟨sourceLocal, sourceItems, rfl, ?_⟩
          simpa [iterationActualSpliceOfEmpty, spliceInput, host, pattern,
            targetLocal, targetLength, targetItems, material, actualWire,
            actualRelation] using
            (RegionIso.spliceAt_renameRelations hostItemsIso material
              (fun index => Fin.castAdd sourceLocal (routeWire index))
              actualWire wireFactor routeRelation actualRelation
              relationFactor)

end VisualProof.Refinement.Implementation.IterationActualSplice
