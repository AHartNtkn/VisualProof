import VisualProof.Rule.Soundness.Iteration.CanonicalContraction

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Rule.ModalSoundness

/-- Complete scoped contraction certificate for proper-target, empty-spine
iteration at the selection anchor. -/
structure ProperIterationRootAnchorContraction
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible) where
  root : Region signature
    (iterationCoalescedAnchorView input selection target hadmissible
      ).focus.holeWires
    (iterationCoalescedAnchorView input selection target hadmissible
      ).focus.holeRels
  rootEq : root =
    (iterationCoalescedAnchorView input selection target hadmissible
      ).focus.body
  path : List Nat
  route : Splice.RegionRoute
    (iterationInput input selection target).coalesceFrameRaw
    selection.val.anchor target path
  flatWitness : Region.ContextPath
    (Region.mk 0
      (iterationCoalescedAnchorView input selection target hadmissible
        ).compilerLeaf.items) path
  flatReplacement : Region signature flatWitness.toFocus.holeWires
    flatWitness.toFocus.holeRels
  flatEquivalent : ∀ (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (environment : Fin
      (iterationCoalescedAnchorView input selection target hadmissible
        |>.compilerLeaf.inheritedWires.extend selection.val.anchor).length →
      model.Carrier)
    (relEnv : RelEnv model.Carrier
      (iterationCoalescedAnchorView input selection target hadmissible
        ).focus.holeRels),
    denoteItemSeq model named environment relEnv
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.items ↔
      denoteRegion model named environment relEnv
        (flatWitness.toFocus.context.fill flatReplacement)
  flatActualRelsEq : flatWitness.toFocus.holeRels =
    (Splice.Input.compiledSpliceHostView
      (iterationInput input selection target) hadmissible).focus.holeRels
  flatActualWire : FiniteEquiv (Fin flatWitness.toFocus.holeWires)
    (Fin (Splice.Input.compiledSpliceHostView
      (iterationInput input selection target) hadmissible).focus.holeWires)
  flatActualIso : RegionIso signature flatActualWire
    (Splice.Input.compiledSpliceHostView
      (iterationInput input selection target) hadmissible).focus.holeRels
    (flatReplacement.renameRelations
      (Splice.Input.relationRenamingOfEq flatActualRelsEq))
    (iterationActualSpliceOfEmpty input selection target hadmissible)
  witness : Region.ContextPath root path
  replacement : Region signature witness.toFocus.holeWires
    witness.toFocus.holeRels
  actualRelsEq : witness.toFocus.holeRels =
    (Splice.Input.compiledSpliceHostView
      (iterationInput input selection target) hadmissible).focus.holeRels
  actualWire : FiniteEquiv (Fin witness.toFocus.holeWires)
    (Fin (Splice.Input.compiledSpliceHostView
      (iterationInput input selection target) hadmissible).focus.holeWires)
  terminalWires : List (Fin
    (iterationInput input selection target).coalesceFrameRaw.wireCount)
  terminalLength : terminalWires.length = witness.toFocus.holeWires
  actualWireSpec : ∀ index : Fin witness.toFocus.holeWires,
    (Splice.Input.compiledSpliceHostView
        (iterationInput input selection target) hadmissible
      ).compilerLeaf.inheritedWires.get
        (Fin.cast
          (Splice.Input.compiledSpliceHostView
            (iterationInput input selection target) hadmissible
          ).compilerLeaf.inheritedLength.symm (actualWire index)) =
      terminalWires.get (Fin.cast terminalLength.symm index)
  terminalCoherent : ∀ {sourceOuter : Nat} {sourceRels : Theory.RelCtx}
      {sourceBody : Region signature sourceOuter sourceRels}
      {targetPath : List Nat}
      {targetWitness : Region.ContextPath sourceBody targetPath}
      {targetState : Splice.Region.ContextPath.CompilerLeaf
        (iterationInput input selection target).coalesceFrameRaw
        selection.val.anchor (.here sourceBody)}
      {targetRoute : Splice.RegionRoute
        (iterationInput input selection target).coalesceFrameRaw
        selection.val.anchor target targetPath}
      (targetTrace : Splice.CompilerTrace signature
        (iterationInput input selection target).coalesceFrameRaw targetRoute
        targetWitness targetState),
    targetState.inheritedWires =
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.atFocus.inheritedWires →
      terminalWires = targetTrace.leaf.inheritedWires
  actualIso : RegionIso signature actualWire
    (Splice.Input.compiledSpliceHostView
      (iterationInput input selection target) hadmissible).focus.holeRels
    (replacement.renameRelations
      (Splice.Input.relationRenamingOfEq actualRelsEq))
    (iterationActualSpliceOfEmpty input selection target hadmissible)
  equivalent : ∀ (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (environment : Fin
      (iterationCoalescedAnchorView input selection target hadmissible
        ).focus.holeWires → model.Carrier)
    (relEnv : RelEnv model.Carrier
      (iterationCoalescedAnchorView input selection target hadmissible
        ).focus.holeRels),
    denoteRegion model named environment relEnv
        (iterationCoalescedAnchorView input selection target hadmissible
          ).focus.body ↔
      denoteRegion model named environment relEnv
        (witness.toFocus.context.fill replacement)

/-- Empty-spine scoped contraction in the ordered-open compiler coordinates
at a nested selection anchor. -/
structure ProperIterationRootOpenAnchorContraction
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (sourceBoundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root) where
  target_ne_anchor : target ≠ selection.val.anchor
  anchor_ne_root : selection.val.anchor ≠ input.val.root
  target_ne_root : target ≠
    (iterationInput input selection target).coalesceFrameRaw.root
  path : List Nat
  route : Splice.RegionRoute
    (iterationInput input selection target).coalesceFrameRaw
    selection.val.anchor target path
  witness : Region.ContextPath
    (iterationCoalescedOpenAnchorView input selection target hadmissible
      sourceBoundary sourceRoot).focus.body path
  replacement : Region signature witness.toFocus.holeWires
    witness.toFocus.holeRels
  actualRelsEq : witness.toFocus.holeRels =
    (Splice.Input.compiledSpliceHostView
      (iterationInput input selection target) hadmissible).focus.holeRels
  actualWire : FiniteEquiv (Fin witness.toFocus.holeWires)
    (Fin (Splice.Input.compiledSpliceHostView
      (iterationInput input selection target) hadmissible).focus.holeWires)
  routeTargetHoleWires : Nat
  routeWire : FiniteEquiv (Fin witness.toFocus.holeWires)
    (Fin routeTargetHoleWires)
  targetActualWire : FiniteEquiv (Fin routeTargetHoleWires)
    (Fin (Splice.Input.compiledSpliceHostView
      (iterationInput input selection target) hadmissible).focus.holeWires)
  actualWire_factor : actualWire = routeWire.trans targetActualWire
  sourceTerminalLeaf : Splice.Region.ContextPath.CompilerLeaf
    (iterationInput input selection target).coalesceFrameRaw target witness
  sourceTerminalWires : List (Fin
    (iterationInput input selection target).coalesceFrameRaw.wireCount)
  targetTerminalWires : List (Fin
    (iterationInput input selection target).coalesceFrameRaw.wireCount)
  sourceTerminalLength : sourceTerminalWires.length =
    witness.toFocus.holeWires
  targetTerminalLength : targetTerminalWires.length = routeTargetHoleWires
  sourceTerminalWires_eq : sourceTerminalWires =
    sourceTerminalLeaf.inheritedWires
  sourceTerminalCanonical : sourceTerminalWires =
    (Splice.Input.compiledSpliceCoalescedNestedLeaf
      (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot target_ne_root).inheritedWires
  terminalWireSpec : ∀ index : Fin witness.toFocus.holeWires,
    targetTerminalWires.get
        (Fin.cast targetTerminalLength.symm (routeWire index)) =
      sourceTerminalWires.get
        (Fin.cast sourceTerminalLength.symm index)
  actualWireSpec : ∀ index : Fin witness.toFocus.holeWires,
    (Splice.Input.compiledSpliceHostView
        (iterationInput input selection target) hadmissible
      ).compilerLeaf.inheritedWires.get
        (Fin.cast
          (Splice.Input.compiledSpliceHostView
            (iterationInput input selection target) hadmissible
          ).compilerLeaf.inheritedLength.symm (actualWire index)) =
      sourceTerminalWires.get (Fin.cast sourceTerminalLength.symm index)
  actualIso : RegionIso signature actualWire
    (Splice.Input.compiledSpliceHostView
      (iterationInput input selection target) hadmissible).focus.holeRels
    (replacement.renameRelations
      (Splice.Input.relationRenamingOfEq actualRelsEq))
    (iterationActualSpliceOfEmpty input selection target hadmissible)
  equivalent : ∀ (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (environment : Fin
      (iterationCoalescedOpenAnchorView input selection target hadmissible
        sourceBoundary sourceRoot).focus.holeWires → model.Carrier)
    (relEnv : RelEnv model.Carrier
      (iterationCoalescedOpenAnchorView input selection target hadmissible
        sourceBoundary sourceRoot).focus.holeRels),
    denoteRegion model named environment relEnv
        (iterationCoalescedOpenAnchorView input selection target hadmissible
          sourceBoundary sourceRoot).focus.body ↔
      denoteRegion model named environment relEnv
        (witness.toFocus.context.fill replacement)

private structure ZeroRoutedCompilerTraceAtBody
    (diagram : ConcreteDiagram) (start target : Fin diagram.regionCount)
    {path : List Nat} (route : Splice.RegionRoute diagram start target path)
    {outer : Nat} {rels : Theory.RelCtx}
    (body : Region signature outer rels)
    (initialWires : List (Fin diagram.wireCount)) where
  witness : Region.ContextPath body path
  state : Splice.Region.ContextPath.CompilerLeaf diagram start (.here body)
  trace : Splice.CompilerTrace signature diagram route witness state
  initial_eq : state.inheritedWires = initialWires

private def ZeroRoutedCompilerTraceAtBody.castBodyEq
    {diagram : ConcreteDiagram} {start target : Fin diagram.regionCount}
    {path : List Nat} {route : Splice.RegionRoute diagram start target path}
    {outer : Nat} {rels : Theory.RelCtx}
    {sourceBody targetBody : Region signature outer rels}
    {initialWires : List (Fin diagram.wireCount)}
    (equality : sourceBody = targetBody)
    (result : ZeroRoutedCompilerTraceAtBody diagram start target route
      sourceBody initialWires) :
    ZeroRoutedCompilerTraceAtBody diagram start target route targetBody
      initialWires := by
  subst targetBody
  exact result

/-- Empty-spine contraction at the authoritative anchor leaf. -/
theorem partitionedRoute_root_leaf_equiv
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hzero : (iterationInput input selection target).binderSpine.proxyCount =
      0)
    {selectedItems keptItems : ItemSeq signature
      ((iterationCoalescedAnchorView input selection target hadmissible)
        |>.compilerLeaf.inheritedWires.extend selection.val.anchor).length
      (iterationCoalescedAnchorView input selection target hadmissible
        ).focus.holeRels}
    (selectedCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature
          (iterationInput input selection target).coalesceFrameRaw
          (ConcreteElaboration.compileRegion? signature
            (iterationInput input selection target).coalesceFrameRaw
            (iterationCoalescedAnchorView input selection target hadmissible
              ).compilerLeaf.fuel)
          ((iterationCoalescedAnchorView input selection target hadmissible)
            |>.compilerLeaf.inheritedWires.extend selection.val.anchor)
          (iterationCoalescedAnchorView input selection target hadmissible
            ).compilerLeaf.binders
          (selectedOccurrences input.val selection) = some selectedItems)
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
    {hostLocal : Nat}
    {hostItems : ItemSeq signature (witness.toFocus.holeWires + hostLocal)
      witness.toFocus.holeRels}
    (bodyEq : witness.toFocus.body = Region.mk hostLocal hostItems)
    (factor : ∀ (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (env : Fin ((iterationCoalescedAnchorView input selection target
        hadmissible).compilerLeaf.inheritedWires.extend
          selection.val.anchor).length → model.Carrier)
      (relEnv : RelEnv model.Carrier
        (iterationCoalescedAnchorView input selection target hadmissible
          ).focus.holeRels),
      denoteItemSeq model named env relEnv
          (iterationCoalescedAnchorView input selection target hadmissible
            ).compilerLeaf.items ↔
        denoteRegion model named env relEnv (Region.mk 0 selectedItems) ∧
        denoteRegion model named env relEnv (Region.mk 0 keptItems))
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin ((iterationCoalescedAnchorView input selection target
      hadmissible).compilerLeaf.inheritedWires.extend
        selection.val.anchor).length → model.Carrier)
    (relEnv : RelEnv model.Carrier
      (iterationCoalescedAnchorView input selection target hadmissible
        ).focus.holeRels) :
    let spliceInput := iterationInput input selection target
    let anchorView := iterationCoalescedAnchorView input selection target
      hadmissible
    let sourceContext := anchorView.compilerLeaf.inheritedWires.extend
      selection.val.anchor
    let frameIso := iterationCoalescedFrameIso input selection target
    let targetContext := sourceContext.map frameIso.wires
    let pattern := Splice.Input.compiledSpliceOpenRootItems spliceInput.pattern
    let hostIndex := iterationRootAnchorIndex input selection target
      hadmissible hzero
    let sourceContextWire : FiniteEquiv (Fin sourceContext.length)
        (Fin targetContext.length) :=
      FiniteEquiv.finCast (List.length_map frameIso.wires).symm
    let routeWire : Fin spliceInput.pattern.val.exposedWires.length →
        Fin witness.toFocus.holeWires := fun index =>
      Fin.cast terminal.leaf.inheritedLength
        (terminal.inheritedIndex (sourceContextWire.symm (hostIndex index)))
    let routeRelation : RelationRenaming [] witness.toFocus.holeRels :=
      Splice.Input.PlugLayout.emptyRelationRenaming witness.toFocus.holeRels
    let material := ConcreteElaboration.finishRoot
      spliceInput.pattern.val.exposedWires spliceInput.pattern.val.hiddenWires
      pattern.items
    denoteItemSeq model named env relEnv anchorView.compilerLeaf.items ↔
      denoteRegion model named env relEnv
        ((Region.mk 0 selectedItems).conjoin
          (witness.toFocus.context.fill
            (Region.spliceAt hostLocal hostItems material
              (fun index => Fin.castAdd hostLocal (routeWire index))
              routeRelation))) := by
  dsimp only
  have contraction := partitionedRoute_rootSplice_equiv input selection target
    hadmissible hzero selectedCompiled route terminal
    (hostLocal := hostLocal) (hostItems := hostItems)
    model named env relEnv
  have rebuild : witness.toFocus.context.fill (Region.mk hostLocal hostItems) =
      Region.mk 0 keptItems := by
    rw [← bodyEq]
    exact witness.toFocus.rebuild
  calc
    denoteItemSeq model named env relEnv
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.items ↔
        denoteRegion model named env relEnv (Region.mk 0 selectedItems) ∧
          denoteRegion model named env relEnv (Region.mk 0 keptItems) :=
      factor model named env relEnv
    _ ↔ denoteRegion model named env relEnv
        ((Region.mk 0 selectedItems).conjoin (Region.mk 0 keptItems)) :=
      (Region.denote_conjoin model named env relEnv _ _).symm
    _ ↔ denoteRegion model named env relEnv
        ((Region.mk 0 selectedItems).conjoin
          (witness.toFocus.context.fill (Region.mk hostLocal hostItems))) := by
      rw [rebuild]
    _ ↔ _ := contraction

/-- Proper-target, empty-spine iteration at the authoritative anchor leaf. -/
theorem properIterationRootAnchorLeaf_equiv
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hencloses : input.val.Encloses selection.val.anchor target)
    (hzero : (iterationInput input selection target).binderSpine.proxyCount =
      0)
    {selectedItems keptItems : ItemSeq signature
      ((iterationCoalescedAnchorView input selection target hadmissible)
        |>.compilerLeaf.inheritedWires.extend selection.val.anchor).length
      (iterationCoalescedAnchorView input selection target hadmissible
        ).focus.holeRels}
    (selectedCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature
          (iterationInput input selection target).coalesceFrameRaw
          (ConcreteElaboration.compileRegion? signature
            (iterationInput input selection target).coalesceFrameRaw
            (iterationCoalescedAnchorView input selection target hadmissible
              ).compilerLeaf.fuel)
          ((iterationCoalescedAnchorView input selection target hadmissible)
            |>.compilerLeaf.inheritedWires.extend selection.val.anchor)
          (iterationCoalescedAnchorView input selection target hadmissible
            ).compilerLeaf.binders
          (selectedOccurrences input.val selection) = some selectedItems)
    {path : List Nat}
    (route : Splice.RegionRoute
      (iterationInput input selection target).coalesceFrameRaw
      selection.val.anchor target path)
    {index : Nat} {rest : List Nat}
    (retained : Region.ContextPath (Region.mk 0 keptItems) (index :: rest))
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
      keptItems route (index :: rest) retained)
    {partitionIso : RegionIso signature
      (FiniteEquiv.refl
        (Fin ((iterationCoalescedAnchorView input selection target hadmissible)
          |>.compilerLeaf.inheritedWires.extend selection.val.anchor).length))
      (iterationCoalescedAnchorView input selection target hadmissible
        ).focus.holeRels
      (Region.mk 0 (keptItems.append selectedItems))
      (Region.mk 0
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.items)}
    (alignment : RegionIso.ContextPathAlignment partitionIso
      (retained.appendRootItemsRight selectedItems))
    (factor : ∀ (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (env : Fin ((iterationCoalescedAnchorView input selection target
        hadmissible).compilerLeaf.inheritedWires.extend
          selection.val.anchor).length → model.Carrier)
      (relEnv : RelEnv model.Carrier
        (iterationCoalescedAnchorView input selection target hadmissible
          ).focus.holeRels),
      denoteItemSeq model named env relEnv
          (iterationCoalescedAnchorView input selection target hadmissible
            ).compilerLeaf.items ↔
        denoteRegion model named env relEnv (Region.mk 0 selectedItems) ∧
        denoteRegion model named env relEnv (Region.mk 0 keptItems))
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin ((iterationCoalescedAnchorView input selection target
      hadmissible).compilerLeaf.inheritedWires.extend
        selection.val.anchor).length → model.Carrier)
    (relEnv : RelEnv model.Carrier
      (iterationCoalescedAnchorView input selection target hadmissible
        ).focus.holeRels) :
    let spliceInput := iterationInput input selection target
    let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
    let hrels := Classical.choose
      (coalescedRouteTerminal_hostLexical input selection target hadmissible
        hencloses route terminal)
    let relationWire :=
      Splice.Input.compilerLeafOuterWire retained terminal.leaf
        host.intrinsicPath host.compilerLeaf
        (Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
          retained terminal.leaf host.intrinsicPath host.compilerLeaf)
    let extendedRelsEq :=
      (retained.appendRootItemsRightHoleRelsEq
        (suffix := selectedItems)).trans hrels
    let extendedWire :=
      (retained.appendRootItemsRightHoleWire
        (suffix := selectedItems)).trans relationWire
    let actual : Region signature host.focus.holeWires host.focus.holeRels :=
      iterationActualSpliceOfEmpty input selection target hadmissible
    let targetActualRelsEq := alignment.holeRelsEq.trans extendedRelsEq
    let bridgeWire := alignment.holeWire.symm.trans extendedWire
    let canonicalActual : Region signature
        alignment.targetWitness.toFocus.holeWires
        alignment.targetWitness.toFocus.holeRels :=
      (targetActualRelsEq.symm ▸ actual).renameWires bridgeWire.symm
    denoteItemSeq model named env relEnv
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.items ↔
      denoteRegion model named env relEnv
        (alignment.targetWitness.toFocus.context.fill canonicalActual) := by
  dsimp only
  obtain ⟨sourceLocal, sourceItems, bodyEq, actualIso⟩ :=
    properRoute_rootActualSpliceIso input selection target hadmissible
      hencloses hzero route terminal
  let spliceInput := iterationInput input selection target
  let anchorView := iterationCoalescedAnchorView input selection target
    hadmissible
  let sourceContext :=
    anchorView.compilerLeaf.inheritedWires.extend selection.val.anchor
  let frameIso := iterationCoalescedFrameIso input selection target
  let targetContext := sourceContext.map frameIso.wires
  let pattern := Splice.Input.compiledSpliceOpenRootItems spliceInput.pattern
  let hostIndex := iterationRootAnchorIndex input selection target
    hadmissible hzero
  let sourceContextWire : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length) :=
    FiniteEquiv.finCast (List.length_map frameIso.wires).symm
  let routeWire : Fin spliceInput.pattern.val.exposedWires.length →
      Fin retained.toFocus.holeWires := fun index =>
    Fin.cast terminal.leaf.inheritedLength
      (terminal.inheritedIndex (sourceContextWire.symm (hostIndex index)))
  let routeRelation : RelationRenaming [] retained.toFocus.holeRels :=
    Splice.Input.PlugLayout.emptyRelationRenaming retained.toFocus.holeRels
  let material := ConcreteElaboration.finishRoot
    spliceInput.pattern.val.exposedWires spliceInput.pattern.val.hiddenWires
    pattern.items
  let replacement := Region.spliceAt sourceLocal sourceItems material
    (fun index => Fin.castAdd sourceLocal (routeWire index)) routeRelation
  have partitioned := partitionedRoute_root_leaf_equiv input selection target
    hadmissible hzero selectedCompiled route terminal bodyEq factor
    model named env relEnv
  let hrels := Classical.choose
    (coalescedRouteTerminal_hostLexical input selection target hadmissible
      hencloses route terminal)
  let relationWire :=
    Splice.Input.compilerLeafOuterWire retained terminal.leaf
      (Splice.Input.compiledSpliceHostView spliceInput hadmissible).intrinsicPath
      (Splice.Input.compiledSpliceHostView spliceInput hadmissible).compilerLeaf
      (Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
        retained terminal.leaf
        (Splice.Input.compiledSpliceHostView spliceInput hadmissible).intrinsicPath
        (Splice.Input.compiledSpliceHostView spliceInput hadmissible).compilerLeaf)
  have extendedActualIso :=
    VisualProof.Rule.IterationSoundness.Region.ContextPath.appendRootItemsRight_actualIso
      retained (suffix := selectedItems)
      replacement hrels relationWire
      (iterationActualSpliceOfEmpty input selection target hadmissible)
      actualIso
  exact partitionedAlignment_actual_leaf_equiv retained alignment replacement
    ((retained.appendRootItemsRightHoleRelsEq
      (suffix := selectedItems)).trans hrels)
    ((retained.appendRootItemsRightHoleWire
      (suffix := selectedItems)).trans relationWire)
    (iterationActualSpliceOfEmpty input selection target hadmissible)
    extendedActualIso model named env relEnv partitioned

/-- All partition, route, alignment, scoping, and executable-splice witnesses
for the proper-target empty-spine branch. -/
theorem properIterationRootAnchorContraction_complete
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hencloses : input.val.Encloses selection.val.anchor target)
    (targetNotSelected : ¬ selection.val.SelectsRegion target)
    (targetNe : target ≠ selection.val.anchor)
    (hzero : (iterationInput input selection target).binderSpine.proxyCount =
      0) :
    Nonempty (ProperIterationRootAnchorContraction input selection target
      hadmissible) := by
  obtain ⟨keptItems, selectedItems, path, route, keptCompiled,
      selectedCompiled, ⟨routeResult⟩, factor⟩ :=
    coalescedAnchor_factor_and_route input selection target hadmissible
      hencloses targetNotSelected
  obtain ⟨compiledPosition, rest, retained, terminal, partitionIso,
      alignment, retainedHEq, alignmentPath, alignmentWire⟩ :=
    coalescedRoute_partition_alignment input selection target hadmissible
      targetNe keptCompiled selectedCompiled route routeResult
  obtain ⟨fullRouteResult⟩ := compilerLeaf_routeTrace_complete
    ((iterationInput input selection target).coalesceFrame hadmissible)
    (iterationCoalescedAnchorView input selection target hadmissible
      ).compilerLeaf.atFocus route
  have terminalFullWiresEq : terminal.leaf.inheritedWires =
      fullRouteResult.trace.leaf.inheritedWires := by
    apply terminal.terminalInherited fullRouteResult.trace
    simpa using fullRouteResult.inherited_eq
  let spliceInput := iterationInput input selection target
  let anchorView := iterationCoalescedAnchorView input selection target
    hadmissible
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  let hrels := Classical.choose
    (coalescedRouteTerminal_hostLexical input selection target hadmissible
      hencloses route terminal)
  let relationWire :=
    Splice.Input.compilerLeafOuterWire retained terminal.leaf
      host.intrinsicPath host.compilerLeaf
      (Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
        retained terminal.leaf host.intrinsicPath host.compilerLeaf)
  let extendedRelsEq :=
    (retained.appendRootItemsRightHoleRelsEq
      (suffix := selectedItems)).trans hrels
  let extendedWire :=
    (retained.appendRootItemsRightHoleWire
      (suffix := selectedItems)).trans relationWire
  let actual : Region signature host.focus.holeWires host.focus.holeRels :=
    iterationActualSpliceOfEmpty input selection target hadmissible
  let targetActualRelsEq := alignment.holeRelsEq.trans extendedRelsEq
  let bridgeWire := alignment.holeWire.symm.trans extendedWire
  let canonicalActual : Region signature
      alignment.targetWitness.toFocus.holeWires
      alignment.targetWitness.toFocus.holeRels :=
    (targetActualRelsEq.symm ▸ actual).renameWires bridgeWire.symm
  have itemsEquiv : ∀ (model : Lambda.LambdaModel)
      (named : NamedEnv model.Carrier signature)
      (environment : Fin
        (anchorView.compilerLeaf.inheritedWires.extend
          selection.val.anchor).length → model.Carrier)
      (relEnv : RelEnv model.Carrier anchorView.focus.holeRels),
      denoteItemSeq model named environment relEnv
          anchorView.compilerLeaf.items ↔
        denoteRegion model named environment relEnv
          (alignment.targetWitness.toFocus.context.fill canonicalActual) := by
    intro model named environment relEnv
    simpa [spliceInput, anchorView, host, hrels, relationWire,
      extendedRelsEq, extendedWire, actual, targetActualRelsEq, bridgeWire,
      canonicalActual] using
      (properIterationRootAnchorLeaf_equiv input selection target hadmissible
        hencloses hzero selectedCompiled route retained terminal alignment
        factor model named environment relEnv)
  have flatNonempty : alignment.targetPath ≠ [] := by
    rw [alignmentPath]
    exact Splice.RegionRoute.path_ne_nil route targetNe.symm
  let localWires :=
    (ConcreteElaboration.exactScopeWires spliceInput.coalesceFrameRaw
      selection.val.anchor).length
  let lengthExtend := ConcreteElaboration.WireContext.length_extend
    anchorView.compilerLeaf.inheritedWires selection.val.anchor
  let totalEquality :
      (anchorView.compilerLeaf.inheritedWires.extend
        selection.val.anchor).length =
        anchorView.focus.holeWires + localWires :=
    lengthExtend.trans
      (congrArg (fun inherited => inherited + localWires)
        anchorView.compilerLeaf.inheritedLength)
  let scopedWitness := alignment.targetWitness.relocal totalEquality
  let holeWiresEq : scopedWitness.toFocus.holeWires =
      alignment.targetWitness.toFocus.holeWires :=
    alignment.targetWitness.relocal_toFocus_holeWires_of_nonempty
      totalEquality flatNonempty
  let holeRelsEq : scopedWitness.toFocus.holeRels =
      alignment.targetWitness.toFocus.holeRels :=
    alignment.targetWitness.relocal_toFocus_holeRels totalEquality
  let scopedReplacement : Region signature scopedWitness.toFocus.holeWires
      scopedWitness.toFocus.holeRels :=
    holeRelsEq.symm ▸ canonicalActual.renameWires
      (FiniteEquiv.finCast holeWiresEq).symm
  let scopedActualRelsEq := holeRelsEq.trans targetActualRelsEq
  let scopedActualWire :=
    ((FiniteEquiv.finCast holeWiresEq).symm).symm.trans bridgeWire
  have alignmentHoleEq :
      (retained.appendRootItemsRight selectedItems).toFocus.holeWires =
        alignment.targetWitness.toFocus.holeWires := by
    apply Nat.le_antisymm
    · apply Nat.le_of_not_gt
      intro hle
      let index : Fin
          (retained.appendRootItemsRight selectedItems).toFocus.holeWires :=
        ⟨alignment.targetWitness.toFocus.holeWires, hle⟩
      have bound := (alignment.holeWire index).isLt
      rw [alignmentWire index] at bound
      exact (Nat.lt_irrefl _ bound)
    · apply Nat.le_of_not_gt
      intro hle
      let targetIndex : Fin alignment.targetWitness.toFocus.holeWires :=
        ⟨(retained.appendRootItemsRight selectedItems).toFocus.holeWires,
          hle⟩
      let sourceIndex := alignment.holeWire.symm targetIndex
      have mapped : alignment.holeWire sourceIndex = targetIndex :=
        alignment.holeWire.apply_symm_apply targetIndex
      have preserved := alignmentWire sourceIndex
      rw [mapped] at preserved
      have impossible :
          (retained.appendRootItemsRight selectedItems).toFocus.holeWires <
            (retained.appendRootItemsRight selectedItems).toFocus.holeWires :=
        calc
          _ = sourceIndex.val := preserved
          _ < _ := sourceIndex.isLt
      exact (Nat.lt_irrefl _ impossible)
  have appendHoleEq : retained.toFocus.holeWires =
      (retained.appendRootItemsRight selectedItems).toFocus.holeWires := by
    cases retained <;> rfl
  have terminalLength : fullRouteResult.trace.leaf.inheritedWires.length =
      scopedWitness.toFocus.holeWires := by
    calc
      fullRouteResult.trace.leaf.inheritedWires.length =
          terminal.leaf.inheritedWires.length :=
        congrArg List.length terminalFullWiresEq.symm
      _ = retained.toFocus.holeWires := terminal.leaf.inheritedLength
      _ = (retained.appendRootItemsRight selectedItems).toFocus.holeWires :=
        appendHoleEq
      _ = alignment.targetWitness.toFocus.holeWires := alignmentHoleEq
      _ = scopedWitness.toFocus.holeWires := holeWiresEq.symm
  have actualIso : RegionIso signature scopedActualWire host.focus.holeRels
      (scopedReplacement.renameRelations
        (Splice.Input.relationRenamingOfEq scopedActualRelsEq)) actual := by
    have canonicalIso := RegionIso.pulledBack_to_actual targetActualRelsEq
      bridgeWire actual
    have transported := RegionIso.transportedReplacement_to_actual
      holeRelsEq targetActualRelsEq
      (FiniteEquiv.finCast holeWiresEq).symm bridgeWire canonicalActual actual
      canonicalIso
    simpa [scopedReplacement, scopedActualRelsEq, scopedActualWire,
      FiniteEquiv.trans] using transported
  refine ⟨{
    root := Region.mk localWires
      (anchorView.compilerLeaf.items.castWiresEq totalEquality)
    rootEq := ?_
    path := alignment.targetPath
    route := alignmentPath.symm ▸ route
    flatWitness := alignment.targetWitness
    flatReplacement := canonicalActual
    flatEquivalent := itemsEquiv
    flatActualRelsEq := targetActualRelsEq
    flatActualWire := bridgeWire
    flatActualIso := by
      simpa [canonicalActual] using
        (RegionIso.pulledBack_to_actual targetActualRelsEq bridgeWire actual)
    witness := scopedWitness
    replacement := scopedReplacement
    actualRelsEq := scopedActualRelsEq
    actualWire := scopedActualWire
    terminalWires := fullRouteResult.trace.leaf.inheritedWires
    terminalLength := terminalLength
    actualWireSpec := by
      intro index
      let retainedIndex : Fin retained.toFocus.holeWires := Fin.cast
        (terminalLength.symm.trans
          ((congrArg List.length terminalFullWiresEq).symm.trans
            terminal.leaf.inheritedLength)) index
      have core := compilerLeafOuterWire_sameSite_spec retained terminal.leaf
        host.intrinsicPath host.compilerLeaf retainedIndex
      let targetIndex := Fin.cast holeWiresEq index
      let alignedIndex := alignment.holeWire.symm targetIndex
      have alignedVal : alignedIndex.val = index.val := by
        have preserved := alignmentWire alignedIndex
        have mapped : alignment.holeWire alignedIndex = targetIndex :=
          alignment.holeWire.apply_symm_apply targetIndex
        rw [mapped] at preserved
        exact preserved.symm
      have retainedArgumentEq :
          retained.appendRootItemsRightHoleWire alignedIndex =
            retainedIndex := by
        apply Fin.ext
        calc
          (retained.appendRootItemsRightHoleWire alignedIndex).val =
              alignedIndex.val := by cases retained <;> rfl
          _ = index.val := alignedVal
          _ = retainedIndex.val := rfl
      have actualWireEq : scopedActualWire index =
          relationWire retainedIndex := by
        change relationWire
            (retained.appendRootItemsRightHoleWire
              (alignment.holeWire.symm (Fin.cast holeWiresEq index))) = _
        exact congrArg relationWire retainedArgumentEq
      have hostIndexEq :
          Fin.cast host.compilerLeaf.inheritedLength.symm
              (scopedActualWire index) =
            Fin.cast host.compilerLeaf.inheritedLength.symm
              (relationWire retainedIndex) :=
        congrArg (Fin.cast host.compilerLeaf.inheritedLength.symm)
          actualWireEq
      have terminalGetEq :
          terminal.leaf.inheritedWires.get
              (Fin.cast terminal.leaf.inheritedLength.symm retainedIndex) =
            fullRouteResult.trace.leaf.inheritedWires.get
              (Fin.cast terminalLength.symm index) := by
        have transported := List.get_of_eq terminalFullWiresEq
          (Fin.cast terminal.leaf.inheritedLength.symm retainedIndex)
        rw [transported]
        congr 1
      rw [hostIndexEq]
      exact core.trans terminalGetEq
    terminalCoherent := by
      intro sourceOuter sourceRels sourceBody targetPath targetWitness
        targetState targetRoute targetTrace targetInitialEq
      apply Splice.Input.CompilerTrace.sameDiagramTerminalInherited
        ((iterationInput input selection target).coalesceFrameRaw_wellFormed
          hadmissible)
        fullRouteResult.trace targetTrace
      exact fullRouteResult.inherited_eq.trans targetInitialEq.symm
    actualIso := actualIso
    equivalent := ?_
  }⟩
  · change Region.mk localWires
        (anchorView.compilerLeaf.items.castWiresEq totalEquality) =
      anchorView.intrinsicPath.toFocus.body
    rw [anchorView.compilerLeaf.bodyComputation]
    simp only [ConcreteElaboration.finishRegion, Region.castWiresEq_mk,
      ItemSeq.castWiresEq_trans]
    congr
  intro model named environment relEnv
  have base :=
    Splice.Region.ContextPath.CompilerLeaf.body_equiv_of_relocal_fill
      anchorView.compilerLeaf alignment.targetWitness flatNonempty
      canonicalActual itemsEquiv model named environment relEnv
  dsimp only at base
  rw [Region.castWiresEq_castRels,
    Region.castWiresEq_eq_renameWires] at base
  simpa [scopedReplacement, scopedWitness, holeWiresEq, holeRelsEq,
    anchorView, Splice.SiteView.focus] using base

/-- Transport the empty-spine closed certificate into ordered-open compiler
coordinates at a proper nested anchor. -/
theorem properIterationRootOpenAnchorContraction_complete
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hencloses : input.val.Encloses selection.val.anchor target)
    (targetNotSelected : ¬ selection.val.SelectsRegion target)
    (targetNe : target ≠ selection.val.anchor)
    (hzero : (iterationInput input selection target).binderSpine.proxyCount =
      0)
    (sourceBoundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root)
    (hanchor : selection.val.anchor ≠ input.val.root) :
    Nonempty (ProperIterationRootOpenAnchorContraction input selection target
      hadmissible sourceBoundary sourceRoot) := by
  obtain ⟨closed⟩ := properIterationRootAnchorContraction_complete input
    selection target hadmissible hencloses targetNotSelected targetNe hzero
  have targetNeRoot : target ≠
      (iterationInput input selection target).coalesceFrameRaw.root := by
    intro targetRoot
    have anchorEnclosesRoot :
        (iterationInput input selection target).coalesceFrameRaw.Encloses
          selection.val.anchor
          (iterationInput input selection target).coalesceFrameRaw.root := by
      simpa [targetRoot] using Splice.Input.RegionRoute.encloses closed.route
        ((iterationInput input selection target).coalesceFrameRaw_wellFormed
          hadmissible)
    have rootEnclosesAnchor :=
      ((iterationInput input selection target).coalesceFrameRaw_wellFormed
        hadmissible).all_regions_reach_root selection.val.anchor
    apply hanchor
    simpa [Splice.Input.coalesceFrameRaw] using
      ConcreteElaboration.checked_encloses_antisymm
        ((iterationInput input selection target).coalesceFrameRaw_wellFormed
          hadmissible) anchorEnclosesRoot rootEnclosesAnchor
  let openView := iterationCoalescedOpenAnchorView input selection target
    hadmissible sourceBoundary sourceRoot
  let closedView := iterationCoalescedAnchorView input selection target
    hadmissible
  let sourceView := Splice.Input.compiledSpliceCoalescedOpenView
    (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot
  let hne : selection.val.anchor ≠
      (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot).val.diagram.root := by
    simpa [Splice.Input.PlugLayout.checkedCoalescedOpenRoot,
      Splice.Input.PlugLayout.coalescedOpenRoot,
      Splice.Input.coalesceFrameRaw] using hanchor
  let openLeaf := openView.compilerLeaf.nestedOfNe hne
  obtain ⟨hrels, hbinders⟩ :=
    iterationCoalescedOpenAnchor_terminalLexical input selection target
      hadmissible sourceBoundary sourceRoot hanchor
  let castRoot := hrels.symm ▸ closed.root
  let castWitness := closed.witness.castRelsEq hrels.symm
  let castHoleWiresEq : castWitness.toFocus.holeWires =
      closed.witness.toFocus.holeWires :=
    closed.witness.castRelsEq_toFocus_holeWires hrels.symm
  let castHoleRelsEq : castWitness.toFocus.holeRels =
      closed.witness.toFocus.holeRels :=
    closed.witness.castRelsEq_toFocus_holeRels hrels.symm
  let castWire := (FiniteEquiv.finCast castHoleWiresEq).symm
  let castReplacement : Region signature castWitness.toFocus.holeWires
      castWitness.toFocus.holeRels :=
    castHoleRelsEq.symm ▸ closed.replacement.renameWires castWire
  let openFocusLeaf := openLeaf.atFocus
  let closedFocusLeaf := closedView.compilerLeaf.atFocus
  let closedRootLeaf := closedFocusLeaf.castHereBodyEq closed.rootEq.symm
  have hbindersRoot : HEq openFocusLeaf.binders closedRootLeaf.binders := by
    simpa [openFocusLeaf, closedRootLeaf, closedFocusLeaf] using hbinders
  let inherited :=
    Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv
      (.here openView.focus.body) openFocusLeaf (.here closed.root)
      closedRootLeaf
  have inheritedSpec : ∀ index,
      closedRootLeaf.inheritedWires.get (inherited index) =
        openFocusLeaf.inheritedWires.get index := by
    intro index
    exact Splice.Input.Region.ContextPath.CompilerLeaf.sameSiteInheritedEquiv_spec
      (.here openView.focus.body) openFocusLeaf (.here closed.root)
      closedRootLeaf index
  let wire := Splice.Input.compilerLeafOuterWire
    (.here openView.focus.body) openFocusLeaf (.here closed.root)
      closedRootLeaf inherited
  have anchorIsoRaw := Splice.Input.compilerLeaf_regionIso_sameDiagram
    ((iterationInput input selection target).coalesceFrameRaw_wellFormed
      hadmissible)
    (.here openView.focus.body) openFocusLeaf (.here closed.root)
    closedRootLeaf hrels hbindersRoot
  have anchorIso : RegionIso signature wire
      (iterationCoalescedOpenAnchorView input selection target hadmissible
        sourceBoundary sourceRoot).focus.holeRels
      (iterationCoalescedOpenAnchorView input selection target hadmissible
        sourceBoundary sourceRoot).focus.body castRoot := by
    exact RegionIso.of_renamed_relEq hrels wire openView.focus.body
      closed.root anchorIsoRaw
  have castFillEq : castWitness.toFocus.context.fill castReplacement =
      hrels.symm ▸
        closed.witness.toFocus.context.fill closed.replacement := by
    have core := closed.witness.castRelsEq_fill hrels.symm
      closed.replacement
    dsimp only at core
    rw [Region.castWiresEq_castRels,
      Region.castWiresEq_eq_renameWires] at core
    simpa [castWitness, castReplacement, castHoleWiresEq, castHoleRelsEq,
      castWire] using core
  have castActualIso := RegionIso.transportedReplacement_to_actual
    castHoleRelsEq closed.actualRelsEq castWire closed.actualWire
      closed.replacement
      (iterationActualSpliceOfEmpty input selection target hadmissible)
      closed.actualIso
  let castActualRelsEq := castHoleRelsEq.trans closed.actualRelsEq
  let castActualWire := castWire.symm.trans closed.actualWire
  obtain ⟨routeAlignment⟩ :=
    compilerLeaf_sameRouteContextIso_toWitness_with_terminal_of_relEq
      ((iterationInput input selection target).coalesceFrame hadmissible)
      openFocusLeaf closedRootLeaf closed.route hrels inherited inheritedSpec
      hbindersRoot castWitness
  obtain ⟨sourceComparisonResult⟩ := compilerLeaf_routeTrace_complete
    ((iterationInput input selection target).coalesceFrame hadmissible)
    openFocusLeaf closed.route
  let sourceComparisonWitnessRaw := sourceComparisonResult.witness.castWiresEq
    openFocusLeaf.inheritedLength
  let sourceComparisonStateRaw := Splice.compilerLeafHereCastWiresEq
    sourceComparisonResult.state openFocusLeaf.inheritedLength
  let sourceComparisonTraceRaw := sourceComparisonResult.trace.castWiresEq
    closed.route sourceComparisonResult.witness sourceComparisonResult.state
      openFocusLeaf.inheritedLength
  let sourceComparisonBody := Region.castWiresEq
    openFocusLeaf.inheritedLength
    (ConcreteElaboration.finishRegion
      (iterationInput input selection target).coalesceFrameRaw
      openFocusLeaf.inheritedWires selection.val.anchor openFocusLeaf.items)
  have sourceComparisonBodyEq : openView.focus.body =
      sourceComparisonBody := by
    simpa using openFocusLeaf.bodyComputation
  let sourceComparisonRaw : ZeroRoutedCompilerTraceAtBody
      (iterationInput input selection target).coalesceFrameRaw
      selection.val.anchor target closed.route sourceComparisonBody
      sourceComparisonResult.state.inheritedWires := {
    witness := sourceComparisonWitnessRaw
    state := sourceComparisonStateRaw
    trace := sourceComparisonTraceRaw
    initial_eq := by simp [sourceComparisonStateRaw]
  }
  let sourceComparison := sourceComparisonRaw.castBodyEq
    sourceComparisonBodyEq.symm
  have sourceComparisonInitial : sourceComparison.state.inheritedWires =
      openFocusLeaf.inheritedWires :=
    sourceComparison.initial_eq.trans sourceComparisonResult.inherited_eq
  have routeSourceTerminalEq : routeAlignment.sourceTerminalWires =
      sourceComparison.trace.leaf.inheritedWires :=
    routeAlignment.sourceTerminalCoherent sourceComparison.trace
      (by
        change sourceComparison.state.inheritedWires =
          openFocusLeaf.inheritedWires
        exact sourceComparisonInitial)
  have sourceSplitInitial : sourceComparison.state.inheritedWires =
      (openView.result.trace.leaf.nestedOfNe hne).inheritedWires := by
    simpa [openFocusLeaf, openLeaf, Splice.OpenSiteView.compilerLeaf,
      Splice.Region.ContextPath.CompilerLeaf.atFocus] using
        sourceComparisonInitial
  have sourceComparisonCanonical :=
    Splice.Input.OpenCompilerTrace.sameDiagramTerminalInheritedOfSplit
      ((iterationInput input selection target).coalesceFrameRaw_wellFormed
        hadmissible)
      hne openView.result.trace sourceComparison.trace sourceView.result.trace
      sourceSplitInitial
  have sourceTerminalCanonical : routeAlignment.sourceTerminalWires =
      (Splice.Input.compiledSpliceCoalescedNestedLeaf
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot targetNeRoot).inheritedWires := by
    exact routeSourceTerminalEq.trans (by
      simpa [sourceView,
        Splice.Input.compiledSpliceCoalescedNestedLeaf,
        Splice.OpenSiteView.compilerLeaf] using sourceComparisonCanonical)
  let openWitness := routeAlignment.sourceWitness
  let alignment := routeAlignment.alignment
  let sourceReplacement : Region signature
      openWitness.toFocus.holeWires openWitness.toFocus.holeRels :=
    alignment.holeRelsEq.symm ▸
      castReplacement.renameWires alignment.holeWire.symm
  have replacementIso : RegionIso signature alignment.holeWire
      openWitness.toFocus.holeRels sourceReplacement
      (alignment.holeRelsEq.symm ▸ castReplacement) := by
    exact RegionIso.castRelsEqBoth alignment.holeRelsEq
      alignment.holeWire
      (castReplacement.renameWires alignment.holeWire.symm)
      castReplacement
      (RegionIso.renameWiresEquiv castReplacement
        alignment.holeWire.symm).symm
  have filledIsoCore := alignment.contexts.fill replacementIso
  have targetFill := DiagramContext.fill_castHoleRels
    alignment.holeRelsEq.symm castWitness.toFocus.context castReplacement
  have filledIso : RegionIso signature wire openView.focus.holeRels
      (openWitness.toFocus.context.fill sourceReplacement)
      (castWitness.toFocus.context.fill castReplacement) := by
    exact targetFill ▸ filledIsoCore
  have actualIso := RegionIso.transportedReplacement_to_actual
    alignment.holeRelsEq castActualRelsEq alignment.holeWire.symm
      castActualWire castReplacement
      (iterationActualSpliceOfEmpty input selection target hadmissible)
      (by simpa [castReplacement, castActualRelsEq, castActualWire] using
        castActualIso)
  let sourceActualRelsEq := alignment.holeRelsEq.trans castActualRelsEq
  let sourceActualWire := alignment.holeWire.trans castActualWire
  obtain ⟨terminalComparison⟩ := compilerLeaf_routeTrace_complete
    ((iterationInput input selection target).coalesceFrame hadmissible)
    closedRootLeaf closed.route
  let comparisonWitnessRaw := terminalComparison.witness.castWiresEq
    closedRootLeaf.inheritedLength
  let comparisonStateRaw := Splice.compilerLeafHereCastWiresEq
    terminalComparison.state closedRootLeaf.inheritedLength
  let comparisonTraceRaw := terminalComparison.trace.castWiresEq closed.route
    terminalComparison.witness terminalComparison.state
      closedRootLeaf.inheritedLength
  let comparisonBody := Region.castWiresEq
      closedRootLeaf.inheritedLength
      (ConcreteElaboration.finishRegion
        (iterationInput input selection target).coalesceFrameRaw
        closedRootLeaf.inheritedWires selection.val.anchor
        closedRootLeaf.items)
  have comparisonBodyEq : closed.root = comparisonBody := by
    simpa using closedRootLeaf.bodyComputation
  let comparisonRaw : ZeroRoutedCompilerTraceAtBody
      (iterationInput input selection target).coalesceFrameRaw
      selection.val.anchor target closed.route comparisonBody
      terminalComparison.state.inheritedWires := {
    witness := comparisonWitnessRaw
    state := comparisonStateRaw
    trace := comparisonTraceRaw
    initial_eq := by simp [comparisonStateRaw]
  }
  let comparison := comparisonRaw.castBodyEq comparisonBodyEq.symm
  let comparisonState := comparison.state
  let comparisonTrace := comparison.trace
  have comparisonInitialRoot : comparisonState.inheritedWires =
      closedRootLeaf.inheritedWires :=
    comparison.initial_eq.trans terminalComparison.inherited_eq
  have comparisonInitial : comparisonState.inheritedWires =
      closedView.compilerLeaf.atFocus.inheritedWires := by
    exact comparisonInitialRoot.trans (by
      simp [closedRootLeaf, closedFocusLeaf])
  have closedTerminalEq : closed.terminalWires =
      comparisonTrace.leaf.inheritedWires :=
    closed.terminalCoherent comparisonTrace comparisonInitial
  have routeTerminalEq : routeAlignment.targetTerminalWires =
      comparisonTrace.leaf.inheritedWires :=
    routeAlignment.targetTerminalCoherent comparisonTrace
      comparisonInitialRoot
  have terminalListsEq : closed.terminalWires =
      routeAlignment.targetTerminalWires :=
    closedTerminalEq.trans routeTerminalEq.symm
  have targetActualWireSpec : ∀ index : Fin castWitness.toFocus.holeWires,
      (Splice.Input.compiledSpliceHostView
          (iterationInput input selection target) hadmissible
        ).compilerLeaf.inheritedWires.get
          (Fin.cast
            (Splice.Input.compiledSpliceHostView
              (iterationInput input selection target) hadmissible
            ).compilerLeaf.inheritedLength.symm (castActualWire index)) =
        routeAlignment.targetTerminalWires.get
          (Fin.cast routeAlignment.targetTerminalLength.symm index) := by
    intro index
    let closedIndex := castWire.symm index
    have core := closed.actualWireSpec closedIndex
    simpa [castActualWire, closedIndex, castWire, terminalListsEq,
      FiniteEquiv.trans] using core
  refine ⟨{
    target_ne_anchor := targetNe
    anchor_ne_root := hanchor
    target_ne_root := targetNeRoot
    path := closed.path
    route := closed.route
    witness := openWitness
    replacement := sourceReplacement
    actualRelsEq := sourceActualRelsEq
    actualWire := sourceActualWire
    routeTargetHoleWires := castWitness.toFocus.holeWires
    routeWire := alignment.holeWire
    targetActualWire := castActualWire
    actualWire_factor := rfl
    sourceTerminalLeaf := routeAlignment.sourceTerminalLeaf
    sourceTerminalWires := routeAlignment.sourceTerminalWires
    targetTerminalWires := routeAlignment.targetTerminalWires
    sourceTerminalLength := routeAlignment.sourceTerminalLength
    targetTerminalLength := routeAlignment.targetTerminalLength
    sourceTerminalWires_eq := routeAlignment.sourceTerminalWires_eq
    sourceTerminalCanonical := sourceTerminalCanonical
    terminalWireSpec := routeAlignment.terminalWireSpec
    actualWireSpec := by
      intro index
      exact (targetActualWireSpec (alignment.holeWire index)).trans
        (routeAlignment.terminalWireSpec index)
    actualIso := by
      simpa [sourceReplacement, sourceActualRelsEq, sourceActualWire] using
        actualIso
    equivalent := ?_
  }⟩
  intro model named environment relEnv
  apply RegionIso.source_equiv_of_target_equiv anchorIso filledIso
  intro targetModel targetNamed targetEnvironment targetRelEnv
  change denoteRegion targetModel targetNamed targetEnvironment targetRelEnv
      (hrels.symm ▸ closed.root) ↔
    denoteRegion targetModel targetNamed targetEnvironment targetRelEnv
      (castWitness.toFocus.context.fill castReplacement)
  calc
    _ ↔ denoteRegion targetModel targetNamed targetEnvironment
        (hrels ▸ targetRelEnv) closed.root := by
      simpa using denoteRegion_castRels_iff hrels.symm closed.root
        targetModel targetNamed targetEnvironment targetRelEnv
    _ ↔ denoteRegion targetModel targetNamed targetEnvironment
        (hrels ▸ targetRelEnv)
        (closed.witness.toFocus.context.fill closed.replacement) :=
      by simpa [closed.rootEq] using
        closed.equivalent targetModel targetNamed targetEnvironment
          (hrels ▸ targetRelEnv)
    _ ↔ _ := by
      rw [castFillEq]
      simpa using (denoteRegion_castRels_iff hrels.symm
        (closed.witness.toFocus.context.fill closed.replacement)
        targetModel targetNamed targetEnvironment targetRelEnv).symm

/-- An empty-spine scoped ordered-open contraction lifts through every
enclosing cut to the complete ordered-open root diagram. -/
theorem ProperIterationRootOpenAnchorContraction.wholeOpen_equiv
    {input : CheckedDiagram signature}
    {selection : CheckedSelection input.val}
    {target : Fin input.val.regionCount}
    {hadmissible : (iterationInput input selection target).Admissible}
    {sourceBoundary : List (Fin input.val.wireCount)}
    {sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.val.wires wire).scope = input.val.root}
    (certificate : ProperIterationRootOpenAnchorContraction input selection
      target hadmissible sourceBoundary sourceRoot)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin
      (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot).val.boundary.length → model.Carrier) :
    let source :=
      (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
        (iterationInput input selection target) hadmissible sourceBoundary
        sourceRoot).elaborate
    let anchorView := iterationCoalescedOpenAnchorView input selection target
      hadmissible sourceBoundary sourceRoot
    let modifiedBody := anchorView.focus.context.fill
      (certificate.witness.toFocus.context.fill certificate.replacement)
    denoteOpen model named source args ↔
      denoteOpen model named (Splice.replaceOpenBody source modifiedBody)
        args := by
  dsimp only
  let source :=
    (Splice.Input.PlugLayout.checkedCoalescedOpenRoot
      (iterationInput input selection target) hadmissible sourceBoundary
      sourceRoot).elaborate
  let anchorView := iterationCoalescedOpenAnchorView input selection target
    hadmissible sourceBoundary sourceRoot
  let modifiedBody := anchorView.focus.context.fill
    (certificate.witness.toFocus.context.fill certificate.replacement)
  have bodyEquiv : ∀ env : Fin source.externalClasses → model.Carrier,
      denoteRegion (relCtx := []) model named env
          (PUnit.unit : RelEnv model.Carrier [])
          source.body ↔
        denoteRegion (relCtx := []) model named env
          (PUnit.unit : RelEnv model.Carrier [])
          modifiedBody := by
    intro env
    rw [← anchorView.rebuild]
    exact DiagramContext.fill_equiv anchorView.focus.context
      anchorView.focus.body
      (certificate.witness.toFocus.context.fill certificate.replacement)
      model named env (PUnit.unit : RelEnv model.Carrier [])
      (fun holeEnv holeRelEnv =>
        certificate.equivalent model named holeEnv holeRelEnv)
  exact (Splice.denote_replaceOpenBody_iff source modifiedBody model named args
    (fun env => (bodyEquiv env).symm)).symm

end VisualProof.Rule.IterationSoundness
