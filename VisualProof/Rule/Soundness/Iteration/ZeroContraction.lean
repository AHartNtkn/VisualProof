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

end VisualProof.Rule.IterationSoundness
