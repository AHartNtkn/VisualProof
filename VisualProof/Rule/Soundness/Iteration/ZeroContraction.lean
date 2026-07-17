import VisualProof.Rule.Soundness.Iteration.CanonicalContraction

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Rule.ModalSoundness

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

end VisualProof.Rule.IterationSoundness
