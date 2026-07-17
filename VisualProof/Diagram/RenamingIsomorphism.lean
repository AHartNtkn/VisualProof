import VisualProof.Diagram.Algebra

namespace VisualProof.Diagram

open VisualProof
open Theory

private def RegionIsoRenamingMotive {signature : List Nat}
    {sourceWires targetWires : Nat}
    (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (rels : RelCtx) (source : Region signature sourceWires rels)
    (target : Region signature targetWires rels)
    (_ : RegionIso signature wire rels source target) : Prop :=
  ∀ {renamedSourceWires renamedTargetWires : Nat}
    (sourceMap : Fin sourceWires → Fin renamedSourceWires)
    (targetMap : Fin targetWires → Fin renamedTargetWires)
    (renamedWire : FiniteEquiv
      (Fin renamedSourceWires) (Fin renamedTargetWires)),
    renamedWire.toFun ∘ sourceMap = targetMap ∘ wire.toFun →
      RegionIso signature renamedWire rels
        (source.renameWires sourceMap) (target.renameWires targetMap)

private def ItemIsoRenamingMotive {signature : List Nat}
    {sourceWires targetWires : Nat}
    (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (rels : RelCtx) (source : Item signature sourceWires rels)
    (target : Item signature targetWires rels)
    (_ : ItemIso signature wire rels source target) : Prop :=
  ∀ {renamedSourceWires renamedTargetWires : Nat}
    (sourceMap : Fin sourceWires → Fin renamedSourceWires)
    (targetMap : Fin targetWires → Fin renamedTargetWires)
    (renamedWire : FiniteEquiv
      (Fin renamedSourceWires) (Fin renamedTargetWires)),
    renamedWire.toFun ∘ sourceMap = targetMap ∘ wire.toFun →
      ItemIso signature renamedWire rels
        (source.renameWires sourceMap) (target.renameWires targetMap)

private def ItemSeqIsoRenamingMotive {signature : List Nat}
    {sourceWires targetWires : Nat}
    (wire : FiniteEquiv (Fin sourceWires) (Fin targetWires))
    (rels : RelCtx) (source : ItemSeq signature sourceWires rels)
    (target : ItemSeq signature targetWires rels)
    (_ : ItemSeqIso signature wire rels source target) : Prop :=
  ∀ {renamedSourceWires renamedTargetWires : Nat}
    (sourceMap : Fin sourceWires → Fin renamedSourceWires)
    (targetMap : Fin targetWires → Fin renamedTargetWires)
    (renamedWire : FiniteEquiv
      (Fin renamedSourceWires) (Fin renamedTargetWires)),
    renamedWire.toFun ∘ sourceMap = targetMap ∘ wire.toFun →
      ItemSeqIso signature renamedWire rels
        (source.renameWires sourceMap) (target.renameWires targetMap)

private theorem extendWireRenaming_commutes
    (wire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (localWire : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
    (sourceMap : Fin sourceOuter → Fin renamedSourceOuter)
    (targetMap : Fin targetOuter → Fin renamedTargetOuter)
    (renamedWire : FiniteEquiv
      (Fin renamedSourceOuter) (Fin renamedTargetOuter))
    (commutes : renamedWire.toFun ∘ sourceMap =
      targetMap ∘ wire.toFun) :
    (extendWireEquiv renamedWire localWire).toFun ∘
        extendWireRenaming sourceMap sourceLocal =
      extendWireRenaming targetMap targetLocal ∘
        (extendWireEquiv wire localWire).toFun := by
  funext index
  refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_) index
  · have outer := congrFun commutes inherited
    simpa [extendWireRenaming] using
      congrArg (Fin.castAdd targetLocal) outer
  · simp [extendWireRenaming]

private theorem regionIsoRenamingCase
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {sourceItems : ItemSeq signature (sourceWires + sourceLocal) rels}
    {targetItems : ItemSeq signature (targetWires + targetLocal) rels}
    (localWire : FiniteEquiv (Fin sourceLocal) (Fin targetLocal))
    (items : ItemSeqIso signature (extendWireEquiv wire localWire) rels
      sourceItems targetItems)
    (itemsIH : ItemSeqIsoRenamingMotive
      (extendWireEquiv wire localWire) rels sourceItems targetItems items) :
    RegionIsoRenamingMotive wire rels (.mk sourceLocal sourceItems)
      (.mk targetLocal targetItems) (.mk localWire items) := by
  intro renamedSource renamedTarget sourceMap targetMap renamedWire commutes
  apply RegionIso.mk localWire
  exact itemsIH (extendWireRenaming sourceMap sourceLocal)
    (extendWireRenaming targetMap targetLocal)
    (extendWireEquiv renamedWire localWire)
    (extendWireRenaming_commutes wire localWire sourceMap targetMap renamedWire
      commutes)

private theorem equationIsoRenamingCase
    {signature : List Nat}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {sourceOutput : Fin sourceWires} {targetOutput : Fin targetWires}
    {sourceTerm : Lambda.Term 0 (Fin sourceWires)}
    {targetTerm : Lambda.Term 0 (Fin targetWires)}
    (outputEq : wire sourceOutput = targetOutput)
    (termEq : sourceTerm.mapFree wire = targetTerm) :
    ItemIsoRenamingMotive (signature := signature) wire rels
      (.equation sourceOutput sourceTerm)
      (.equation targetOutput targetTerm)
      (ItemIso.equation (signature := signature) outputEq termEq) := by
  intro renamedSource renamedTarget sourceMap targetMap renamedWire commutes
  apply ItemIso.equation
  · have mapped := congrFun commutes sourceOutput
    simpa [outputEq] using mapped
  · rw [Lambda.Term.mapFree_comp]
    have functionEq : renamedWire.toFun ∘ sourceMap =
        targetMap ∘ wire.toFun := commutes
    rw [functionEq, ← Lambda.Term.mapFree_comp, termEq]

private theorem atomIsoRenamingCase
    {signature : List Nat}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    (relation : RelVar rels arity)
    {sourceArguments : Fin arity → Fin sourceWires}
    {targetArguments : Fin arity → Fin targetWires}
    (argumentsEq : wire.toFun ∘ sourceArguments = targetArguments) :
    ItemIsoRenamingMotive (signature := signature) wire rels
      (.atom relation sourceArguments) (.atom relation targetArguments)
      (ItemIso.atom (signature := signature) relation argumentsEq) := by
  intro renamedSource renamedTarget sourceMap targetMap renamedWire commutes
  apply ItemIso.atom relation
  funext index
  have mapped := congrFun commutes (sourceArguments index)
  simpa [Function.comp_apply, ← argumentsEq] using mapped

private theorem namedIsoRenamingCase
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    (relation : NamedRel signature arity)
    {sourceArguments : Fin arity → Fin sourceWires}
    {targetArguments : Fin arity → Fin targetWires}
    (argumentsEq : wire.toFun ∘ sourceArguments = targetArguments) :
    ItemIsoRenamingMotive wire rels (.named relation sourceArguments)
      (.named relation targetArguments) (.named relation argumentsEq) := by
  intro renamedSource renamedTarget sourceMap targetMap renamedWire commutes
  apply ItemIso.named relation
  funext index
  have mapped := congrFun commutes (sourceArguments index)
  simpa [Function.comp_apply, ← argumentsEq] using mapped

private theorem cutIsoRenamingCase
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {sourceBody : Region signature sourceWires rels}
    {targetBody : Region signature targetWires rels}
    (body : RegionIso signature wire rels sourceBody targetBody)
    (bodyIH : RegionIsoRenamingMotive wire rels sourceBody targetBody body) :
    ItemIsoRenamingMotive wire rels (.cut sourceBody) (.cut targetBody)
      (.cut body) := by
  intro renamedSource renamedTarget sourceMap targetMap renamedWire commutes
  exact ItemIso.cut (bodyIH sourceMap targetMap renamedWire commutes)

private theorem bubbleIsoRenamingCase
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {sourceBody : Region signature sourceWires (arity :: rels)}
    {targetBody : Region signature targetWires (arity :: rels)}
    (body : RegionIso signature wire (arity :: rels) sourceBody targetBody)
    (bodyIH : RegionIsoRenamingMotive wire (arity :: rels)
      sourceBody targetBody body) :
    ItemIsoRenamingMotive wire rels (.bubble arity sourceBody)
      (.bubble arity targetBody) (.bubble body) := by
  intro renamedSource renamedTarget sourceMap targetMap renamedWire commutes
  exact ItemIso.bubble (bodyIH sourceMap targetMap renamedWire commutes)

private theorem itemSeqIsoRenamingCase
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {source : ItemSeq signature sourceWires rels}
    {target : ItemSeq signature targetWires rels}
    (positions : FiniteEquiv (Fin source.length) (Fin target.length))
    (items : ∀ index, ItemIso signature wire rels
      (source.get index) (target.get (positions index)))
    (itemsIH : ∀ index, ItemIsoRenamingMotive wire rels
      (source.get index) (target.get (positions index)) (items index)) :
    ItemSeqIsoRenamingMotive wire rels source target
      (.permute positions items) := by
  intro renamedSource renamedTarget sourceMap targetMap renamedWire commutes
  let sourcePositions := source.renameWiresPositionEquiv sourceMap
  let targetPositions := target.renameWiresPositionEquiv targetMap
  let renamedPositions := sourcePositions.symm.trans
    (positions.trans targetPositions)
  refine ItemSeqIso.permute renamedPositions ?_
  intro renamedIndex
  let sourceIndex := sourcePositions.symm renamedIndex
  have transported := itemsIH sourceIndex sourceMap targetMap renamedWire commutes
  have sourceIndexEq : sourcePositions sourceIndex = renamedIndex :=
    sourcePositions.right_inv renamedIndex
  rw [← sourceIndexEq]
  change ItemIso signature renamedWire rels
    ((source.renameWires sourceMap).get (sourcePositions sourceIndex))
    ((target.renameWires targetMap).get
      (targetPositions (positions sourceIndex)))
  rw [ItemSeq.get_renameWires source sourceMap sourceIndex,
    ItemSeq.get_renameWires target targetMap (positions sourceIndex)]
  exact transported

private theorem regionIsoRenamingRec
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {source : Region signature sourceWires rels}
    {target : Region signature targetWires rels}
    (iso : RegionIso signature wire rels source target) :
    RegionIsoRenamingMotive wire rels source target iso := by
  exact RegionIso.rec
    (motive_1 := RegionIsoRenamingMotive)
    (motive_2 := ItemIsoRenamingMotive)
    (motive_3 := ItemSeqIsoRenamingMotive)
    regionIsoRenamingCase equationIsoRenamingCase atomIsoRenamingCase
    namedIsoRenamingCase cutIsoRenamingCase bubbleIsoRenamingCase
    itemSeqIsoRenamingCase iso

private theorem itemIsoRenamingRec
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {source : Item signature sourceWires rels}
    {target : Item signature targetWires rels}
    (iso : ItemIso signature wire rels source target) :
    ItemIsoRenamingMotive wire rels source target iso := by
  exact ItemIso.rec
    (motive_1 := RegionIsoRenamingMotive)
    (motive_2 := ItemIsoRenamingMotive)
    (motive_3 := ItemSeqIsoRenamingMotive)
    regionIsoRenamingCase equationIsoRenamingCase atomIsoRenamingCase
    namedIsoRenamingCase cutIsoRenamingCase bubbleIsoRenamingCase
    itemSeqIsoRenamingCase iso

private theorem itemSeqIsoRenamingRec
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {source : ItemSeq signature sourceWires rels}
    {target : ItemSeq signature targetWires rels}
    (iso : ItemSeqIso signature wire rels source target) :
    ItemSeqIsoRenamingMotive wire rels source target iso := by
  exact ItemSeqIso.rec
    (motive_1 := RegionIsoRenamingMotive)
    (motive_2 := ItemIsoRenamingMotive)
    (motive_3 := ItemSeqIsoRenamingMotive)
    regionIsoRenamingCase equationIsoRenamingCase atomIsoRenamingCase
    namedIsoRenamingCase cutIsoRenamingCase bubbleIsoRenamingCase
    itemSeqIsoRenamingCase iso

/-- Transport a region isomorphism through arbitrary wire renamings whose
square commutes. -/
theorem RegionIso.renameWires_commuting
    {sourceWires targetWires renamedSourceWires renamedTargetWires : Nat}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {rels : RelCtx}
    {source : Region signature sourceWires rels}
    {target : Region signature targetWires rels}
    (iso : RegionIso signature wire rels source target)
    (sourceMap : Fin sourceWires → Fin renamedSourceWires)
    (targetMap : Fin targetWires → Fin renamedTargetWires)
    (renamedWire : FiniteEquiv
      (Fin renamedSourceWires) (Fin renamedTargetWires))
    (commutes : renamedWire.toFun ∘ sourceMap =
      targetMap ∘ wire.toFun) :
    RegionIso signature renamedWire rels
      (source.renameWires sourceMap) (target.renameWires targetMap) :=
  regionIsoRenamingRec iso sourceMap targetMap renamedWire commutes

theorem ItemIso.renameWires_commuting
    {sourceWires targetWires renamedSourceWires renamedTargetWires : Nat}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {rels : RelCtx}
    {source : Item signature sourceWires rels}
    {target : Item signature targetWires rels}
    (iso : ItemIso signature wire rels source target)
    (sourceMap : Fin sourceWires → Fin renamedSourceWires)
    (targetMap : Fin targetWires → Fin renamedTargetWires)
    (renamedWire : FiniteEquiv
      (Fin renamedSourceWires) (Fin renamedTargetWires))
    (commutes : renamedWire.toFun ∘ sourceMap =
      targetMap ∘ wire.toFun) :
    ItemIso signature renamedWire rels
      (source.renameWires sourceMap) (target.renameWires targetMap) :=
  itemIsoRenamingRec iso sourceMap targetMap renamedWire commutes

theorem ItemSeqIso.renameWires_commuting
    {sourceWires targetWires renamedSourceWires renamedTargetWires : Nat}
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {rels : RelCtx}
    {source : ItemSeq signature sourceWires rels}
    {target : ItemSeq signature targetWires rels}
    (iso : ItemSeqIso signature wire rels source target)
    (sourceMap : Fin sourceWires → Fin renamedSourceWires)
    (targetMap : Fin targetWires → Fin renamedTargetWires)
    (renamedWire : FiniteEquiv
      (Fin renamedSourceWires) (Fin renamedTargetWires))
    (commutes : renamedWire.toFun ∘ sourceMap =
      targetMap ∘ wire.toFun) :
    ItemSeqIso signature renamedWire rels
      (source.renameWires sourceMap) (target.renameWires targetMap) :=
  itemSeqIsoRenamingRec iso sourceMap targetMap renamedWire commutes

/-- Concatenate two item-sequence isomorphisms that use the same ambient wire
transport, preserving the order of the two blocks. -/
theorem ItemSeqIso.append
    {wire : FiniteEquiv (Fin sourceWires) (Fin targetWires)}
    {sourceFirst sourceSecond : ItemSeq signature sourceWires rels}
    {targetFirst targetSecond : ItemSeq signature targetWires rels}
    (first : ItemSeqIso signature wire rels sourceFirst targetFirst)
    (second : ItemSeqIso signature wire rels sourceSecond targetSecond) :
    ItemSeqIso signature wire rels
      (sourceFirst.append sourceSecond) (targetFirst.append targetSecond) := by
  cases first with
  | permute firstPositions firstItems =>
      cases second with
      | permute secondPositions secondItems =>
          let positions :=
            (FiniteEquiv.finCast
              (ItemSeq.length_append sourceFirst sourceSecond)).trans
            ((extendWireEquiv firstPositions secondPositions).trans
              (FiniteEquiv.finCast
                (ItemSeq.length_append targetFirst targetSecond).symm))
          refine ItemSeqIso.permute positions ?_
          intro index
          let sourceSum : Fin (sourceFirst.length + sourceSecond.length) :=
            Fin.cast (ItemSeq.length_append sourceFirst sourceSecond) index
          refine Fin.addCases (motive := fun split => sourceSum = split →
              ItemIso signature wire rels
                ((sourceFirst.append sourceSecond).get index)
                ((targetFirst.append targetSecond).get (positions index)))
            (fun firstIndex sourceEq => ?_)
            (fun secondIndex sourceEq => ?_) sourceSum rfl
          · have indexEq : index = Fin.cast
                (ItemSeq.length_append sourceFirst sourceSecond).symm
                (Fin.castAdd sourceSecond.length firstIndex) := by
              apply Fin.ext
              simpa [sourceSum] using congrArg Fin.val sourceEq
            subst index
            rw [ItemSeq.get_append_left]
            have targetEq : positions
                (Fin.cast (ItemSeq.length_append sourceFirst sourceSecond).symm
                  (Fin.castAdd sourceSecond.length firstIndex)) =
                Fin.cast
                  (ItemSeq.length_append targetFirst targetSecond).symm
                  (Fin.castAdd targetSecond.length
                    (firstPositions firstIndex)) := by
              apply Fin.ext
              simp [positions, FiniteEquiv.finCast]
            rw [targetEq, ItemSeq.get_append_left]
            exact firstItems firstIndex
          · have indexEq : index = Fin.cast
                (ItemSeq.length_append sourceFirst sourceSecond).symm
                (Fin.natAdd sourceFirst.length secondIndex) := by
              apply Fin.ext
              simpa [sourceSum] using congrArg Fin.val sourceEq
            subst index
            rw [ItemSeq.get_append_right]
            have targetEq : positions
                (Fin.cast (ItemSeq.length_append sourceFirst sourceSecond).symm
                  (Fin.natAdd sourceFirst.length secondIndex)) =
                Fin.cast
                  (ItemSeq.length_append targetFirst targetSecond).symm
                  (Fin.natAdd targetFirst.length
                    (secondPositions secondIndex)) := by
              apply Fin.ext
              simp [positions, FiniteEquiv.finCast]
            rw [targetEq, ItemSeq.get_append_right]
            exact secondItems secondIndex

private theorem adjoinHostWire_commutes
    (outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (hostLocalWire : FiniteEquiv (Fin sourceHostLocal) (Fin targetHostLocal))
    (addedLocalWire : FiniteEquiv
      (Fin sourceAddedLocal) (Fin targetAddedLocal)) :
    (extendWireEquiv outerWire
        (extendWireEquiv hostLocalWire addedLocalWire)).toFun ∘
        Region.adjoinHostWire sourceOuter sourceHostLocal sourceAddedLocal =
      Region.adjoinHostWire targetOuter targetHostLocal targetAddedLocal ∘
        (extendWireEquiv outerWire hostLocalWire).toFun := by
  funext wire
  refine Fin.addCases (fun inherited => ?_) (fun hostLocal => ?_) wire
  · simp
  · simp

private theorem adjoinMaterialWire_commutes
    (outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (hostLocalWire : FiniteEquiv (Fin sourceHostLocal) (Fin targetHostLocal))
    (addedLocalWire : FiniteEquiv
      (Fin sourceAddedLocal) (Fin targetAddedLocal)) :
    (extendWireEquiv outerWire
        (extendWireEquiv hostLocalWire addedLocalWire)).toFun ∘
        Region.adjoinMaterialWire sourceOuter sourceHostLocal sourceAddedLocal =
      Region.adjoinMaterialWire targetOuter targetHostLocal targetAddedLocal ∘
        (extendWireEquiv
          (extendWireEquiv outerWire hostLocalWire) addedLocalWire).toFun := by
  funext wire
  refine Fin.addCases (fun prior => ?_) (fun added => ?_) wire
  · refine Fin.addCases (fun inherited => ?_) (fun hostLocal => ?_) prior
    · simp
    · simp
  · simp

/-- The intrinsic splice kernel preserves a host item isomorphism when the
material wire substitutions commute with its complete host-wire transport.
The relation substitution is shared on both sides. -/
theorem RegionIso.spliceAt
    {outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter)}
    {hostLocalWire : FiniteEquiv
      (Fin sourceHostLocal) (Fin targetHostLocal)}
    {sourceHostItems : ItemSeq signature
      (sourceOuter + sourceHostLocal) hostRels}
    {targetHostItems : ItemSeq signature
      (targetOuter + targetHostLocal) hostRels}
    (hostItems : ItemSeqIso signature
      (extendWireEquiv outerWire hostLocalWire) hostRels
      sourceHostItems targetHostItems)
    (material : Region signature patternWires patternRels)
    (sourceWireMap : Fin patternWires →
      Fin (sourceOuter + sourceHostLocal))
    (targetWireMap : Fin patternWires →
      Fin (targetOuter + targetHostLocal))
    (wireFactor :
      (extendWireEquiv outerWire hostLocalWire).toFun ∘ sourceWireMap =
        targetWireMap)
    (relationMap : RelationRenaming patternRels hostRels) :
    RegionIso signature outerWire hostRels
      (Region.spliceAt sourceHostLocal sourceHostItems material sourceWireMap
        relationMap)
      (Region.spliceAt targetHostLocal targetHostItems material targetWireMap
        relationMap) := by
  let hostWire := extendWireEquiv outerWire hostLocalWire
  have renamedMaterial : RegionIso signature hostWire patternRels
      (material.renameWires sourceWireMap)
      (material.renameWires targetWireMap) := by
    have renamed := RegionIso.renameWiresEquiv
      (material.renameWires sourceWireMap) hostWire
    simpa [hostWire, Region.renameWires_comp, wireFactor] using renamed
  have substitutedMaterial := renamedMaterial.renameRelations relationMap
  unfold Region.spliceAt Region.adjoinAt
  generalize sourceMaterialEq :
      (material.renameWires sourceWireMap).renameRelations relationMap =
        sourceMaterial at substitutedMaterial ⊢
  generalize targetMaterialEq :
      (material.renameWires targetWireMap).renameRelations relationMap =
        targetMaterial at substitutedMaterial ⊢
  cases sourceMaterial with
  | mk sourceAddedLocal sourceAddedItems =>
      cases targetMaterial with
      | mk targetAddedLocal targetAddedItems =>
          cases substitutedMaterial with
          | mk addedLocalWire addedItems =>
              let outputLocalWire :=
                extendWireEquiv hostLocalWire addedLocalWire
              let outputWire := extendWireEquiv outerWire outputLocalWire
              have hostOutput := hostItems.renameWires_commuting
                (Region.adjoinHostWire sourceOuter sourceHostLocal
                  sourceAddedLocal)
                (Region.adjoinHostWire targetOuter targetHostLocal
                  targetAddedLocal)
                outputWire
                (adjoinHostWire_commutes outerWire hostLocalWire
                  addedLocalWire)
              have materialOutput := addedItems.renameWires_commuting
                (Region.adjoinMaterialWire sourceOuter sourceHostLocal
                  sourceAddedLocal)
                (Region.adjoinMaterialWire targetOuter targetHostLocal
                  targetAddedLocal)
                outputWire
                (adjoinMaterialWire_commutes outerWire hostLocalWire
                  addedLocalWire)
              exact RegionIso.mk outputLocalWire
                (hostOutput.append materialOutput)

/-- Relation renaming commutes with capture-avoiding insertion; the host
renaming composes after the material-to-host substitution. -/
theorem Region.spliceAt_renameRelations
    (hostLocal : Nat)
    (hostItems : ItemSeq signature (outer + hostLocal) sourceHostRels)
    (material : Region signature patternWires patternRels)
    (wireMap : Fin patternWires → Fin (outer + hostLocal))
    (materialRelation : RelationRenaming patternRels sourceHostRels)
    (hostRelation : RelationRenaming sourceHostRels targetHostRels) :
    (Region.spliceAt hostLocal hostItems material wireMap materialRelation
      ).renameRelations hostRelation =
      Region.spliceAt hostLocal (hostItems.renameRelations hostRelation)
        material wireMap (fun relation =>
          hostRelation (materialRelation relation)) := by
  cases material with
  | mk addedLocal addedItems =>
      simp only [Region.spliceAt, Region.adjoinAt, Region.renameWires,
        Region.renameRelations, ItemSeq.renameRelations_append,
        ItemSeq.renameWires_renameRelations]
      rw [← ItemSeq.renameWires_renameRelations]
      have composed := Region.renameRelations_comp
        (Region.mk addedLocal addedItems) materialRelation hostRelation
      simp only [Region.renameRelations] at composed
      have itemEq := eq_of_heq (Region.mk.inj composed).2
      rw [itemEq]

/-- Relation-changing counterpart of `RegionIso.spliceAt`. -/
theorem RegionIso.spliceAt_renameRelations
    {outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter)}
    {hostLocalWire : FiniteEquiv
      (Fin sourceHostLocal) (Fin targetHostLocal)}
    {sourceHostItems : ItemSeq signature
      (sourceOuter + sourceHostLocal) sourceHostRels}
    {targetHostItems : ItemSeq signature
      (targetOuter + targetHostLocal) targetHostRels}
    (hostItems : ItemSeqIso signature
      (extendWireEquiv outerWire hostLocalWire) targetHostRels
      (sourceHostItems.renameRelations hostRelation) targetHostItems)
    (material : Region signature patternWires patternRels)
    (sourceWireMap : Fin patternWires →
      Fin (sourceOuter + sourceHostLocal))
    (targetWireMap : Fin patternWires →
      Fin (targetOuter + targetHostLocal))
    (wireFactor :
      (extendWireEquiv outerWire hostLocalWire).toFun ∘ sourceWireMap =
        targetWireMap)
    (sourceRelationMap : RelationRenaming patternRels sourceHostRels)
    (targetRelationMap : RelationRenaming patternRels targetHostRels)
    (relationFactor : ∀ {arity} (relation : RelVar patternRels arity),
      targetRelationMap relation =
        hostRelation (sourceRelationMap relation)) :
    RegionIso signature outerWire targetHostRels
      ((Region.spliceAt sourceHostLocal sourceHostItems material sourceWireMap
        sourceRelationMap).renameRelations hostRelation)
      (Region.spliceAt targetHostLocal targetHostItems material targetWireMap
        targetRelationMap) := by
  rw [Region.spliceAt_renameRelations]
  let composed : RelationRenaming patternRels targetHostRels :=
    fun {arity} (relation : RelVar patternRels arity) =>
      hostRelation (sourceRelationMap relation)
  have relationEq : @targetRelationMap = @composed := by
    funext arity relation
    exact relationFactor relation
  rw [relationEq]
  exact RegionIso.spliceAt hostItems material sourceWireMap targetWireMap
    wireFactor composed

end VisualProof.Diagram
