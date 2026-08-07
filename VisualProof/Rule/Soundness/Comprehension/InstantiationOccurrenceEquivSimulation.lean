import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvanceFrameNodeSemantic

namespace VisualProof.Rule

open VisualProof.Concrete

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- A proof-relevant equivalence of compiler occurrence positions lifts
pointwise item simulation to the complete ordered conjunction.  The
logical conjunction is insensitive to the dense enumeration order, while the
compiler receipts and `get` equations remain exact. -/
theorem compileOccurrences_simulation_of_equiv
    {source target : Concrete.Diagram}
    (sourceRecurse : ∀ {rels : RelCtx},
      (region : Fin source.regionCount) →
      (context : Concrete.Elaboration.WireContext source) →
      Concrete.Elaboration.BinderContext source rels →
      Option (Region  context.length rels))
    (targetRecurse : ∀ {rels : RelCtx},
      (region : Fin target.regionCount) →
      (context : Concrete.Elaboration.WireContext target) →
      Concrete.Elaboration.BinderContext target rels →
      Option (Region  context.length rels))
    (sourceContext : Concrete.Elaboration.WireContext source)
    (targetContext : Concrete.Elaboration.WireContext target)
    (sourceBinders : Concrete.Elaboration.BinderContext source sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext target targetRels)
    (sourceOccurrences : List (Concrete.Elaboration.LocalOccurrence
      source.regionCount source.nodeCount))
    (targetOccurrences : List (Concrete.Elaboration.LocalOccurrence
      target.regionCount target.nodeCount))
    (positions : FiniteEquiv (Fin sourceOccurrences.length)
      (Fin targetOccurrences.length))
    (mapOccurrence : Concrete.Elaboration.LocalOccurrence source.regionCount
      source.nodeCount → Concrete.Elaboration.LocalOccurrence target.regionCount
        target.nodeCount)
    (positionSpec : ∀ index,
      targetOccurrences.get (positions index) =
        mapOccurrence (sourceOccurrences.get index))
    (model : Model)
    (direction : Concrete.Elaboration.SimulationDirection)
    (relation : Concrete.Elaboration.ContextIndexRelation sourceContext.length
      targetContext.length)
    (relationMap : RelationRenaming sourceRels targetRels)
    (pointwise : ∀ occurrence, occurrence ∈ sourceOccurrences →
      ∀ (sourceItem : Item  sourceContext.length sourceRels)
        (targetItem : Item  targetContext.length targetRels),
      Concrete.Elaboration.compileOccurrenceWith?  source sourceRecurse
          sourceContext sourceBinders occurrence = some sourceItem →
      Concrete.Elaboration.compileOccurrenceWith?  target targetRecurse
          targetContext targetBinders (mapOccurrence occurrence) =
            some targetItem →
      Concrete.Elaboration.ItemSimulation model  direction relation
        (sourceItem.renameRelations relationMap) targetItem)
    (sourceItems : ItemSeq  sourceContext.length sourceRels)
    (targetItems : ItemSeq  targetContext.length targetRels)
    (sourceCompiled : Concrete.Elaboration.compileOccurrencesWith?
      source sourceRecurse sourceContext sourceBinders sourceOccurrences =
        some sourceItems)
    (targetCompiled : Concrete.Elaboration.compileOccurrencesWith?
      target targetRecurse targetContext targetBinders targetOccurrences =
        some targetItems) :
    Concrete.Elaboration.ItemSeqSimulation model  direction relation
      (sourceItems.renameRelations relationMap) targetItems := by
  have sourceLength := Concrete.Elaboration.compileOccurrencesWith?_length
    sourceRecurse sourceContext sourceBinders sourceCompiled
  have targetLength := Concrete.Elaboration.compileOccurrencesWith?_length
    targetRecurse targetContext targetBinders targetCompiled
  intro sourceEnv targetEnv relEnv environments
  cases direction with
  | forward =>
      intro sourceDenotes
      apply (denoteItemSeq_iff_get model  targetEnv relEnv targetItems).2
      intro targetItemIndex
      let targetOccurrenceIndex := Fin.cast targetLength targetItemIndex
      let sourceOccurrenceIndex := positions.symm targetOccurrenceIndex
      let sourceItemIndex := Fin.cast sourceLength.symm sourceOccurrenceIndex
      let sourcePreparedIndex := Fin.cast
        (ItemSeq.renameRelations_length sourceItems relationMap).symm
        sourceItemIndex
      have sourceAt := Concrete.Elaboration.compileOccurrencesWith?_get
        sourceRecurse sourceContext sourceBinders sourceCompiled
        sourceOccurrenceIndex
      have targetAt := Concrete.Elaboration.compileOccurrencesWith?_get
        targetRecurse targetContext targetBinders targetCompiled
        targetOccurrenceIndex
      have positionEq : positions sourceOccurrenceIndex =
          targetOccurrenceIndex := positions.right_inv targetOccurrenceIndex
      rw [← positionEq, positionSpec sourceOccurrenceIndex] at targetAt
      have sourceItemIndexEq :
          Fin.cast sourceLength.symm sourceOccurrenceIndex =
            sourceItemIndex := by
        apply Fin.ext
        rfl
      have targetItemIndexEq :
          Fin.cast targetLength.symm (positions sourceOccurrenceIndex) =
            targetItemIndex := by
        apply Fin.ext
        change (positions sourceOccurrenceIndex).val = targetItemIndex.val
        calc
          _ = targetOccurrenceIndex.val := congrArg Fin.val positionEq
          _ = targetItemIndex.val := rfl
      rw [sourceItemIndexEq] at sourceAt
      rw [targetItemIndexEq] at targetAt
      let occurrence := sourceOccurrences.get sourceOccurrenceIndex
      have occurrenceMember : occurrence ∈ sourceOccurrences :=
        List.get_mem sourceOccurrences sourceOccurrenceIndex
      have itemSimulation := pointwise occurrence occurrenceMember
        (sourceItems.get sourceItemIndex) (targetItems.get targetItemIndex)
        sourceAt targetAt
      have sourceItemDenotes :=
        (denoteItemSeq_iff_get model  sourceEnv relEnv
          (sourceItems.renameRelations relationMap)).1 sourceDenotes
          sourcePreparedIndex
      have sourcePreparedGet :
          (sourceItems.renameRelations relationMap).get sourcePreparedIndex =
            (sourceItems.get sourceItemIndex).renameRelations relationMap := by
        dsimp only [sourcePreparedIndex]
        simpa only [ItemSeq.get_renameRelations]
      rw [sourcePreparedGet] at sourceItemDenotes
      exact itemSimulation sourceEnv targetEnv relEnv environments
        sourceItemDenotes
  | backward =>
      intro targetDenotes
      apply (denoteItemSeq_iff_get model  sourceEnv relEnv
        (sourceItems.renameRelations relationMap)).2
      intro sourcePreparedIndex
      let sourceItemIndex := Fin.cast
        (ItemSeq.renameRelations_length sourceItems relationMap)
        sourcePreparedIndex
      let sourceOccurrenceIndex := Fin.cast sourceLength sourceItemIndex
      let targetOccurrenceIndex := positions sourceOccurrenceIndex
      let targetItemIndex := Fin.cast targetLength.symm targetOccurrenceIndex
      have sourceAt := Concrete.Elaboration.compileOccurrencesWith?_get
        sourceRecurse sourceContext sourceBinders sourceCompiled
        sourceOccurrenceIndex
      have targetAt := Concrete.Elaboration.compileOccurrencesWith?_get
        targetRecurse targetContext targetBinders targetCompiled
        targetOccurrenceIndex
      rw [positionSpec sourceOccurrenceIndex] at targetAt
      let occurrence := sourceOccurrences.get sourceOccurrenceIndex
      have occurrenceMember : occurrence ∈ sourceOccurrences :=
        List.get_mem sourceOccurrences sourceOccurrenceIndex
      have itemSimulation := pointwise occurrence occurrenceMember
        (sourceItems.get sourceItemIndex) (targetItems.get targetItemIndex)
        sourceAt targetAt
      have targetItemDenotes :=
        (denoteItemSeq_iff_get model  targetEnv relEnv targetItems).1
          targetDenotes targetItemIndex
      have sourcePreparedIndexEq :
          Fin.cast (ItemSeq.renameRelations_length sourceItems relationMap).symm
            sourceItemIndex = sourcePreparedIndex := by
        apply Fin.ext
        rfl
      rw [← sourcePreparedIndexEq]
      simpa only [ItemSeq.get_renameRelations] using
        itemSimulation sourceEnv targetEnv relEnv environments targetItemDenotes

end InstantiationSemantic

end VisualProof.Rule
