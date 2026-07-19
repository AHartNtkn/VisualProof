import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvanceFrameNodeSemantic

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- A proof-relevant equivalence of compiler occurrence positions lifts
pointwise item simulation to the complete ordered conjunction.  The
logical conjunction is insensitive to the dense enumeration order, while the
compiler receipts and `get` equations remain exact. -/
theorem compileOccurrences_simulation_of_equiv
    {signature : List Nat}
    {source target : ConcreteDiagram}
    (sourceRecurse : ∀ {rels : RelCtx},
      (region : Fin source.regionCount) →
      (context : ConcreteElaboration.WireContext source) →
      ConcreteElaboration.BinderContext source rels →
      Option (Region signature context.length rels))
    (targetRecurse : ∀ {rels : RelCtx},
      (region : Fin target.regionCount) →
      (context : ConcreteElaboration.WireContext target) →
      ConcreteElaboration.BinderContext target rels →
      Option (Region signature context.length rels))
    (sourceContext : ConcreteElaboration.WireContext source)
    (targetContext : ConcreteElaboration.WireContext target)
    (sourceBinders : ConcreteElaboration.BinderContext source sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext target targetRels)
    (sourceOccurrences : List (ConcreteElaboration.LocalOccurrence
      source.regionCount source.nodeCount))
    (targetOccurrences : List (ConcreteElaboration.LocalOccurrence
      target.regionCount target.nodeCount))
    (positions : FiniteEquiv (Fin sourceOccurrences.length)
      (Fin targetOccurrences.length))
    (mapOccurrence : ConcreteElaboration.LocalOccurrence source.regionCount
      source.nodeCount → ConcreteElaboration.LocalOccurrence target.regionCount
        target.nodeCount)
    (positionSpec : ∀ index,
      targetOccurrences.get (positions index) =
        mapOccurrence (sourceOccurrences.get index))
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (relation : ConcreteElaboration.ContextIndexRelation sourceContext.length
      targetContext.length)
    (relationMap : RelationRenaming sourceRels targetRels)
    (pointwise : ∀ occurrence, occurrence ∈ sourceOccurrences →
      ∀ (sourceItem : Item signature sourceContext.length sourceRels)
        (targetItem : Item signature targetContext.length targetRels),
      ConcreteElaboration.compileOccurrenceWith? signature source sourceRecurse
          sourceContext sourceBinders occurrence = some sourceItem →
      ConcreteElaboration.compileOccurrenceWith? signature target targetRecurse
          targetContext targetBinders (mapOccurrence occurrence) =
            some targetItem →
      ConcreteElaboration.ItemSimulation model named direction relation
        (sourceItem.renameRelations relationMap) targetItem)
    (sourceItems : ItemSeq signature sourceContext.length sourceRels)
    (targetItems : ItemSeq signature targetContext.length targetRels)
    (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      source sourceRecurse sourceContext sourceBinders sourceOccurrences =
        some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      target targetRecurse targetContext targetBinders targetOccurrences =
        some targetItems) :
    ConcreteElaboration.ItemSeqSimulation model named direction relation
      (sourceItems.renameRelations relationMap) targetItems := by
  have sourceLength := ConcreteElaboration.compileOccurrencesWith?_length
    sourceRecurse sourceContext sourceBinders sourceCompiled
  have targetLength := ConcreteElaboration.compileOccurrencesWith?_length
    targetRecurse targetContext targetBinders targetCompiled
  intro sourceEnv targetEnv relEnv environments
  cases direction with
  | forward =>
      intro sourceDenotes
      apply (denoteItemSeq_iff_get model named targetEnv relEnv targetItems).2
      intro targetItemIndex
      let targetOccurrenceIndex := Fin.cast targetLength targetItemIndex
      let sourceOccurrenceIndex := positions.symm targetOccurrenceIndex
      let sourceItemIndex := Fin.cast sourceLength.symm sourceOccurrenceIndex
      let sourcePreparedIndex := Fin.cast
        (ItemSeq.renameRelations_length sourceItems relationMap).symm
        sourceItemIndex
      have sourceAt := ConcreteElaboration.compileOccurrencesWith?_get
        sourceRecurse sourceContext sourceBinders sourceCompiled
        sourceOccurrenceIndex
      have targetAt := ConcreteElaboration.compileOccurrencesWith?_get
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
        (denoteItemSeq_iff_get model named sourceEnv relEnv
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
      apply (denoteItemSeq_iff_get model named sourceEnv relEnv
        (sourceItems.renameRelations relationMap)).2
      intro sourcePreparedIndex
      let sourceItemIndex := Fin.cast
        (ItemSeq.renameRelations_length sourceItems relationMap)
        sourcePreparedIndex
      let sourceOccurrenceIndex := Fin.cast sourceLength sourceItemIndex
      let targetOccurrenceIndex := positions sourceOccurrenceIndex
      let targetItemIndex := Fin.cast targetLength.symm targetOccurrenceIndex
      have sourceAt := ConcreteElaboration.compileOccurrencesWith?_get
        sourceRecurse sourceContext sourceBinders sourceCompiled
        sourceOccurrenceIndex
      have targetAt := ConcreteElaboration.compileOccurrencesWith?_get
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
        (denoteItemSeq_iff_get model named targetEnv relEnv targetItems).1
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
