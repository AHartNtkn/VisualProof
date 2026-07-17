import VisualProof.Rule.Soundness.Modal.VacuousEliminationCompiler
import VisualProof.Rule.Soundness.Modal.EliminationFocusedItems

namespace VisualProof.Rule.VacuousElimTrace

open VisualProof
open VisualProof.Theory
open VisualProof.Diagram
open VisualProof.Rule.DoubleCutElimTrace

theorem focusedTargetEnvironment_outer
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input)
    (context : PromotedContextWitness trace sourceContext targetContext)
    (sourceExact :
      (sourceContext.extend (trace.targetIndex wellFormed)).Exact
        (trace.targetIndex wellFormed))
    (sourceOuter : Fin sourceContext.length → D)
    (targetOuter : Fin targetContext.length → D)
    (outerAgreement :
      context.indexRelation.EnvironmentsAgree sourceOuter targetOuter)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires
      trace.sourceDiagram (trace.targetIndex wellFormed)).length → D)
    (targetIndex : Fin targetContext.length) :
    let focused := context.extendFocused wellFormed
    focused.targetEnvironment
        (ConcreteElaboration.extendedEnvironment sourceContext
          (trace.targetIndex wellFormed) sourceOuter sourceLocal)
        (extendedOuterIndex targetContext trace.parent targetIndex) =
      targetOuter targetIndex := by
  dsimp only
  let focused := context.extendFocused wellFormed
  let sourceIndex := context.sourceIndex targetIndex
  let sourceExtendedIndex := extendedOuterIndex sourceContext
    (trace.targetIndex wellFormed) sourceIndex
  let targetExtendedIndex := extendedOuterIndex targetContext trace.parent
    targetIndex
  have corresponding :
      (sourceContext.extend (trace.targetIndex wellFormed)).get
          sourceExtendedIndex =
        (targetContext.extend trace.parent).get targetExtendedIndex := by
    calc
      _ = sourceContext.get sourceIndex :=
        extendedOuterIndex_get sourceContext
          (trace.targetIndex wellFormed) sourceIndex
      _ = targetContext.get targetIndex := context.sourceIndex_get targetIndex
      _ = _ :=
        (extendedOuterIndex_get targetContext trace.parent targetIndex).symm
  have sourceExtendedIndexEq :
      sourceExtendedIndex = focused.sourceIndex targetExtendedIndex :=
    ConcreteElaboration.WireContext.lookup?_unique sourceExact.nodup
      (focused.sourceIndex_lookup targetExtendedIndex) corresponding
  unfold PromotedContextWitness.targetEnvironment
  rw [← sourceExtendedIndexEq, extendedEnvironment_outer]
  exact outerAgreement sourceIndex targetIndex (context.sourceIndex_get _)

theorem PromotedContextWitness.targetEnvironment_eq_of_get
    (first : PromotedContextWitness trace sourceContext firstTargetContext)
    (second : PromotedContextWitness trace sourceContext secondTargetContext)
    (sourceNodup : sourceContext.Nodup)
    (sourceEnvironment : Fin sourceContext.length → D)
    (firstIndex : Fin firstTargetContext.length)
    (secondIndex : Fin secondTargetContext.length)
    (sameWire : firstTargetContext.get firstIndex =
      secondTargetContext.get secondIndex) :
    first.targetEnvironment sourceEnvironment firstIndex =
      second.targetEnvironment sourceEnvironment secondIndex := by
  have secondGet := second.sourceIndex_get secondIndex
  have indicesEqual :
      first.sourceIndex firstIndex = second.sourceIndex secondIndex := by
    exact (ConcreteElaboration.WireContext.lookup?_unique sourceNodup
      (first.sourceIndex_lookup firstIndex)
      (secondGet.trans sameWire.symm)).symm
  unfold PromotedContextWitness.targetEnvironment
  rw [indicesEqual]

theorem selectedTargetEnvironment_outer
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input)
    (context : PromotedContextWitness trace sourceContext targetContext)
    (sourceExact :
      (sourceContext.extend (trace.targetIndex wellFormed)).Exact
        (trace.targetIndex wellFormed))
    (sourceEnvironment :
      Fin (sourceContext.extend (trace.targetIndex wellFormed)).length → D)
    (index : Fin (targetContext.extend trace.parent).length) :
    let focused := context.extendFocused wellFormed
    let selected := context.extendSelected wellFormed
    selected.targetEnvironment sourceEnvironment
        (extendedOuterIndex (targetContext.extend trace.parent) bubble index) =
      focused.targetEnvironment sourceEnvironment index := by
  dsimp only
  let focused := context.extendFocused wellFormed
  let selected := context.extendSelected wellFormed
  have sameWire :
      ((targetContext.extend trace.parent).extend bubble).get
          (extendedOuterIndex (targetContext.extend trace.parent) bubble index) =
        (targetContext.extend trace.parent).get index :=
    extendedOuterIndex_get (targetContext.extend trace.parent) bubble index
  exact selected.targetEnvironment_eq_of_get focused sourceExact.nodup
    sourceEnvironment _ _ sameWire

theorem PromotedContextWitness.source_subset_target_at_focus
    {input : ConcreteDiagram} {bubble : Fin input.regionCount}
    {raw : ConcreteDiagram}
    {trace : VacuousElimTrace input bubble raw}
    {sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram}
    {targetContext : ConcreteElaboration.WireContext input}
    (context : PromotedContextWitness trace sourceContext targetContext)
    (wellFormed : input.WellFormed signature)
    (sourceExact :
      (sourceContext.extend (trace.targetIndex wellFormed)).Exact
        (trace.targetIndex wellFormed)) :
    ∀ wire, wire ∈ sourceContext → wire ∈ targetContext := by
  intro wire sourceMember
  rcases context.source_subset_target_or_bubble wire sourceMember with
    targetMember | bubbleMember
  · exact targetMember
  · have focusMember :=
      trace.bubbleWire_mem_focusExact wellFormed wire bubbleMember
    have extendedNodup :
        (sourceContext ++ ConcreteElaboration.exactScopeWires
          trace.sourceDiagram (trace.targetIndex wellFormed)).Nodup := by
      simpa [ConcreteElaboration.WireContext.extend] using sourceExact.nodup
    have parts := List.nodup_append.mp extendedNodup
    exact False.elim
      (parts.2.2 wire sourceMember wire focusMember rfl)

theorem selectedSourceEnvironment_outer
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input)
    (context : PromotedContextWitness trace sourceContext targetContext)
    (sourceExact :
      (sourceContext.extend (trace.targetIndex wellFormed)).Exact
        (trace.targetIndex wellFormed))
    (targetSelectedNodup :
      ((targetContext.extend trace.parent).extend bubble).Nodup)
    (sourceOuter : Fin sourceContext.length → D)
    (targetOuter : Fin targetContext.length → D)
    (outerAgreement :
      context.indexRelation.EnvironmentsAgree sourceOuter targetOuter)
    (targetLocal : Fin (ConcreteElaboration.exactScopeWires input
      trace.parent).length → D)
    (bubbleLocal : Fin (ConcreteElaboration.exactScopeWires input
      bubble).length → D)
    (sourceIndex : Fin sourceContext.length) :
    let targetFocusEnvironment :=
      ConcreteElaboration.extendedEnvironment targetContext trace.parent
        targetOuter targetLocal
    let targetSelectedEnvironment :=
      ConcreteElaboration.extendedEnvironment
        (targetContext.extend trace.parent) bubble
        targetFocusEnvironment bubbleLocal
    let selected := context.extendSelected wellFormed
    selected.sourceEnvironment
        (context.extendSelected_source_subset_target wellFormed)
        targetSelectedEnvironment
        (extendedOuterIndex sourceContext (trace.targetIndex wellFormed)
          sourceIndex) = sourceOuter sourceIndex := by
  dsimp only
  let selected := context.extendSelected wellFormed
  let sourceSubset := context.source_subset_target_at_focus wellFormed
    sourceExact
  let targetBaseIndex := context.targetIndex sourceSubset sourceIndex
  let targetFocusIndex := extendedOuterIndex targetContext trace.parent
    targetBaseIndex
  let targetSelectedIndex := extendedOuterIndex
    (targetContext.extend trace.parent) bubble targetFocusIndex
  let sourceExtendedIndex := extendedOuterIndex sourceContext
    (trace.targetIndex wellFormed) sourceIndex
  have corresponding :
      ((targetContext.extend trace.parent).extend bubble).get
          targetSelectedIndex =
        (sourceContext.extend (trace.targetIndex wellFormed)).get
          sourceExtendedIndex := by
    calc
      _ = (targetContext.extend trace.parent).get targetFocusIndex :=
        extendedOuterIndex_get (targetContext.extend trace.parent) bubble
          targetFocusIndex
      _ = targetContext.get targetBaseIndex :=
        extendedOuterIndex_get targetContext trace.parent targetBaseIndex
      _ = sourceContext.get sourceIndex :=
        context.targetIndex_get sourceSubset sourceIndex
      _ = _ := (extendedOuterIndex_get sourceContext
        (trace.targetIndex wellFormed) sourceIndex).symm
  have targetSelectedIndexEq :
      targetSelectedIndex = selected.targetIndex
        (context.extendSelected_source_subset_target wellFormed)
        sourceExtendedIndex :=
    ConcreteElaboration.WireContext.lookup?_unique targetSelectedNodup
      (selected.targetIndex_lookup
        (context.extendSelected_source_subset_target wellFormed)
        sourceExtendedIndex)
      corresponding
  unfold PromotedContextWitness.sourceEnvironment
  rw [← targetSelectedIndexEq]
  simp [targetSelectedIndex, targetFocusIndex]
  exact (outerAgreement sourceIndex targetBaseIndex
    (context.targetIndex_get sourceSubset sourceIndex).symm).symm

theorem sourceFocused_partition_denote_iff
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram)
    (keptItems selectedItems : ItemSeq signature
      (sourceContext.extend (trace.targetIndex wellFormed)).length rels)
    (sourceEnvironment : Fin sourceContext.length → model.Carrier)
    (relations : RelEnv model.Carrier rels) :
    denoteRegion model named sourceEnvironment relations
        (ConcreteElaboration.finishRegion trace.sourceDiagram sourceContext
          (trace.targetIndex wellFormed) (keptItems.append selectedItems)) ↔
      ∃ sourceLocal : Fin (ConcreteElaboration.exactScopeWires
          trace.sourceDiagram (trace.targetIndex wellFormed)).length →
            model.Carrier,
        denoteItemSeq model named
            (ConcreteElaboration.extendedEnvironment sourceContext
              (trace.targetIndex wellFormed) sourceEnvironment sourceLocal)
            relations keptItems ∧
          denoteItemSeq model named
            (ConcreteElaboration.extendedEnvironment sourceContext
              (trace.targetIndex wellFormed) sourceEnvironment sourceLocal)
            relations selectedItems := by
  rw [finishRegion_denote_iff]
  apply exists_congr
  intro sourceLocal
  exact denoteItemSeq_append model named _ relations keptItems selectedItems

theorem targetFocused_bubble_denote_iff
    (trace : VacuousElimTrace input bubble raw)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (targetContext : ConcreteElaboration.WireContext input)
    (keptItems : ItemSeq signature
      (targetContext.extend trace.parent).length rels)
    (selectedItems : ItemSeq signature
      ((targetContext.extend trace.parent).extend bubble).length
      (trace.arity :: rels))
    (targetEnvironment : Fin targetContext.length → model.Carrier)
    (relations : RelEnv model.Carrier rels) :
    denoteRegion model named targetEnvironment relations
        (ConcreteElaboration.finishRegion input targetContext trace.parent
          (keptItems.append (.cons
            (.bubble trace.arity
              (ConcreteElaboration.finishRegion input
                (targetContext.extend trace.parent) bubble selectedItems))
            .nil))) ↔
      ∃ targetLocal : Fin (ConcreteElaboration.exactScopeWires input
          trace.parent).length → model.Carrier,
        denoteItemSeq model named
            (ConcreteElaboration.extendedEnvironment targetContext trace.parent
              targetEnvironment targetLocal)
            relations keptItems ∧
          ∃ fresh : Relation model.Carrier trace.arity,
            ∃ bubbleLocal : Fin (ConcreteElaboration.exactScopeWires input
                bubble).length → model.Carrier,
              denoteItemSeq (relCtx := trace.arity :: rels) model named
                (ConcreteElaboration.extendedEnvironment
                  (targetContext.extend trace.parent) bubble
                  (ConcreteElaboration.extendedEnvironment targetContext
                    trace.parent targetEnvironment targetLocal)
                  bubbleLocal)
                ((fresh, relations) :
                  RelEnv model.Carrier (trace.arity :: rels)) selectedItems := by
  rw [finishRegion_denote_iff]
  apply exists_congr
  intro targetLocal
  simp only [denoteItemSeq_append, denoteItemSeq_cons, denoteItemSeq_nil,
    and_true, bubble_denotes_exists]
  apply and_congr Iff.rfl
  apply exists_congr
  intro fresh
  exact finishRegion_denote_iff input
    (targetContext.extend trace.parent) bubble selectedItems model named
    (ConcreteElaboration.extendedEnvironment targetContext trace.parent
      targetEnvironment targetLocal)
    (fresh, relations)

theorem targetSelected_exact
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (targetContext : ConcreteElaboration.WireContext input)
    (targetExact :
      (targetContext.extend trace.parent).Exact trace.parent) :
    ((targetContext.extend trace.parent).extend bubble).Exact bubble := by
  have parentEq : (input.regions bubble).parent? = some trace.parent := by
    simp [trace.bubble_eq, CRegion.parent?]
  exact targetExact.extend_child wellFormed parentEq

end VisualProof.Rule.VacuousElimTrace
