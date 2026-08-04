import VisualProof.Rule.Soundness.Modal.EliminationCompiler

namespace VisualProof.Rule.DoubleCutElimTrace

open VisualProof
open VisualProof.Theory
open VisualProof.Diagram

theorem finishRegion_denote_iff
    (diagram : ConcreteDiagram)
    (context : ConcreteElaboration.WireContext diagram)
    (region : Fin diagram.regionCount)
    (items : ItemSeq signature (context.extend region).length rels)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (environment : Fin context.length → model.Carrier)
    (relations : RelEnv model.Carrier rels) :
    denoteRegion model named environment relations
        (ConcreteElaboration.finishRegion diagram context region items) ↔
      ∃ localEnvironment :
          Fin (ConcreteElaboration.exactScopeWires diagram region).length →
            model.Carrier,
        denoteItemSeq model named
          (ConcreteElaboration.extendedEnvironment context region environment
            localEnvironment)
          relations items := by
  unfold ConcreteElaboration.finishRegion
  simp only [denoteRegion_mk, ItemSeq.castWiresEq_eq_renameWires]
  constructor
  · rintro ⟨localEnvironment, denotation⟩
    refine ⟨localEnvironment, ?_⟩
    exact (denoteItemSeq_renameWires model named
      (Fin.cast (ConcreteElaboration.WireContext.length_extend context region))
      (extendWireEnv environment localEnvironment) relations items).mp
        denotation
  · rintro ⟨localEnvironment, denotation⟩
    refine ⟨localEnvironment, ?_⟩
    exact (denoteItemSeq_renameWires model named
      (Fin.cast (ConcreteElaboration.WireContext.length_extend context region))
      (extendWireEnv environment localEnvironment) relations items).mpr
        denotation

def emptyOuterEnvironment
    (trace : DoubleCutElimTrace input outer raw) (D : Type) :
    Fin (ConcreteElaboration.exactScopeWires input outer).length → D :=
  fun index => Fin.elim0
    (Fin.cast (congrArg List.length trace.outer_exactScopeWires) index)

theorem extendOuter_eq
    (trace : DoubleCutElimTrace input outer raw)
    (context : ConcreteElaboration.WireContext input) :
    context.extend outer = context := by
  unfold ConcreteElaboration.WireContext.extend
  rw [trace.outer_exactScopeWires]
  exact List.append_nil context

theorem extendedEnvironment_outer_empty
    (trace : DoubleCutElimTrace input outer raw)
    (context : ConcreteElaboration.WireContext input)
    (environment : Fin context.length → D) :
    ConcreteElaboration.extendedEnvironment context outer environment
        (trace.emptyOuterEnvironment D) =
      fun index => environment
        (Fin.cast (congrArg List.length (trace.extendOuter_eq context))
          index) := by
  funext index
  unfold ConcreteElaboration.extendedEnvironment emptyOuterEnvironment
  simp only [Function.comp_apply]
  let sourceLocal :
      Fin (ConcreteElaboration.exactScopeWires input outer).length → D :=
    trace.emptyOuterEnvironment D
  let countEq :
      (ConcreteElaboration.exactScopeWires input outer).length = 0 :=
    congrArg List.length trace.outer_exactScopeWires
  have transported := VisualProof.Rule.ModalSoundness.extendWireEnv_transport
    (countEq := countEq.symm)
    (sourceLocal := sourceLocal)
    (targetLocal := (Fin.elim0 : Fin 0 → D))
    (localValues := by
      intro impossible
      exact Fin.elim0 impossible)
    (sourceIndex := Fin.cast
      (ConcreteElaboration.WireContext.length_extend context outer) index)
    (targetIndex := Fin.cast
      ((congrArg List.length (trace.extendOuter_eq context)).trans
        (Nat.add_zero context.length).symm)
      index)
    (indexValue := rfl)
    environment
  simpa [sourceLocal, emptyOuterEnvironment, extendWireEnv_zero] using
    transported

def extendedOuterIndex
    (context : ConcreteElaboration.WireContext diagram)
    (region : Fin diagram.regionCount) (index : Fin context.length) :
    Fin (context.extend region).length :=
  Fin.cast (ConcreteElaboration.WireContext.length_extend context region).symm
    (Fin.castAdd
      (ConcreteElaboration.exactScopeWires diagram region).length index)

def extendedLocalIndex
    (context : ConcreteElaboration.WireContext diagram)
    (region : Fin diagram.regionCount)
    (index : Fin (ConcreteElaboration.exactScopeWires diagram region).length) :
    Fin (context.extend region).length :=
  Fin.cast (ConcreteElaboration.WireContext.length_extend context region).symm
    (Fin.natAdd context.length index)

def localEnvironmentPart
    (context : ConcreteElaboration.WireContext diagram)
    (region : Fin diagram.regionCount)
    (environment : Fin (context.extend region).length → D) :
    Fin (ConcreteElaboration.exactScopeWires diagram region).length → D :=
  fun index => environment (extendedLocalIndex context region index)

theorem extendedEnvironment_of_parts
    (context : ConcreteElaboration.WireContext diagram)
    (region : Fin diagram.regionCount)
    (outerEnvironment : Fin context.length → D)
    (environment : Fin (context.extend region).length → D)
    (outerValues : ∀ index,
      environment (extendedOuterIndex context region index) =
        outerEnvironment index) :
    ConcreteElaboration.extendedEnvironment context region outerEnvironment
        (localEnvironmentPart context region environment) =
      environment := by
  funext index
  let splitIndex := Fin.cast
    (ConcreteElaboration.WireContext.length_extend context region) index
  change extendWireEnv outerEnvironment
      (localEnvironmentPart context region environment) splitIndex =
    environment (Fin.cast
      (ConcreteElaboration.WireContext.length_extend context region).symm
      splitIndex)
  refine Fin.addCases ?_ ?_ splitIndex
  · intro outerIndex
    rw [extendWireEnv, Fin.addCases_left]
    exact (outerValues outerIndex).symm
  · intro localIndex
    rw [extendWireEnv, Fin.addCases_right]
    rfl

@[simp] theorem extendedEnvironment_outer
    (context : ConcreteElaboration.WireContext diagram)
    (region : Fin diagram.regionCount)
    (outerEnvironment : Fin context.length → D)
    (localEnvironment :
      Fin (ConcreteElaboration.exactScopeWires diagram region).length → D)
    (index : Fin context.length) :
    ConcreteElaboration.extendedEnvironment context region outerEnvironment
        localEnvironment (extendedOuterIndex context region index) =
      outerEnvironment index := by
  simp [ConcreteElaboration.extendedEnvironment, extendedOuterIndex,
    extendWireEnv, Fin.addCases_left]

@[simp] theorem extendedEnvironment_local
    (context : ConcreteElaboration.WireContext diagram)
    (region : Fin diagram.regionCount)
    (outerEnvironment : Fin context.length → D)
    (localEnvironment :
      Fin (ConcreteElaboration.exactScopeWires diagram region).length → D)
    (index :
      Fin (ConcreteElaboration.exactScopeWires diagram region).length) :
    ConcreteElaboration.extendedEnvironment context region outerEnvironment
        localEnvironment (extendedLocalIndex context region index) =
      localEnvironment index := by
  simp [ConcreteElaboration.extendedEnvironment, extendedLocalIndex,
    extendWireEnv, Fin.addCases_right]

@[simp] theorem extendedOuterIndex_get
    (context : ConcreteElaboration.WireContext diagram)
    (region : Fin diagram.regionCount) (index : Fin context.length) :
    (context.extend region).get (extendedOuterIndex context region index) =
      context.get index := by
  simpa [extendedOuterIndex,
    ConcreteElaboration.WireContext.outerIndex] using
      ConcreteElaboration.WireContext.extend_outer context region index

@[simp] theorem extendedLocalIndex_get
    (context : ConcreteElaboration.WireContext diagram)
    (region : Fin diagram.regionCount)
    (index :
      Fin (ConcreteElaboration.exactScopeWires diagram region).length) :
    (context.extend region).get (extendedLocalIndex context region index) =
      (ConcreteElaboration.exactScopeWires diagram region).get index := by
  simpa [extendedLocalIndex] using
    ConcreteElaboration.WireContext.extend_local context region index

theorem focusedTargetEnvironment_outer
    (trace : DoubleCutElimTrace input outer raw)
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
    (sourceLocal :
      Fin (ConcreteElaboration.exactScopeWires trace.sourceDiagram
        (trace.targetIndex wellFormed)).length → D)
    (targetIndex : Fin targetContext.length) :
    let focused := context.extendFocused wellFormed
    focused.targetEnvironment
        (ConcreteElaboration.extendedEnvironment sourceContext
          (trace.targetIndex wellFormed) sourceOuter sourceLocal)
        (extendedOuterIndex targetContext trace.target targetIndex) =
      targetOuter targetIndex := by
  dsimp only
  let focused := context.extendFocused wellFormed
  let sourceIndex := context.sourceIndex targetIndex
  let sourceExtendedIndex := extendedOuterIndex sourceContext
    (trace.targetIndex wellFormed) sourceIndex
  let targetExtendedIndex := extendedOuterIndex targetContext trace.target
    targetIndex
  have corresponding :
      (sourceContext.extend (trace.targetIndex wellFormed)).get
          sourceExtendedIndex =
        (targetContext.extend trace.target).get targetExtendedIndex := by
    calc
      _ = sourceContext.get sourceIndex :=
        extendedOuterIndex_get sourceContext
          (trace.targetIndex wellFormed) sourceIndex
      _ = targetContext.get targetIndex := context.sourceIndex_get targetIndex
      _ = _ :=
        (extendedOuterIndex_get targetContext trace.target targetIndex).symm
  have sourceExtendedIndexEq :
      sourceExtendedIndex = focused.sourceIndex targetExtendedIndex :=
    ConcreteElaboration.WireContext.lookup?_unique sourceExact.nodup
      (focused.sourceIndex_lookup targetExtendedIndex) corresponding
  unfold PromotedContextWitness.targetEnvironment
  rw [← sourceExtendedIndexEq]
  rw [extendedEnvironment_outer]
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
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input)
    (context : PromotedContextWitness trace sourceContext targetContext)
    (sourceExact :
      (sourceContext.extend (trace.targetIndex wellFormed)).Exact
        (trace.targetIndex wellFormed))
    (sourceEnvironment :
      Fin (sourceContext.extend (trace.targetIndex wellFormed)).length → D)
    (index : Fin
      ((targetContext.extend trace.target).extend outer).length) :
    let focused := context.extendFocused wellFormed
    let selected := context.extendSelected wellFormed
    selected.targetEnvironment sourceEnvironment
        (extendedOuterIndex
          ((targetContext.extend trace.target).extend outer) trace.inner
          index) =
      ConcreteElaboration.extendedEnvironment
        (targetContext.extend trace.target) outer
        (focused.targetEnvironment sourceEnvironment)
        (trace.emptyOuterEnvironment D) index := by
  dsimp only
  let focused := context.extendFocused wellFormed
  let selected := context.extendSelected wellFormed
  let outerContext := (targetContext.extend trace.target).extend outer
  let focusContext := targetContext.extend trace.target
  let contextEq : outerContext = focusContext :=
    trace.extendOuter_eq focusContext
  let focusIndex : Fin focusContext.length :=
    Fin.cast (congrArg List.length contextEq) index
  have sameWire :
      (outerContext.extend trace.inner).get
          (extendedOuterIndex outerContext trace.inner index) =
        focusContext.get focusIndex := by
    rw [extendedOuterIndex_get]
    simpa [outerContext, focusContext, focusIndex, contextEq]
  calc
    _ = focused.targetEnvironment sourceEnvironment focusIndex :=
      selected.targetEnvironment_eq_of_get focused sourceExact.nodup
        sourceEnvironment _ _ sameWire
    _ = _ := by
      rw [trace.extendedEnvironment_outer_empty focusContext
        (focused.targetEnvironment sourceEnvironment)]

theorem PromotedContextWitness.source_subset_target_at_focus
    {input : ConcreteDiagram} {outer : Fin input.regionCount}
    {raw : ConcreteDiagram}
    {trace : DoubleCutElimTrace input outer raw}
    {sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram}
    {targetContext : ConcreteElaboration.WireContext input}
    (context : PromotedContextWitness trace sourceContext targetContext)
    (wellFormed : input.WellFormed signature)
    (sourceExact :
      (sourceContext.extend (trace.targetIndex wellFormed)).Exact
        (trace.targetIndex wellFormed)) :
    ∀ wire, wire ∈ sourceContext → wire ∈ targetContext := by
  intro wire sourceMember
  rcases context.source_subset_target_or_inner wire sourceMember with
    targetMember | innerMember
  · exact targetMember
  · have focusMember :=
      trace.innerWire_mem_focusExact wellFormed wire innerMember
    have extendedNodup :
        (sourceContext ++
          ConcreteElaboration.exactScopeWires trace.sourceDiagram
            (trace.targetIndex wellFormed)).Nodup := by
      simpa [ConcreteElaboration.WireContext.extend] using sourceExact.nodup
    have parts := List.nodup_append.mp extendedNodup
    exact False.elim (parts.2.2 wire sourceMember wire focusMember rfl)

theorem selectedSourceEnvironment_outer
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input)
    (context : PromotedContextWitness trace sourceContext targetContext)
    (sourceExact :
      (sourceContext.extend (trace.targetIndex wellFormed)).Exact
        (trace.targetIndex wellFormed))
    (targetSelectedNodup :
      (((targetContext.extend trace.target).extend outer).extend
        trace.inner).Nodup)
    (sourceOuter : Fin sourceContext.length → D)
    (targetOuter : Fin targetContext.length → D)
    (outerAgreement :
      context.indexRelation.EnvironmentsAgree sourceOuter targetOuter)
    (targetLocal :
      Fin (ConcreteElaboration.exactScopeWires input trace.target).length → D)
    (innerLocal :
      Fin (ConcreteElaboration.exactScopeWires input trace.inner).length → D)
    (sourceIndex : Fin sourceContext.length) :
    let targetFocusEnvironment :=
      ConcreteElaboration.extendedEnvironment targetContext trace.target
        targetOuter targetLocal
    let targetOuterEnvironment :=
      ConcreteElaboration.extendedEnvironment
        (targetContext.extend trace.target) outer targetFocusEnvironment
        (trace.emptyOuterEnvironment D)
    let targetSelectedEnvironment :=
      ConcreteElaboration.extendedEnvironment
        ((targetContext.extend trace.target).extend outer) trace.inner
        targetOuterEnvironment innerLocal
    let selected := context.extendSelected wellFormed
    selected.sourceEnvironment
        (context.extendSelected_source_subset_target wellFormed)
        targetSelectedEnvironment
        (extendedOuterIndex sourceContext (trace.targetIndex wellFormed)
          sourceIndex) =
      sourceOuter sourceIndex := by
  dsimp only
  let selected := context.extendSelected wellFormed
  let sourceSubset := context.source_subset_target_at_focus wellFormed
    sourceExact
  let targetBaseIndex := context.targetIndex sourceSubset sourceIndex
  let targetFocusIndex := extendedOuterIndex targetContext trace.target
    targetBaseIndex
  let targetOuterIndex := extendedOuterIndex
    (targetContext.extend trace.target) outer targetFocusIndex
  let targetSelectedIndex := extendedOuterIndex
    ((targetContext.extend trace.target).extend outer) trace.inner
    targetOuterIndex
  let sourceExtendedIndex := extendedOuterIndex sourceContext
    (trace.targetIndex wellFormed) sourceIndex
  have corresponding :
      (((targetContext.extend trace.target).extend outer).extend
          trace.inner).get targetSelectedIndex =
        (sourceContext.extend (trace.targetIndex wellFormed)).get
          sourceExtendedIndex := by
    calc
      _ = ((targetContext.extend trace.target).extend outer).get
          targetOuterIndex :=
        extendedOuterIndex_get
          ((targetContext.extend trace.target).extend outer) trace.inner
          targetOuterIndex
      _ = (targetContext.extend trace.target).get targetFocusIndex :=
        extendedOuterIndex_get (targetContext.extend trace.target) outer
          targetFocusIndex
      _ = targetContext.get targetBaseIndex :=
        extendedOuterIndex_get targetContext trace.target targetBaseIndex
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
  simp [targetSelectedIndex, targetOuterIndex, targetFocusIndex]
  exact (outerAgreement sourceIndex targetBaseIndex
    (context.targetIndex_get sourceSubset sourceIndex).symm).symm


theorem targetFocused_doubleCut_denote_iff
    (trace : DoubleCutElimTrace input outer raw)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (targetContext : ConcreteElaboration.WireContext input)
    (keptItems : ItemSeq signature
      (targetContext.extend trace.target).length rels)
    (selectedItems : ItemSeq signature
      (((targetContext.extend trace.target).extend outer).extend
        trace.inner).length rels)
    (targetEnvironment : Fin targetContext.length → model.Carrier)
    (relations : RelEnv model.Carrier rels) :
    denoteRegion model named targetEnvironment relations
        (ConcreteElaboration.finishRegion input targetContext trace.target
          (keptItems.append
            (.cons
              (.cut
                (ConcreteElaboration.finishRegion input
                  (targetContext.extend trace.target) outer
                  (.cons
                    (.cut
                      (ConcreteElaboration.finishRegion input
                        ((targetContext.extend trace.target).extend outer)
                        trace.inner selectedItems))
                    .nil)))
              .nil))) ↔
      ∃ targetLocal :
          Fin (ConcreteElaboration.exactScopeWires input
            trace.target).length → model.Carrier,
        denoteItemSeq model named
            (ConcreteElaboration.extendedEnvironment targetContext
              trace.target targetEnvironment targetLocal)
            relations keptItems ∧
          ∃ innerLocal :
              Fin (ConcreteElaboration.exactScopeWires input
                trace.inner).length → model.Carrier,
            denoteItemSeq model named
              (ConcreteElaboration.extendedEnvironment
                ((targetContext.extend trace.target).extend outer)
                trace.inner
                (ConcreteElaboration.extendedEnvironment
                  (targetContext.extend trace.target) outer
                  (ConcreteElaboration.extendedEnvironment targetContext
                    trace.target targetEnvironment targetLocal)
                  (trace.emptyOuterEnvironment model.Carrier))
                innerLocal)
              relations selectedItems := by
  rw [finishRegion_denote_iff]
  apply exists_congr
  intro targetLocal
  simp only [denoteItemSeq_append, denoteItemSeq_cons, denoteItemSeq_nil,
    and_true, cut_denotes_negation]
  apply and_congr Iff.rfl
  rw [finishRegion_denote_iff]
  constructor
  · intro doubleNegation
    have innerRegion :
        denoteRegion model named
          (ConcreteElaboration.extendedEnvironment
            (targetContext.extend trace.target) outer
            (ConcreteElaboration.extendedEnvironment targetContext
              trace.target targetEnvironment targetLocal)
            (trace.emptyOuterEnvironment model.Carrier))
          relations
          (ConcreteElaboration.finishRegion input
            ((targetContext.extend trace.target).extend outer)
            trace.inner selectedItems) := by
      apply Classical.byContradiction
      intro notInner
      apply doubleNegation
      refine ⟨trace.emptyOuterEnvironment model.Carrier, ?_⟩
      simpa only [denoteItemSeq_cons, denoteItemSeq_nil, and_true,
        cut_denotes_negation] using notInner
    exact (finishRegion_denote_iff input
      ((targetContext.extend trace.target).extend outer) trace.inner
      selectedItems model named
      (ConcreteElaboration.extendedEnvironment
        (targetContext.extend trace.target) outer
        (ConcreteElaboration.extendedEnvironment targetContext trace.target
          targetEnvironment targetLocal)
        (trace.emptyOuterEnvironment model.Carrier))
      relations).mp innerRegion
  · intro innerItems
    have innerRegion := (finishRegion_denote_iff input
      ((targetContext.extend trace.target).extend outer) trace.inner
      selectedItems model named
      (ConcreteElaboration.extendedEnvironment
        (targetContext.extend trace.target) outer
        (ConcreteElaboration.extendedEnvironment targetContext trace.target
          targetEnvironment targetLocal)
        (trace.emptyOuterEnvironment model.Carrier))
      relations).mpr innerItems
    rintro ⟨outerLocal, outerDenotation⟩
    have outerLocalEq :
        outerLocal = trace.emptyOuterEnvironment model.Carrier := by
      funext index
      exact Fin.elim0
        (Fin.cast (congrArg List.length trace.outer_exactScopeWires) index)
    subst outerLocal
    have notInner :
        ¬ denoteRegion model named
          (ConcreteElaboration.extendedEnvironment
            (targetContext.extend trace.target) outer
            (ConcreteElaboration.extendedEnvironment targetContext
              trace.target targetEnvironment targetLocal)
            (trace.emptyOuterEnvironment model.Carrier))
          relations
          (ConcreteElaboration.finishRegion input
            ((targetContext.extend trace.target).extend outer)
            trace.inner selectedItems) := by
      simpa only [denoteItemSeq_cons, denoteItemSeq_nil, and_true,
        cut_denotes_negation] using outerDenotation
    exact notInner innerRegion

theorem sourceFocused_partition_denote_iff
    (trace : DoubleCutElimTrace input outer raw)
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
      ∃ sourceLocal :
          Fin (ConcreteElaboration.exactScopeWires trace.sourceDiagram
            (trace.targetIndex wellFormed)).length → model.Carrier,
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

theorem targetSelected_exact
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (targetContext : ConcreteElaboration.WireContext input)
    (targetExact : (targetContext.extend trace.target).Exact trace.target) :
    (((targetContext.extend trace.target).extend outer).extend
      trace.inner).Exact trace.inner := by
  have outerExact := targetExact.extend_child wellFormed trace.outer_parent
  exact outerExact.extend_child wellFormed trace.inner_parent

end VisualProof.Rule.DoubleCutElimTrace
