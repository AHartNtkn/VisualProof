import VisualProof.Rule.Soundness.Modal.EliminationRoot

namespace VisualProof.Rule.DoubleCutElimTrace

open VisualProof
open VisualProof.Theory
open VisualProof.Diagram

theorem rootTargetEnvironment_outer
    (trace : DoubleCutElimTrace input outer raw)
    (sourceAmbient sourceLocals :
      ConcreteElaboration.WireContext trace.sourceDiagram)
    (targetAmbient targetLocals : ConcreteElaboration.WireContext input)
    (context : PromotedContextWitness trace
      (sourceAmbient ++ sourceLocals) (targetAmbient ++ targetLocals))
    (sourceExact : (sourceAmbient ++ sourceLocals).Nodup)
    (ambientSubset : ∀ wire, wire ∈ targetAmbient → wire ∈ sourceAmbient)
    (sourceOuter : Fin sourceAmbient.length → D)
    (targetOuter : Fin targetAmbient.length → D)
    (outerAgreement :
      (trace.wireIdentityRelation sourceAmbient targetAmbient).EnvironmentsAgree
        sourceOuter targetOuter)
    (sourceLocal : Fin sourceLocals.length → D)
    (targetIndex : Fin targetAmbient.length) :
    context.targetEnvironment
        (ConcreteElaboration.rootEnvironment sourceAmbient sourceLocals
          sourceOuter sourceLocal)
        (rootOuterIndex targetAmbient targetLocals targetIndex) =
      targetOuter targetIndex := by
  let sourceIndex :=
    (PromotedContextWitness.sourceIndex context
      (rootOuterIndex targetAmbient targetLocals targetIndex))
  have corresponding := context.sourceIndex_get
    (rootOuterIndex targetAmbient targetLocals targetIndex)
  have sourceOuterMember : targetAmbient.get targetIndex ∈ sourceAmbient := by
    exact ambientSubset _ (List.get_mem _ _)
  let outerSourceIndex := Classical.choose
    (ConcreteElaboration.WireContext.lookup?_complete sourceOuterMember)
  have outerLookup := Classical.choose_spec
    (ConcreteElaboration.WireContext.lookup?_complete sourceOuterMember)
  let sourceRootIndex := rootOuterIndex sourceAmbient sourceLocals
    outerSourceIndex
  have sourceRootIndexEq : sourceRootIndex = sourceIndex :=
    ConcreteElaboration.WireContext.lookup?_unique sourceExact
      (context.sourceIndex_lookup
        (rootOuterIndex targetAmbient targetLocals targetIndex)) (by
          calc
            _ = sourceAmbient.get outerSourceIndex := rootOuterIndex_get _ _ _
            _ = targetAmbient.get targetIndex :=
              (ConcreteElaboration.WireContext.lookup?_sound outerLookup)
            _ = _ := (rootOuterIndex_get _ _ _).symm)
  unfold PromotedContextWitness.targetEnvironment
  dsimp [sourceIndex] at sourceRootIndexEq
  rw [← sourceRootIndexEq, rootEnvironment_outer]
  exact outerAgreement outerSourceIndex targetIndex
    (ConcreteElaboration.WireContext.lookup?_sound outerLookup)

theorem rootSelectedTargetEnvironment_outer
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input)
    (context : PromotedContextWitness trace sourceContext targetContext)
    (sourceExact : sourceContext.Exact (trace.targetIndex wellFormed))
    (sourceEnvironment : Fin sourceContext.length → D)
    (index : Fin (targetContext.extend outer).length) :
    let selected := context.extendRootSelected trace wellFormed sourceContext
      targetContext sourceExact
    selected.targetEnvironment sourceEnvironment
        (extendedOuterIndex (targetContext.extend outer) trace.inner index) =
      ConcreteElaboration.extendedEnvironment targetContext outer
        (context.targetEnvironment sourceEnvironment)
        (trace.emptyOuterEnvironment D) index := by
  dsimp only
  let selected := context.extendRootSelected trace wellFormed sourceContext
    targetContext sourceExact
  let outerContext := targetContext.extend outer
  let contextEq : outerContext = targetContext := trace.extendOuter_eq _
  let targetIndex : Fin targetContext.length :=
    Fin.cast (congrArg List.length contextEq) index
  have sameWire :
      (outerContext.extend trace.inner).get
          (extendedOuterIndex outerContext trace.inner index) =
        targetContext.get targetIndex := by
    rw [extendedOuterIndex_get]
    simpa [outerContext, targetIndex, contextEq]
  calc
    _ = context.targetEnvironment sourceEnvironment targetIndex :=
      selected.targetEnvironment_eq_of_get context sourceExact.nodup
        sourceEnvironment _ _ sameWire
    _ = _ := by
      rw [trace.extendedEnvironment_outer_empty targetContext
        (context.targetEnvironment sourceEnvironment)]

theorem rootSelectedSourceEnvironment_outer
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (sourceAmbient sourceLocals :
      ConcreteElaboration.WireContext trace.sourceDiagram)
    (targetAmbient targetLocals : ConcreteElaboration.WireContext input)
    (context : PromotedContextWitness trace
      (sourceAmbient ++ sourceLocals) (targetAmbient ++ targetLocals))
    (sourceExact :
      (sourceAmbient ++ sourceLocals).Exact (trace.targetIndex wellFormed))
    (targetSelectedNodup :
      ((((targetAmbient ++ targetLocals).extend outer).extend
        trace.inner)).Nodup)
    (ambientSubset : ∀ wire, wire ∈ sourceAmbient → wire ∈ targetAmbient)
    (sourceOuter : Fin sourceAmbient.length → D)
    (targetOuter : Fin targetAmbient.length → D)
    (outerAgreement :
      (trace.wireIdentityRelation sourceAmbient targetAmbient).EnvironmentsAgree
        sourceOuter targetOuter)
    (targetLocal : Fin targetLocals.length → D)
    (innerLocal :
      Fin (ConcreteElaboration.exactScopeWires input trace.inner).length → D)
    (sourceIndex : Fin sourceAmbient.length) :
    let targetRootEnvironment :=
      ConcreteElaboration.rootEnvironment targetAmbient targetLocals
        targetOuter targetLocal
    let targetOuterEnvironment :=
      ConcreteElaboration.extendedEnvironment
        (targetAmbient ++ targetLocals) outer targetRootEnvironment
        (trace.emptyOuterEnvironment D)
    let targetSelectedEnvironment :=
      ConcreteElaboration.extendedEnvironment
        ((targetAmbient ++ targetLocals).extend outer) trace.inner
        targetOuterEnvironment innerLocal
    let selected := context.extendRootSelected trace wellFormed
      (sourceAmbient ++ sourceLocals) (targetAmbient ++ targetLocals)
      sourceExact
    selected.sourceEnvironment
        (context.extendRootSelected_source_subset_target trace wellFormed
          (sourceAmbient ++ sourceLocals) (targetAmbient ++ targetLocals)
          sourceExact)
        targetSelectedEnvironment
        (rootOuterIndex sourceAmbient sourceLocals sourceIndex) =
      sourceOuter sourceIndex := by
  dsimp only
  let selected := context.extendRootSelected trace wellFormed
    (sourceAmbient ++ sourceLocals) (targetAmbient ++ targetLocals)
    sourceExact
  have targetAmbientMember :
      sourceAmbient.get sourceIndex ∈ targetAmbient :=
    ambientSubset _ (List.get_mem _ _)
  let targetAmbientIndex := Classical.choose
    (ConcreteElaboration.WireContext.lookup?_complete targetAmbientMember)
  have targetAmbientLookup := Classical.choose_spec
    (ConcreteElaboration.WireContext.lookup?_complete targetAmbientMember)
  let targetRootIndex := rootOuterIndex targetAmbient targetLocals
    targetAmbientIndex
  let targetOuterIndex := extendedOuterIndex
    (targetAmbient ++ targetLocals) outer targetRootIndex
  let targetSelectedIndex := extendedOuterIndex
    ((targetAmbient ++ targetLocals).extend outer) trace.inner
    targetOuterIndex
  let sourceRootIndex := rootOuterIndex sourceAmbient sourceLocals sourceIndex
  let sourceSubset :=
    context.extendRootSelected_source_subset_target trace wellFormed
      (sourceAmbient ++ sourceLocals) (targetAmbient ++ targetLocals)
      sourceExact
  have corresponding :
      ((((targetAmbient ++ targetLocals).extend outer).extend
          trace.inner)).get targetSelectedIndex =
        (sourceAmbient ++ sourceLocals).get sourceRootIndex := by
    calc
      _ = ((targetAmbient ++ targetLocals).extend outer).get
          targetOuterIndex :=
        extendedOuterIndex_get
          ((targetAmbient ++ targetLocals).extend outer) trace.inner
          targetOuterIndex
      _ = (targetAmbient ++ targetLocals).get targetRootIndex :=
        extendedOuterIndex_get (targetAmbient ++ targetLocals) outer
          targetRootIndex
      _ = targetAmbient.get targetAmbientIndex :=
        rootOuterIndex_get targetAmbient targetLocals targetAmbientIndex
      _ = sourceAmbient.get sourceIndex :=
        ConcreteElaboration.WireContext.lookup?_sound targetAmbientLookup
      _ = _ := (rootOuterIndex_get sourceAmbient sourceLocals sourceIndex).symm
  have targetSelectedIndexEq :
      targetSelectedIndex = selected.targetIndex sourceSubset sourceRootIndex :=
    ConcreteElaboration.WireContext.lookup?_unique targetSelectedNodup
      (selected.targetIndex_lookup sourceSubset sourceRootIndex) corresponding
  unfold PromotedContextWitness.sourceEnvironment
  rw [← targetSelectedIndexEq]
  simp [targetSelectedIndex, targetOuterIndex, targetRootIndex]
  exact (outerAgreement sourceIndex targetAmbientIndex
    (ConcreteElaboration.WireContext.lookup?_sound
      targetAmbientLookup).symm).symm

theorem targetRoot_doubleCut_denote_iff
    (trace : DoubleCutElimTrace input outer raw)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (targetContext : ConcreteElaboration.WireContext input)
    (keptItems : ItemSeq signature targetContext.length rels)
    (selectedItems : ItemSeq signature
      ((targetContext.extend outer).extend trace.inner).length rels)
    (targetEnvironment : Fin targetContext.length → model.Carrier)
    (relations : RelEnv model.Carrier rels) :
    denoteItemSeq model named targetEnvironment relations
        (keptItems.append
          (.cons
            (.cut
              (ConcreteElaboration.finishRegion input targetContext outer
                (.cons
                  (.cut
                    (ConcreteElaboration.finishRegion input
                      (targetContext.extend outer) trace.inner selectedItems))
                  .nil)))
            .nil)) ↔
      denoteItemSeq model named targetEnvironment relations keptItems ∧
        ∃ innerLocal :
            Fin (ConcreteElaboration.exactScopeWires input
              trace.inner).length → model.Carrier,
          denoteItemSeq model named
            (ConcreteElaboration.extendedEnvironment
              (targetContext.extend outer) trace.inner
              (ConcreteElaboration.extendedEnvironment targetContext outer
                targetEnvironment (trace.emptyOuterEnvironment model.Carrier))
              innerLocal)
            relations selectedItems := by
  simp only [denoteItemSeq_append, denoteItemSeq_cons, denoteItemSeq_nil,
    and_true, cut_denotes_negation]
  apply and_congr Iff.rfl
  rw [finishRegion_denote_iff]
  constructor
  · intro doubleNegation
    have innerRegion :
        denoteRegion model named
          (ConcreteElaboration.extendedEnvironment targetContext outer
            targetEnvironment (trace.emptyOuterEnvironment model.Carrier))
          relations
          (ConcreteElaboration.finishRegion input (targetContext.extend outer)
            trace.inner selectedItems) := by
      apply Classical.byContradiction
      intro notInner
      apply doubleNegation
      refine ⟨trace.emptyOuterEnvironment model.Carrier, ?_⟩
      simpa only [denoteItemSeq_cons, denoteItemSeq_nil, and_true,
        cut_denotes_negation] using notInner
    exact (finishRegion_denote_iff input (targetContext.extend outer)
      trace.inner selectedItems model named
      (ConcreteElaboration.extendedEnvironment targetContext outer
        targetEnvironment (trace.emptyOuterEnvironment model.Carrier))
      relations).mp innerRegion
  · intro innerItems
    have innerRegion := (finishRegion_denote_iff input
      (targetContext.extend outer) trace.inner selectedItems model named
      (ConcreteElaboration.extendedEnvironment targetContext outer
        targetEnvironment (trace.emptyOuterEnvironment model.Carrier))
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
          (ConcreteElaboration.extendedEnvironment targetContext outer
            targetEnvironment (trace.emptyOuterEnvironment model.Carrier))
          relations
          (ConcreteElaboration.finishRegion input (targetContext.extend outer)
            trace.inner selectedItems) := by
      simpa only [denoteItemSeq_cons, denoteItemSeq_nil, and_true,
        cut_denotes_negation] using outerDenotation
    exact notInner innerRegion

theorem focusedRootPartition_transport
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (sourceAmbient sourceLocals :
      ConcreteElaboration.WireContext trace.sourceDiagram)
    (targetAmbient targetLocals : ConcreteElaboration.WireContext input)
    (context : PromotedContextWitness trace
      (sourceAmbient ++ sourceLocals) (targetAmbient ++ targetLocals))
    (sourceExact :
      (sourceAmbient ++ sourceLocals).Exact (trace.targetIndex wellFormed))
    (targetSelectedNodup :
      ((((targetAmbient ++ targetLocals).extend outer).extend
        trace.inner)).Nodup)
    (targetAmbientSubset :
      ∀ wire, wire ∈ targetAmbient → wire ∈ sourceAmbient)
    (sourceAmbientSubset :
      ∀ wire, wire ∈ sourceAmbient → wire ∈ targetAmbient)
    (sourceKept sourceSelected : ItemSeq signature
      (sourceAmbient ++ sourceLocals).length [])
    (targetKept : ItemSeq signature
      (targetAmbient ++ targetLocals).length [])
    (targetSelected : ItemSeq signature
      ((((targetAmbient ++ targetLocals).extend outer).extend
        trace.inner)).length [])
    (keptSimulation : ConcreteElaboration.ItemSeqSimulation model named
      direction context.indexRelation sourceKept targetKept)
    (selectedSimulation : ConcreteElaboration.ItemSeqSimulation model named
      direction
        (context.extendRootSelected trace wellFormed
          (sourceAmbient ++ sourceLocals) (targetAmbient ++ targetLocals)
          sourceExact).indexRelation
        sourceSelected targetSelected) :
    ConcreteElaboration.DirectionalRootTransport direction
      sourceAmbient sourceLocals targetAmbient targetLocals
      (trace.wireIdentityRelation sourceAmbient targetAmbient)
      model named (sourceKept.append sourceSelected)
      (targetKept.append
        (.cons
          (.cut
            (ConcreteElaboration.finishRegion input
              (targetAmbient ++ targetLocals) outer
              (.cons
                (.cut
                  (ConcreteElaboration.finishRegion input
                    ((targetAmbient ++ targetLocals).extend outer)
                    trace.inner targetSelected))
                .nil)))
          .nil)) := by
  intro sourceOuter targetOuter relations outerAgreement
  let selected := context.extendRootSelected trace wellFormed
    (sourceAmbient ++ sourceLocals) (targetAmbient ++ targetLocals)
    sourceExact
  cases direction with
  | forward =>
      intro sourceLocal sourceDenotation
      obtain ⟨sourceKeptDenotation, sourceSelectedDenotation⟩ :=
        (denoteItemSeq_append model named
          (ConcreteElaboration.rootEnvironment sourceAmbient sourceLocals
            sourceOuter sourceLocal)
          relations sourceKept sourceSelected).mp sourceDenotation
      let sourceEnvironment :=
        ConcreteElaboration.rootEnvironment sourceAmbient sourceLocals
          sourceOuter sourceLocal
      let targetRootPulled := context.targetEnvironment sourceEnvironment
      let targetLocal := rootLocalPart targetAmbient targetLocals
        targetRootPulled
      have targetRootEq :
          ConcreteElaboration.rootEnvironment targetAmbient targetLocals
              targetOuter targetLocal = targetRootPulled := by
        apply rootEnvironment_of_parts
        intro targetIndex
        exact trace.rootTargetEnvironment_outer sourceAmbient sourceLocals
          targetAmbient targetLocals context sourceExact.nodup
          targetAmbientSubset sourceOuter targetOuter outerAgreement
          sourceLocal targetIndex
      have contextAgreement : context.indexRelation.EnvironmentsAgree
          sourceEnvironment targetRootPulled :=
        context.targetEnvironment_agrees sourceExact.nodup sourceEnvironment
      have targetKeptDenotation := keptSimulation sourceEnvironment
        targetRootPulled relations contextAgreement sourceKeptDenotation
      let targetSelectedPulled := selected.targetEnvironment sourceEnvironment
      let innerLocal := localEnvironmentPart
        ((targetAmbient ++ targetLocals).extend outer) trace.inner
        targetSelectedPulled
      have targetSelectedEq :
          ConcreteElaboration.extendedEnvironment
              ((targetAmbient ++ targetLocals).extend outer) trace.inner
              (ConcreteElaboration.extendedEnvironment
                (targetAmbient ++ targetLocals) outer targetRootPulled
                (trace.emptyOuterEnvironment model.Carrier))
              innerLocal = targetSelectedPulled := by
        apply extendedEnvironment_of_parts
        intro index
        exact trace.rootSelectedTargetEnvironment_outer wellFormed
          (sourceAmbient ++ sourceLocals) (targetAmbient ++ targetLocals)
          context sourceExact sourceEnvironment index
      have selectedAgreement : selected.indexRelation.EnvironmentsAgree
          sourceEnvironment targetSelectedPulled :=
        selected.targetEnvironment_agrees sourceExact.nodup sourceEnvironment
      have targetSelectedDenotation := selectedSimulation sourceEnvironment
        targetSelectedPulled relations selectedAgreement
        sourceSelectedDenotation
      refine ⟨targetLocal, ?_⟩
      apply (trace.targetRoot_doubleCut_denote_iff model named
        (targetAmbient ++ targetLocals) targetKept targetSelected
        (ConcreteElaboration.rootEnvironment targetAmbient targetLocals
          targetOuter targetLocal) relations).mpr
      refine ⟨?_, innerLocal, ?_⟩
      · rw [targetRootEq]
        exact targetKeptDenotation
      · rw [targetRootEq, targetSelectedEq]
        exact targetSelectedDenotation
  | backward =>
      intro targetLocal targetDenotation
      let targetRootEnvironment :=
        ConcreteElaboration.rootEnvironment targetAmbient targetLocals
          targetOuter targetLocal
      obtain ⟨targetKeptDenotation, innerLocal,
          targetSelectedDenotation⟩ :=
        (trace.targetRoot_doubleCut_denote_iff model named
          (targetAmbient ++ targetLocals) targetKept targetSelected
          targetRootEnvironment relations).mp targetDenotation
      let targetOuterEnvironment :=
        ConcreteElaboration.extendedEnvironment
          (targetAmbient ++ targetLocals) outer targetRootEnvironment
          (trace.emptyOuterEnvironment model.Carrier)
      let targetSelectedEnvironment :=
        ConcreteElaboration.extendedEnvironment
          ((targetAmbient ++ targetLocals).extend outer) trace.inner
          targetOuterEnvironment innerLocal
      let sourceSubset :=
        context.extendRootSelected_source_subset_target trace wellFormed
          (sourceAmbient ++ sourceLocals) (targetAmbient ++ targetLocals)
          sourceExact
      let sourceEnvironment := selected.sourceEnvironment sourceSubset
        targetSelectedEnvironment
      let sourceLocal := rootLocalPart sourceAmbient sourceLocals
        sourceEnvironment
      have sourceEnvironmentEq :
          ConcreteElaboration.rootEnvironment sourceAmbient sourceLocals
              sourceOuter sourceLocal = sourceEnvironment := by
        apply rootEnvironment_of_parts
        intro sourceIndex
        exact trace.rootSelectedSourceEnvironment_outer wellFormed
          sourceAmbient sourceLocals targetAmbient targetLocals context
          sourceExact targetSelectedNodup sourceAmbientSubset sourceOuter
          targetOuter outerAgreement targetLocal innerLocal sourceIndex
      have selectedAgreement : selected.indexRelation.EnvironmentsAgree
          sourceEnvironment targetSelectedEnvironment :=
        selected.sourceEnvironment_agrees sourceSubset targetSelectedNodup
          targetSelectedEnvironment
      have sourceSelectedDenotation := selectedSimulation sourceEnvironment
        targetSelectedEnvironment relations selectedAgreement
        targetSelectedDenotation
      have contextAgreement : context.indexRelation.EnvironmentsAgree
          sourceEnvironment targetRootEnvironment := by
        intro sourceIndex targetIndex related
        let targetOuterIndex := extendedOuterIndex
          (targetAmbient ++ targetLocals) outer targetIndex
        let targetSelectedIndex := extendedOuterIndex
          ((targetAmbient ++ targetLocals).extend outer) trace.inner
          targetOuterIndex
        have selectedRelated : selected.indexRelation.Rel sourceIndex
            targetSelectedIndex := by
          exact related.trans (by
            calc
              _ = ((targetAmbient ++ targetLocals).extend outer).get
                  targetOuterIndex :=
                (extendedOuterIndex_get (targetAmbient ++ targetLocals)
                  outer targetIndex).symm
              _ = _ := (extendedOuterIndex_get
                ((targetAmbient ++ targetLocals).extend outer)
                trace.inner targetOuterIndex).symm)
        have agreement := selectedAgreement sourceIndex targetSelectedIndex
          selectedRelated
        simpa [targetSelectedEnvironment, targetOuterEnvironment,
          targetSelectedIndex, targetOuterIndex] using agreement
      have sourceKeptDenotation := keptSimulation sourceEnvironment
        targetRootEnvironment relations contextAgreement targetKeptDenotation
      refine ⟨sourceLocal, ?_⟩
      apply (denoteItemSeq_append model named
        (ConcreteElaboration.rootEnvironment sourceAmbient sourceLocals
          sourceOuter sourceLocal)
        relations sourceKept sourceSelected).mpr
      rw [sourceEnvironmentEq]
      exact ⟨sourceKeptDenotation, sourceSelectedDenotation⟩

end VisualProof.Rule.DoubleCutElimTrace
