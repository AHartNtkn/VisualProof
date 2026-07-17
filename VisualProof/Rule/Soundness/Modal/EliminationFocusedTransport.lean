import VisualProof.Rule.Soundness.Modal.EliminationFocusedItems

namespace VisualProof.Rule.DoubleCutElimTrace

open VisualProof
open VisualProof.Theory
open VisualProof.Diagram

theorem focusedPartition_regionSimulation
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input)
    (context : PromotedContextWitness trace sourceContext targetContext)
    (sourceExact :
      (sourceContext.extend (trace.targetIndex wellFormed)).Exact
        (trace.targetIndex wellFormed))
    (targetSelectedNodup :
      (((targetContext.extend trace.target).extend outer).extend
        trace.inner).Nodup)
    (sourceKept sourceSelected : ItemSeq signature
      (sourceContext.extend (trace.targetIndex wellFormed)).length rels)
    (targetKept : ItemSeq signature
      (targetContext.extend trace.target).length rels)
    (targetSelected : ItemSeq signature
      (((targetContext.extend trace.target).extend outer).extend
        trace.inner).length rels)
    (keptSimulation : ConcreteElaboration.ItemSeqSimulation model named
      direction (context.extendFocused wellFormed).indexRelation
      sourceKept targetKept)
    (selectedSimulation : ConcreteElaboration.ItemSeqSimulation model named
      direction (context.extendSelected wellFormed).indexRelation
      sourceSelected targetSelected) :
    ConcreteElaboration.RegionSimulation model named direction
      context.indexRelation
      (ConcreteElaboration.finishRegion trace.sourceDiagram sourceContext
        (trace.targetIndex wellFormed)
        (sourceKept.append sourceSelected))
      (ConcreteElaboration.finishRegion input targetContext trace.target
        (targetKept.append
          (.cons
            (.cut
              (ConcreteElaboration.finishRegion input
                (targetContext.extend trace.target) outer
                (.cons
                  (.cut
                    (ConcreteElaboration.finishRegion input
                      ((targetContext.extend trace.target).extend outer)
                      trace.inner targetSelected))
                  .nil)))
            .nil))) := by
  intro sourceOuter targetOuter relations outerAgreement
  let focused := context.extendFocused wellFormed
  let selected := context.extendSelected wellFormed
  cases direction with
  | forward =>
      intro sourceDenotation
      obtain ⟨sourceLocal, sourceKeptDenotation,
          sourceSelectedDenotation⟩ :=
        (trace.sourceFocused_partition_denote_iff wellFormed model named
          sourceContext sourceKept sourceSelected sourceOuter relations).mp
          sourceDenotation
      let sourceEnvironment :=
        ConcreteElaboration.extendedEnvironment sourceContext
          (trace.targetIndex wellFormed) sourceOuter sourceLocal
      let targetFocusPulled :=
        focused.targetEnvironment sourceEnvironment
      let targetLocal := localEnvironmentPart targetContext trace.target
        targetFocusPulled
      have targetFocusEq :
          ConcreteElaboration.extendedEnvironment targetContext trace.target
              targetOuter targetLocal =
            targetFocusPulled := by
        apply extendedEnvironment_of_parts
        intro targetIndex
        exact trace.focusedTargetEnvironment_outer wellFormed sourceContext
          targetContext context sourceExact sourceOuter targetOuter
          outerAgreement sourceLocal targetIndex
      have focusedAgreement :
          focused.indexRelation.EnvironmentsAgree sourceEnvironment
            targetFocusPulled :=
        focused.targetEnvironment_agrees sourceExact.nodup sourceEnvironment
      have targetKeptDenotation := keptSimulation sourceEnvironment
        targetFocusPulled relations focusedAgreement sourceKeptDenotation
      let targetSelectedPulled :=
        selected.targetEnvironment sourceEnvironment
      let innerLocal := localEnvironmentPart
        ((targetContext.extend trace.target).extend outer) trace.inner
        targetSelectedPulled
      have targetSelectedEq :
          ConcreteElaboration.extendedEnvironment
              ((targetContext.extend trace.target).extend outer) trace.inner
              (ConcreteElaboration.extendedEnvironment
                (targetContext.extend trace.target) outer targetFocusPulled
                (trace.emptyOuterEnvironment model.Carrier))
              innerLocal =
            targetSelectedPulled := by
        apply extendedEnvironment_of_parts
        intro index
        exact trace.selectedTargetEnvironment_outer wellFormed sourceContext
          targetContext context sourceExact sourceEnvironment index
      have selectedAgreement :
          selected.indexRelation.EnvironmentsAgree sourceEnvironment
            targetSelectedPulled :=
        selected.targetEnvironment_agrees sourceExact.nodup sourceEnvironment
      have targetSelectedDenotation := selectedSimulation sourceEnvironment
        targetSelectedPulled relations selectedAgreement
        sourceSelectedDenotation
      apply (trace.targetFocused_doubleCut_denote_iff model named targetContext
        targetKept targetSelected targetOuter relations).mpr
      refine ⟨targetLocal, ?_, innerLocal, ?_⟩
      · rw [targetFocusEq]
        exact targetKeptDenotation
      · rw [targetFocusEq, targetSelectedEq]
        exact targetSelectedDenotation
  | backward =>
      intro targetDenotation
      obtain ⟨targetLocal, targetKeptDenotation, innerLocal,
          targetSelectedDenotation⟩ :=
        (trace.targetFocused_doubleCut_denote_iff model named targetContext
          targetKept targetSelected targetOuter relations).mp targetDenotation
      let targetFocusEnvironment :=
        ConcreteElaboration.extendedEnvironment targetContext trace.target
          targetOuter targetLocal
      let targetOuterEnvironment :=
        ConcreteElaboration.extendedEnvironment
          (targetContext.extend trace.target) outer targetFocusEnvironment
          (trace.emptyOuterEnvironment model.Carrier)
      let targetSelectedEnvironment :=
        ConcreteElaboration.extendedEnvironment
          ((targetContext.extend trace.target).extend outer) trace.inner
          targetOuterEnvironment innerLocal
      let sourceSubset :=
        context.extendSelected_source_subset_target wellFormed
      let sourceEnvironment :=
        selected.sourceEnvironment sourceSubset targetSelectedEnvironment
      let sourceLocal := localEnvironmentPart sourceContext
        (trace.targetIndex wellFormed) sourceEnvironment
      have sourceEnvironmentEq :
          ConcreteElaboration.extendedEnvironment sourceContext
              (trace.targetIndex wellFormed) sourceOuter sourceLocal =
            sourceEnvironment := by
        apply extendedEnvironment_of_parts
        intro sourceIndex
        exact trace.selectedSourceEnvironment_outer wellFormed sourceContext
          targetContext context sourceExact targetSelectedNodup sourceOuter
          targetOuter outerAgreement targetLocal innerLocal sourceIndex
      have selectedAgreement :
          selected.indexRelation.EnvironmentsAgree sourceEnvironment
            targetSelectedEnvironment :=
        selected.sourceEnvironment_agrees sourceSubset targetSelectedNodup
          targetSelectedEnvironment
      have sourceSelectedDenotation := selectedSimulation sourceEnvironment
        targetSelectedEnvironment relations selectedAgreement
        targetSelectedDenotation
      have focusedAgreement :
          focused.indexRelation.EnvironmentsAgree sourceEnvironment
            targetFocusEnvironment := by
        intro sourceIndex targetIndex related
        let targetOuterIndex := extendedOuterIndex
          (targetContext.extend trace.target) outer targetIndex
        let targetSelectedIndex := extendedOuterIndex
          ((targetContext.extend trace.target).extend outer) trace.inner
          targetOuterIndex
        have selectedRelated : selected.indexRelation.Rel sourceIndex
            targetSelectedIndex := by
          exact related.trans (by
            calc
              _ = ((targetContext.extend trace.target).extend outer).get
                  targetOuterIndex :=
                (extendedOuterIndex_get
                  (targetContext.extend trace.target) outer
                  targetIndex).symm
              _ = _ := (extendedOuterIndex_get
                ((targetContext.extend trace.target).extend outer)
                trace.inner targetOuterIndex).symm)
        have agreement := selectedAgreement sourceIndex targetSelectedIndex
          selectedRelated
        simpa [targetSelectedEnvironment, targetOuterEnvironment,
          targetSelectedIndex, targetOuterIndex] using agreement
      have sourceKeptDenotation := keptSimulation sourceEnvironment
        targetFocusEnvironment relations focusedAgreement targetKeptDenotation
      apply (trace.sourceFocused_partition_denote_iff wellFormed model named
        sourceContext sourceKept sourceSelected sourceOuter relations).mpr
      refine ⟨sourceLocal, ?_, ?_⟩
      · rw [sourceEnvironmentEq]
        exact sourceKeptDenotation
      · rw [sourceEnvironmentEq]
        exact sourceSelectedDenotation

end VisualProof.Rule.DoubleCutElimTrace
