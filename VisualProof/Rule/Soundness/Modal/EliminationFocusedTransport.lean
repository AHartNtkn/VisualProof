import VisualProof.Rule.Soundness.Modal.EliminationFocusedItems

namespace VisualProof.Concrete.DoubleCutElimTrace

open VisualProof.Concrete
open VisualProof.Rule

open VisualProof
open VisualProof.Theory
open VisualProof.Diagram

theorem focusedPartition_regionSimulation
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed )
    (model : Model)
    (direction : Concrete.Elaboration.SimulationDirection)
    (sourceContext : Concrete.Elaboration.WireContext trace.sourceDiagram)
    (targetContext : Concrete.Elaboration.WireContext input)
    (context : PromotedContextWitness trace sourceContext targetContext)
    (sourceExact :
      (sourceContext.extend (trace.targetIndex wellFormed)).Exact
        (trace.targetIndex wellFormed))
    (targetSelectedNodup :
      (((targetContext.extend trace.target).extend outer).extend
        trace.inner).Nodup)
    (sourceKept sourceSelected : ItemSeq
      (sourceContext.extend (trace.targetIndex wellFormed)).length rels)
    (targetKept : ItemSeq
      (targetContext.extend trace.target).length rels)
    (targetSelected : ItemSeq
      (((targetContext.extend trace.target).extend outer).extend
        trace.inner).length rels)
    (keptSimulation : Concrete.Elaboration.ItemSeqSimulation model
      direction (context.extendFocused wellFormed).indexRelation
      sourceKept targetKept)
    (selectedSimulation : Concrete.Elaboration.ItemSeqSimulation model
      direction (context.extendSelected wellFormed).indexRelation
      sourceSelected targetSelected) :
    Concrete.Elaboration.RegionSimulation model  direction
      context.indexRelation
      (Concrete.Elaboration.finishRegion trace.sourceDiagram sourceContext
        (trace.targetIndex wellFormed)
        (sourceKept.append sourceSelected))
      (Concrete.Elaboration.finishRegion input targetContext trace.target
        (targetKept.append
          (.cons
            (.cut
              (Concrete.Elaboration.finishRegion input
                (targetContext.extend trace.target) outer
                (.cons
                  (.cut
                    (Concrete.Elaboration.finishRegion input
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
        (trace.sourceFocused_partition_denote_iff wellFormed model
          sourceContext sourceKept sourceSelected sourceOuter relations).mp
          sourceDenotation
      let sourceEnvironment :=
        Concrete.Elaboration.extendedEnvironment sourceContext
          (trace.targetIndex wellFormed) sourceOuter sourceLocal
      let targetFocusPulled :=
        focused.targetEnvironment sourceEnvironment
      let targetLocal := localEnvironmentPart targetContext trace.target
        targetFocusPulled
      have targetFocusEq :
          Concrete.Elaboration.extendedEnvironment targetContext trace.target
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
          Concrete.Elaboration.extendedEnvironment
              ((targetContext.extend trace.target).extend outer) trace.inner
              (Concrete.Elaboration.extendedEnvironment
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
      apply (trace.targetFocused_doubleCut_denote_iff model  targetContext
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
        (trace.targetFocused_doubleCut_denote_iff model  targetContext
          targetKept targetSelected targetOuter relations).mp targetDenotation
      let targetFocusEnvironment :=
        Concrete.Elaboration.extendedEnvironment targetContext trace.target
          targetOuter targetLocal
      let targetOuterEnvironment :=
        Concrete.Elaboration.extendedEnvironment
          (targetContext.extend trace.target) outer targetFocusEnvironment
          (trace.emptyOuterEnvironment model.Carrier)
      let targetSelectedEnvironment :=
        Concrete.Elaboration.extendedEnvironment
          ((targetContext.extend trace.target).extend outer) trace.inner
          targetOuterEnvironment innerLocal
      let sourceSubset :=
        context.extendSelected_source_subset_target wellFormed
      let sourceEnvironment :=
        selected.sourceEnvironment sourceSubset targetSelectedEnvironment
      let sourceLocal := localEnvironmentPart sourceContext
        (trace.targetIndex wellFormed) sourceEnvironment
      have sourceEnvironmentEq :
          Concrete.Elaboration.extendedEnvironment sourceContext
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
      apply (trace.sourceFocused_partition_denote_iff wellFormed model
        sourceContext sourceKept sourceSelected sourceOuter relations).mpr
      refine ⟨sourceLocal, ?_, ?_⟩
      · rw [sourceEnvironmentEq]
        exact sourceKeptDenotation
      · rw [sourceEnvironmentEq]
        exact sourceSelectedDenotation

end VisualProof.Concrete.DoubleCutElimTrace
