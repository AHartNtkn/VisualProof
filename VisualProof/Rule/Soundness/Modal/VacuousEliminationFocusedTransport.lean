import VisualProof.Rule.Soundness.Modal.VacuousEliminationFocusedItems

namespace VisualProof.Rule.VacuousElimTrace

open VisualProof
open VisualProof.Theory
open VisualProof.Diagram
open VisualProof.Rule.DoubleCutElimTrace

theorem focusedPartition_regionSimulation
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    {sourceRels targetRels : RelCtx}
    (direction : ConcreteElaboration.SimulationDirection)
    (sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input)
    (context : PromotedContextWitness trace sourceContext targetContext)
    (sourceExact :
      (sourceContext.extend (trace.targetIndex wellFormed)).Exact
        (trace.targetIndex wellFormed))
    (targetSelectedNodup :
      ((targetContext.extend trace.parent).extend bubble).Nodup)
    (relationMap : RelationRenaming sourceRels targetRels)
    (sourceKept sourceSelected : ItemSeq signature
      (sourceContext.extend (trace.targetIndex wellFormed)).length sourceRels)
    (targetKept : ItemSeq signature
      (targetContext.extend trace.parent).length targetRels)
    (targetSelected : ItemSeq signature
      ((targetContext.extend trace.parent).extend bubble).length
      (trace.arity :: targetRels))
    (keptSimulation : ConcreteElaboration.ItemSeqSimulation model named
      direction (context.extendFocused wellFormed).indexRelation
      (sourceKept.renameRelations relationMap) targetKept)
    (selectedSimulation : ConcreteElaboration.ItemSeqSimulation model named
      direction (context.extendSelected wellFormed).indexRelation
      (sourceSelected.renameRelations (fun relation =>
        ConcreteElaboration.BinderContext.liftVar trace.arity
          (relationMap relation)))
      targetSelected) :
    ConcreteElaboration.RegionSimulation model named direction
      context.indexRelation
      ((ConcreteElaboration.finishRegion trace.sourceDiagram sourceContext
        (trace.targetIndex wellFormed)
        (sourceKept.append sourceSelected)).renameRelations relationMap)
      (ConcreteElaboration.finishRegion input targetContext trace.parent
        (targetKept.append (.cons
          (.bubble trace.arity
            (ConcreteElaboration.finishRegion input
              (targetContext.extend trace.parent) bubble targetSelected))
          .nil))) := by
  intro sourceOuter targetOuter targetRelations outerAgreement
  let focused := context.extendFocused wellFormed
  let selected := context.extendSelected wellFormed
  let sourceRelations : RelEnv model.Carrier sourceRels :=
    RelEnv.pullback relationMap targetRelations
  have baseAgrees : RelEnv.Agrees relationMap sourceRelations targetRelations :=
    RelEnv.pullback_agrees relationMap targetRelations
  let bubbleMap : RelationRenaming sourceRels
      (trace.arity :: targetRels) :=
    fun relation => ConcreteElaboration.BinderContext.liftVar trace.arity
      (relationMap relation)
  have bubbleAgrees (fresh : Relation model.Carrier trace.arity) :
      RelEnv.Agrees bubbleMap sourceRelations (fresh, targetRelations) := by
    intro binderArity relation
    exact baseAgrees binderArity relation
  have sourceRename :
      denoteRegion model named sourceOuter targetRelations
          ((ConcreteElaboration.finishRegion trace.sourceDiagram sourceContext
            (trace.targetIndex wellFormed)
            (sourceKept.append sourceSelected)).renameRelations relationMap) ↔
        denoteRegion model named sourceOuter sourceRelations
          (ConcreteElaboration.finishRegion trace.sourceDiagram sourceContext
            (trace.targetIndex wellFormed)
            (sourceKept.append sourceSelected)) :=
    denoteRegion_renameRelations model named relationMap sourceRelations
      targetRelations baseAgrees sourceOuter _
  cases direction with
  | forward =>
      intro sourceDenotation
      obtain ⟨sourceLocal, sourceKeptDenotation,
          sourceSelectedDenotation⟩ :=
        (trace.sourceFocused_partition_denote_iff wellFormed model named
          sourceContext sourceKept sourceSelected sourceOuter
          sourceRelations).mp (sourceRename.mp sourceDenotation)
      let sourceEnvironment :=
        ConcreteElaboration.extendedEnvironment sourceContext
          (trace.targetIndex wellFormed) sourceOuter sourceLocal
      let targetFocusPulled := focused.targetEnvironment sourceEnvironment
      let targetLocal := localEnvironmentPart targetContext trace.parent
        targetFocusPulled
      have targetFocusEq :
          ConcreteElaboration.extendedEnvironment targetContext trace.parent
              targetOuter targetLocal = targetFocusPulled := by
        apply extendedEnvironment_of_parts
        intro targetIndex
        exact trace.focusedTargetEnvironment_outer wellFormed sourceContext
          targetContext context sourceExact sourceOuter targetOuter
          outerAgreement sourceLocal targetIndex
      have focusedAgreement :
          focused.indexRelation.EnvironmentsAgree sourceEnvironment
            targetFocusPulled :=
        focused.targetEnvironment_agrees sourceExact.nodup sourceEnvironment
      have sourceKeptRenamed :
          denoteItemSeq model named sourceEnvironment targetRelations
            (sourceKept.renameRelations relationMap) :=
        (denoteItemSeq_renameRelations model named relationMap sourceRelations
          targetRelations baseAgrees sourceEnvironment sourceKept).mpr
          sourceKeptDenotation
      have targetKeptDenotation := keptSimulation sourceEnvironment
        targetFocusPulled targetRelations focusedAgreement sourceKeptRenamed
      let targetSelectedPulled := selected.targetEnvironment sourceEnvironment
      let bubbleLocal := localEnvironmentPart
        (targetContext.extend trace.parent) bubble targetSelectedPulled
      have targetSelectedEq :
          ConcreteElaboration.extendedEnvironment
              (targetContext.extend trace.parent) bubble targetFocusPulled
              bubbleLocal = targetSelectedPulled := by
        apply extendedEnvironment_of_parts
        intro index
        exact trace.selectedTargetEnvironment_outer wellFormed sourceContext
          targetContext context sourceExact sourceEnvironment index
      have selectedAgreement :
          selected.indexRelation.EnvironmentsAgree sourceEnvironment
            targetSelectedPulled :=
        selected.targetEnvironment_agrees sourceExact.nodup sourceEnvironment
      let fresh : Relation model.Carrier trace.arity := fun _ => False
      have sourceSelectedRenamed :
          denoteItemSeq (relCtx := trace.arity :: targetRels) model named
            sourceEnvironment (fresh, targetRelations)
            (sourceSelected.renameRelations bubbleMap) :=
        (denoteItemSeq_renameRelations model named bubbleMap sourceRelations
          (fresh, targetRelations) (bubbleAgrees fresh) sourceEnvironment
          sourceSelected).mpr sourceSelectedDenotation
      have targetSelectedDenotation := selectedSimulation sourceEnvironment
        targetSelectedPulled (fresh, targetRelations) selectedAgreement
        sourceSelectedRenamed
      apply (trace.targetFocused_bubble_denote_iff model named targetContext
        targetKept targetSelected targetOuter targetRelations).mpr
      refine ⟨targetLocal, ?_, fresh, bubbleLocal, ?_⟩
      · rw [targetFocusEq]
        exact targetKeptDenotation
      · rw [targetFocusEq, targetSelectedEq]
        exact targetSelectedDenotation
  | backward =>
      intro targetDenotation
      obtain ⟨targetLocal, targetKeptDenotation, fresh, bubbleLocal,
          targetSelectedDenotation⟩ :=
        (trace.targetFocused_bubble_denote_iff model named targetContext
          targetKept targetSelected targetOuter targetRelations).mp
          targetDenotation
      let targetFocusEnvironment :=
        ConcreteElaboration.extendedEnvironment targetContext trace.parent
          targetOuter targetLocal
      let targetSelectedEnvironment :=
        ConcreteElaboration.extendedEnvironment
          (targetContext.extend trace.parent) bubble targetFocusEnvironment
          bubbleLocal
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
          targetOuter outerAgreement targetLocal bubbleLocal sourceIndex
      have selectedAgreement :
          selected.indexRelation.EnvironmentsAgree sourceEnvironment
            targetSelectedEnvironment :=
        selected.sourceEnvironment_agrees sourceSubset targetSelectedNodup
          targetSelectedEnvironment
      have sourceSelectedRenamed := selectedSimulation sourceEnvironment
        targetSelectedEnvironment (fresh, targetRelations) selectedAgreement
        targetSelectedDenotation
      have sourceSelectedDenotation :
          denoteItemSeq model named sourceEnvironment sourceRelations
            sourceSelected :=
        (denoteItemSeq_renameRelations model named bubbleMap sourceRelations
          (fresh, targetRelations) (bubbleAgrees fresh) sourceEnvironment
          sourceSelected).mp sourceSelectedRenamed
      have focusedAgreement :
          focused.indexRelation.EnvironmentsAgree sourceEnvironment
            targetFocusEnvironment := by
        intro sourceIndex targetIndex related
        let targetSelectedIndex := extendedOuterIndex
          (targetContext.extend trace.parent) bubble targetIndex
        have selectedRelated : selected.indexRelation.Rel sourceIndex
            targetSelectedIndex := by
          exact related.trans (extendedOuterIndex_get
            (targetContext.extend trace.parent) bubble targetIndex).symm
        have agreement := selectedAgreement sourceIndex targetSelectedIndex
          selectedRelated
        simpa [targetSelectedEnvironment, targetSelectedIndex] using agreement
      have sourceKeptRenamed := keptSimulation sourceEnvironment
        targetFocusEnvironment targetRelations focusedAgreement
        targetKeptDenotation
      have sourceKeptDenotation :
          denoteItemSeq model named sourceEnvironment sourceRelations
            sourceKept :=
        (denoteItemSeq_renameRelations model named relationMap sourceRelations
          targetRelations baseAgrees sourceEnvironment sourceKept).mp
          sourceKeptRenamed
      apply sourceRename.mpr
      apply (trace.sourceFocused_partition_denote_iff wellFormed model named
        sourceContext sourceKept sourceSelected sourceOuter
        sourceRelations).mpr
      refine ⟨sourceLocal, ?_, ?_⟩
      · rw [sourceEnvironmentEq]
        exact sourceKeptDenotation
      · rw [sourceEnvironmentEq]
        exact sourceSelectedDenotation

end VisualProof.Rule.VacuousElimTrace
