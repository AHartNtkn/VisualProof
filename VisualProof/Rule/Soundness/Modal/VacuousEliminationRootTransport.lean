import VisualProof.Rule.Soundness.Modal.EliminationRoot
import VisualProof.Rule.Soundness.Modal.VacuousEliminationRoot

namespace VisualProof.Rule.VacuousElimTrace

open VisualProof
open VisualProof.Theory
open VisualProof.Diagram
open VisualProof.Rule.DoubleCutElimTrace

theorem rootTargetEnvironment_outer
    (trace : VacuousElimTrace input bubble raw)
    (sourceAmbient sourceLocals :
      ConcreteElaboration.WireContext trace.sourceDiagram)
    (targetAmbient targetLocals : ConcreteElaboration.WireContext input)
    (context : PromotedContextWitness trace
      (sourceAmbient ++ sourceLocals) (targetAmbient ++ targetLocals))
    (sourceNodup : (sourceAmbient ++ sourceLocals).Nodup)
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
  let sourceIndex := context.sourceIndex
    (rootOuterIndex targetAmbient targetLocals targetIndex)
  have sourceOuterMember : targetAmbient.get targetIndex ∈ sourceAmbient :=
    ambientSubset _ (List.get_mem _ _)
  let outerSourceIndex := Classical.choose
    (ConcreteElaboration.WireContext.lookup?_complete sourceOuterMember)
  have outerLookup := Classical.choose_spec
    (ConcreteElaboration.WireContext.lookup?_complete sourceOuterMember)
  let sourceRootIndex := rootOuterIndex sourceAmbient sourceLocals
    outerSourceIndex
  have sourceRootIndexEq : sourceRootIndex = sourceIndex :=
    ConcreteElaboration.WireContext.lookup?_unique sourceNodup
      (context.sourceIndex_lookup
        (rootOuterIndex targetAmbient targetLocals targetIndex)) (by
          calc
            _ = sourceAmbient.get outerSourceIndex := rootOuterIndex_get _ _ _
            _ = targetAmbient.get targetIndex :=
              ConcreteElaboration.WireContext.lookup?_sound outerLookup
            _ = _ := (rootOuterIndex_get _ _ _).symm)
  unfold PromotedContextWitness.targetEnvironment
  dsimp [sourceIndex] at sourceRootIndexEq
  rw [← sourceRootIndexEq, rootEnvironment_outer]
  exact outerAgreement outerSourceIndex targetIndex
    (ConcreteElaboration.WireContext.lookup?_sound outerLookup)

theorem rootSelectedTargetEnvironment_outer
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input)
    (context : PromotedContextWitness trace sourceContext targetContext)
    (sourceExact : sourceContext.Exact (trace.targetIndex wellFormed))
    (sourceEnvironment : Fin sourceContext.length → D)
    (index : Fin targetContext.length) :
    let selected := context.extendRootSelected trace wellFormed sourceContext
      targetContext sourceExact
    selected.targetEnvironment sourceEnvironment
        (extendedOuterIndex targetContext bubble index) =
      context.targetEnvironment sourceEnvironment index := by
  dsimp only
  let selected := context.extendRootSelected trace wellFormed sourceContext
    targetContext sourceExact
  have sameWire :
      (targetContext.extend bubble).get
          (extendedOuterIndex targetContext bubble index) =
        targetContext.get index := extendedOuterIndex_get _ _ _
  exact selected.targetEnvironment_eq_of_get context sourceExact.nodup
    sourceEnvironment _ _ sameWire

theorem rootSelectedSourceEnvironment_outer
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (sourceAmbient sourceLocals :
      ConcreteElaboration.WireContext trace.sourceDiagram)
    (targetAmbient targetLocals : ConcreteElaboration.WireContext input)
    (context : PromotedContextWitness trace
      (sourceAmbient ++ sourceLocals) (targetAmbient ++ targetLocals))
    (sourceExact :
      (sourceAmbient ++ sourceLocals).Exact (trace.targetIndex wellFormed))
    (targetSelectedNodup :
      ((targetAmbient ++ targetLocals).extend bubble).Nodup)
    (ambientSubset : ∀ wire, wire ∈ sourceAmbient → wire ∈ targetAmbient)
    (sourceOuter : Fin sourceAmbient.length → D)
    (targetOuter : Fin targetAmbient.length → D)
    (outerAgreement :
      (trace.wireIdentityRelation sourceAmbient targetAmbient).EnvironmentsAgree
        sourceOuter targetOuter)
    (targetLocal : Fin targetLocals.length → D)
    (bubbleLocal :
      Fin (ConcreteElaboration.exactScopeWires input bubble).length → D)
    (sourceIndex : Fin sourceAmbient.length) :
    let targetRootEnvironment :=
      ConcreteElaboration.rootEnvironment targetAmbient targetLocals
        targetOuter targetLocal
    let targetSelectedEnvironment :=
      ConcreteElaboration.extendedEnvironment
        (targetAmbient ++ targetLocals) bubble targetRootEnvironment bubbleLocal
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
    (sourceAmbient ++ sourceLocals) (targetAmbient ++ targetLocals) sourceExact
  have targetAmbientMember : sourceAmbient.get sourceIndex ∈ targetAmbient :=
    ambientSubset _ (List.get_mem _ _)
  let targetAmbientIndex := Classical.choose
    (ConcreteElaboration.WireContext.lookup?_complete targetAmbientMember)
  have targetAmbientLookup := Classical.choose_spec
    (ConcreteElaboration.WireContext.lookup?_complete targetAmbientMember)
  let targetRootIndex := rootOuterIndex targetAmbient targetLocals
    targetAmbientIndex
  let targetSelectedIndex := extendedOuterIndex
    (targetAmbient ++ targetLocals) bubble targetRootIndex
  let sourceRootIndex := rootOuterIndex sourceAmbient sourceLocals sourceIndex
  let sourceSubset := context.extendRootSelected_source_subset_target trace
    wellFormed (sourceAmbient ++ sourceLocals)
    (targetAmbient ++ targetLocals) sourceExact
  have corresponding :
      ((targetAmbient ++ targetLocals).extend bubble).get
          targetSelectedIndex =
        (sourceAmbient ++ sourceLocals).get sourceRootIndex := by
    calc
      _ = (targetAmbient ++ targetLocals).get targetRootIndex :=
        extendedOuterIndex_get _ _ _
      _ = targetAmbient.get targetAmbientIndex := rootOuterIndex_get _ _ _
      _ = sourceAmbient.get sourceIndex :=
        ConcreteElaboration.WireContext.lookup?_sound targetAmbientLookup
      _ = _ := (rootOuterIndex_get _ _ _).symm
  have targetSelectedIndexEq :
      targetSelectedIndex = selected.targetIndex sourceSubset sourceRootIndex :=
    ConcreteElaboration.WireContext.lookup?_unique targetSelectedNodup
      (selected.targetIndex_lookup sourceSubset sourceRootIndex) corresponding
  unfold PromotedContextWitness.sourceEnvironment
  rw [← targetSelectedIndexEq]
  simp [targetSelectedIndex, targetRootIndex]
  exact (outerAgreement sourceIndex targetAmbientIndex
    (ConcreteElaboration.WireContext.lookup?_sound
      targetAmbientLookup).symm).symm

theorem targetRoot_bubble_denote_iff
    (trace : VacuousElimTrace input bubble raw)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (targetContext : ConcreteElaboration.WireContext input)
    (keptItems : ItemSeq signature targetContext.length [])
    (selectedItems : ItemSeq signature
      (targetContext.extend bubble).length [trace.arity])
    (targetEnvironment : Fin targetContext.length → model.Carrier) :
    denoteItemSeq (relCtx := []) model named targetEnvironment ()
        (keptItems.append (.cons
          (.bubble trace.arity
            (ConcreteElaboration.finishRegion input targetContext bubble
              selectedItems)) .nil)) ↔
      denoteItemSeq (relCtx := []) model named targetEnvironment () keptItems ∧
        ∃ fresh : Relation model.Carrier trace.arity,
          ∃ bubbleLocal : Fin (ConcreteElaboration.exactScopeWires input
              bubble).length → model.Carrier,
            denoteItemSeq (relCtx := [trace.arity]) model named
              (ConcreteElaboration.extendedEnvironment targetContext bubble
                targetEnvironment bubbleLocal) (fresh, ()) selectedItems := by
  simp only [denoteItemSeq_append, denoteItemSeq_cons, denoteItemSeq_nil,
    and_true, bubble_denotes_exists]
  apply and_congr Iff.rfl
  apply exists_congr
  intro fresh
  exact finishRegion_denote_iff input targetContext bubble selectedItems
    model named targetEnvironment (fresh, ())

theorem focusedRootPartition_transport
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (sourceAmbient sourceLocals :
      ConcreteElaboration.WireContext trace.sourceDiagram)
    (targetAmbient targetLocals : ConcreteElaboration.WireContext input)
    (freshForward :
      (Fin (sourceAmbient ++ sourceLocals).length → model.Carrier) →
        RelEnv model.Carrier [] → Relation model.Carrier trace.arity)
    (context : PromotedContextWitness trace
      (sourceAmbient ++ sourceLocals) (targetAmbient ++ targetLocals))
    (sourceExact :
      (sourceAmbient ++ sourceLocals).Exact (trace.targetIndex wellFormed))
    (targetSelectedNodup :
      ((targetAmbient ++ targetLocals).extend bubble).Nodup)
    (targetAmbientSubset :
      ∀ wire, wire ∈ targetAmbient → wire ∈ sourceAmbient)
    (sourceAmbientSubset :
      ∀ wire, wire ∈ sourceAmbient → wire ∈ targetAmbient)
    (relationMap : RelationRenaming [] [trace.arity])
    (sourceKept sourceSelected : ItemSeq signature
      (sourceAmbient ++ sourceLocals).length [])
    (targetKept : ItemSeq signature
      (targetAmbient ++ targetLocals).length [])
    (targetSelected : ItemSeq signature
      ((targetAmbient ++ targetLocals).extend bubble).length [trace.arity])
    (keptSimulation : ConcreteElaboration.ItemSeqSimulation model named
      direction context.indexRelation sourceKept targetKept)
    (selectedSimulation : ConcreteElaboration.ItemSeqSimulation model named
      direction
        (context.extendRootSelected trace wellFormed
          (sourceAmbient ++ sourceLocals) (targetAmbient ++ targetLocals)
          sourceExact).indexRelation
        (sourceSelected.renameRelations relationMap) targetSelected) :
    ConcreteElaboration.DirectionalRootTransport direction
      sourceAmbient sourceLocals targetAmbient targetLocals
      (trace.wireIdentityRelation sourceAmbient targetAmbient)
      model named (sourceKept.append sourceSelected)
      (targetKept.append (.cons
        (.bubble trace.arity
          (ConcreteElaboration.finishRegion input
            (targetAmbient ++ targetLocals) bubble targetSelected))
        .nil)) := by
  intro sourceOuter targetOuter relations outerAgreement
  let selected := context.extendRootSelected trace wellFormed
    (sourceAmbient ++ sourceLocals) (targetAmbient ++ targetLocals)
    sourceExact
  have relationAgreement (fresh : Relation model.Carrier trace.arity) :
      RelEnv.Agrees relationMap () (fresh, ()) := by
    intro binderArity relation
    exact Fin.elim0 relation.index
  cases direction with
  | forward =>
      intro sourceLocal sourceDenotation
      obtain ⟨sourceKeptDenotation, sourceSelectedDenotation⟩ :=
        (denoteItemSeq_append model named
          (ConcreteElaboration.rootEnvironment sourceAmbient sourceLocals
            sourceOuter sourceLocal) relations sourceKept sourceSelected).mp
          sourceDenotation
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
        targetRootPulled () contextAgreement sourceKeptDenotation
      let targetSelectedPulled := selected.targetEnvironment sourceEnvironment
      let bubbleLocal := localEnvironmentPart
        (targetAmbient ++ targetLocals) bubble targetSelectedPulled
      have targetSelectedEq :
          ConcreteElaboration.extendedEnvironment
              (targetAmbient ++ targetLocals) bubble targetRootPulled
              bubbleLocal = targetSelectedPulled := by
        apply extendedEnvironment_of_parts
        intro index
        exact trace.rootSelectedTargetEnvironment_outer wellFormed
          (sourceAmbient ++ sourceLocals) (targetAmbient ++ targetLocals)
          context sourceExact sourceEnvironment index
      have selectedAgreement : selected.indexRelation.EnvironmentsAgree
          sourceEnvironment targetSelectedPulled :=
        selected.targetEnvironment_agrees sourceExact.nodup sourceEnvironment
      let fresh : Relation model.Carrier trace.arity :=
        freshForward sourceEnvironment ()
      have sourceSelectedRenamed :
          denoteItemSeq (relCtx := [trace.arity]) model named sourceEnvironment
            (fresh, ()) (sourceSelected.renameRelations relationMap) :=
        (denoteItemSeq_renameRelations model named relationMap () (fresh, ())
          (relationAgreement fresh) sourceEnvironment sourceSelected).mpr
          sourceSelectedDenotation
      have targetSelectedDenotation := selectedSimulation sourceEnvironment
        targetSelectedPulled (fresh, ()) selectedAgreement
        sourceSelectedRenamed
      refine ⟨targetLocal, ?_⟩
      apply (trace.targetRoot_bubble_denote_iff model named
        (targetAmbient ++ targetLocals) targetKept targetSelected
        (ConcreteElaboration.rootEnvironment targetAmbient targetLocals
          targetOuter targetLocal)).mpr
      refine ⟨?_, fresh, bubbleLocal, ?_⟩
      · rw [targetRootEq]
        exact targetKeptDenotation
      · rw [targetRootEq, targetSelectedEq]
        exact targetSelectedDenotation
  | backward =>
      intro targetLocal targetDenotation
      let targetRootEnvironment :=
        ConcreteElaboration.rootEnvironment targetAmbient targetLocals
          targetOuter targetLocal
      obtain ⟨targetKeptDenotation, fresh, bubbleLocal,
          targetSelectedDenotation⟩ :=
        (trace.targetRoot_bubble_denote_iff model named
          (targetAmbient ++ targetLocals) targetKept targetSelected
          targetRootEnvironment).mp targetDenotation
      let targetSelectedEnvironment :=
        ConcreteElaboration.extendedEnvironment
          (targetAmbient ++ targetLocals) bubble targetRootEnvironment
          bubbleLocal
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
          targetOuter outerAgreement targetLocal bubbleLocal sourceIndex
      have selectedAgreement : selected.indexRelation.EnvironmentsAgree
          sourceEnvironment targetSelectedEnvironment :=
        selected.sourceEnvironment_agrees sourceSubset targetSelectedNodup
          targetSelectedEnvironment
      have sourceSelectedRenamed := selectedSimulation sourceEnvironment
        targetSelectedEnvironment (fresh, ()) selectedAgreement
        targetSelectedDenotation
      have sourceSelectedDenotation :
          denoteItemSeq (relCtx := []) model named sourceEnvironment ()
            sourceSelected :=
        (denoteItemSeq_renameRelations model named relationMap () (fresh, ())
          (relationAgreement fresh) sourceEnvironment sourceSelected).mp
          sourceSelectedRenamed
      have contextAgreement : context.indexRelation.EnvironmentsAgree
          sourceEnvironment targetRootEnvironment := by
        intro sourceIndex targetIndex related
        let targetSelectedIndex := extendedOuterIndex
          (targetAmbient ++ targetLocals) bubble targetIndex
        have selectedRelated : selected.indexRelation.Rel sourceIndex
            targetSelectedIndex := related.trans
          (extendedOuterIndex_get _ _ _).symm
        have agreement := selectedAgreement sourceIndex targetSelectedIndex
          selectedRelated
        simpa [targetSelectedEnvironment, targetSelectedIndex] using agreement
      have sourceKeptDenotation := keptSimulation sourceEnvironment
        targetRootEnvironment () contextAgreement targetKeptDenotation
      refine ⟨sourceLocal, ?_⟩
      apply (denoteItemSeq_append (relCtx := []) model named
        (ConcreteElaboration.rootEnvironment sourceAmbient sourceLocals
          sourceOuter sourceLocal) () sourceKept sourceSelected).mpr
      rw [sourceEnvironmentEq]
      exact ⟨sourceKeptDenotation, sourceSelectedDenotation⟩

end VisualProof.Rule.VacuousElimTrace
