import VisualProof.Rule.Soundness.Comprehension.AbstractionOccurrenceCompiler

namespace VisualProof.Concrete


open VisualProof.Concrete

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace AbstractionRawTrace

/-- Under the fixed comprehension interpretation, every certified selected
block entails its corresponding fresh atom, simultaneously and in executor
order. -/
theorem occurrenceFamily_forward
    {input : Concrete.Checked }
    {wrap : CheckedSelection input.val}
    {comprehension : Concrete.CheckedOpen }
    {occurrences : List (OperationAbstractionOccurrence input)}
    {raw : Concrete.Diagram}
    {sourceRels targetRels : RelCtx}
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : OperationComprehensionAbstractPayload input wrap comprehension occurrences)
    (model : Model)
    (hostFuel : Nat)
    (region : Fin input.val.regionCount)
    (indices : List (Fin occurrences.length))
    (anchored : ∀ index, index ∈ indices →
      (occurrences.get index).selection.val.anchor = region)
    (sourceContext : Concrete.Elaboration.WireContext input.val)
    (targetContext : Concrete.Elaboration.WireContext trace.diagram)
    (context : ContextWitness trace sourceContext targetContext)
    (sourceBinders : Concrete.Elaboration.BinderContext input.val sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext trace.diagram targetRels)
    (sourceCover : sourceBinders.Covers region)
    (sourceEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      input.val sourceBinders region)
    (sourceExact : sourceContext.Exact region)
    (sourceItems : Fin occurrences.length →
      ItemSeq  sourceContext.length sourceRels)
    (targetItems : Fin occurrences.length →
      Item  targetContext.length targetRels)
    (sourceCompiled : ∀ index, index ∈ indices →
      Concrete.Elaboration.compileOccurrencesWith?  input.val
        (Concrete.Elaboration.compileRegion?  input.val hostFuel)
        sourceContext sourceBinders
        (VisualProof.Rule.ModalSoundness.selectedOccurrences input.val
          (occurrences.get index).selection) = some (sourceItems index))
    (targetCompiled : ∀ index, index ∈ indices →
      Concrete.Elaboration.compileNode?  trace.diagram targetContext
        targetBinders (trace.targetAtom index) = some (targetItems index))
    (sourceEnvironment : Fin sourceContext.length → model.Carrier)
    (targetEnvironment : Fin targetContext.length → model.Carrier)
    (sourceRelations : RelEnv model.Carrier sourceRels)
    (targetRelations : RelEnv model.Carrier targetRels)
    (fixed : @FixedRelationWitness targetRels  input wrap
      comprehension occurrences raw trace model  targetBinders
        targetRelations)
    (environments : context.indexRelation.EnvironmentsAgree sourceEnvironment
      targetEnvironment)
    (sourceDenotes : denoteItemSeq model  sourceEnvironment sourceRelations
      (occurrenceFamilyItems sourceItems indices)) :
    denoteItemSeq model  targetEnvironment targetRelations
      (occurrenceFamilyAtomItems targetItems indices) := by
  apply (occurrenceFamilyAtomItems_denote_iff indices targetItems model
    targetEnvironment targetRelations).2
  have sourceBlocks := (occurrenceFamilyItems_denote_iff indices sourceItems
    model  sourceEnvironment sourceRelations).1 sourceDenotes
  intro index member
  have anchor := anchored index member
  have exactAt : sourceContext.Exact
      (occurrences.get index).selection.val.anchor := by
    rw [anchor]
    exact sourceExact
  have coverAt : sourceBinders.Covers
      (occurrences.get index).selection.val.anchor := by
    rw [anchor]
    exact sourceCover
  have enumerationAt : Concrete.Elaboration.BinderContext.Enumeration input.val
      sourceBinders (occurrences.get index).selection.val.anchor := by
    rw [anchor]
    exact sourceEnumeration
  have relationDenotes := selectedOccurrence_denote_relation input
    (occurrences.get index) (payload.witnesses index) model  hostFuel
    sourceContext sourceBinders enumerationAt coverAt exactAt
    (sourceItems index) (sourceCompiled index member) sourceEnvironment
    sourceRelations (by
      exact (VisualProof.Rule.IterationSoundness.denoteRegion_mk_zero_iff model  sourceEnvironment
        sourceRelations (sourceItems index)).2 (sourceBlocks index member))
  exact (trace.compiledTargetAtom_denote_iff_fixed payload index model
    sourceContext targetContext context exactAt sourceEnvironment
    targetEnvironment environments targetBinders targetRelations fixed
    (targetItems index) (targetCompiled index member)).2 relationDenotes

/-- Conversely, true fixed-relation atoms choose all deleted internal-wire
valuations simultaneously.  The resulting source valuation still agrees with
the target on every surviving wire and makes every selected block true. -/
theorem occurrenceFamily_backward
    {input : Concrete.Checked }
    {wrap : CheckedSelection input.val}
    {comprehension : Concrete.CheckedOpen }
    {occurrences : List (OperationAbstractionOccurrence input)}
    {raw : Concrete.Diagram}
    {sourceRels targetRels : RelCtx}
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : OperationComprehensionAbstractPayload input wrap comprehension occurrences)
    (model : Model)
    (hostFuel : Nat)
    (region : Fin input.val.regionCount)
    (indices : List (Fin occurrences.length))
    (anchored : ∀ index, index ∈ indices →
      (occurrences.get index).selection.val.anchor = region)
    (sourceContext : Concrete.Elaboration.WireContext input.val)
    (targetContext : Concrete.Elaboration.WireContext trace.diagram)
    (context : ContextWitness trace sourceContext targetContext)
    (sourceBinders : Concrete.Elaboration.BinderContext input.val sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext trace.diagram targetRels)
    (sourceCover : sourceBinders.Covers region)
    (sourceEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      input.val sourceBinders region)
    (sourceExact : sourceContext.Exact region)
    (sourceItems : Fin occurrences.length →
      ItemSeq  sourceContext.length sourceRels)
    (targetItems : Fin occurrences.length →
      Item  targetContext.length targetRels)
    (sourceCompiled : ∀ index, index ∈ indices →
      Concrete.Elaboration.compileOccurrencesWith?  input.val
        (Concrete.Elaboration.compileRegion?  input.val hostFuel)
        sourceContext sourceBinders
        (VisualProof.Rule.ModalSoundness.selectedOccurrences input.val
          (occurrences.get index).selection) = some (sourceItems index))
    (targetCompiled : ∀ index, index ∈ indices →
      Concrete.Elaboration.compileNode?  trace.diagram targetContext
        targetBinders (trace.targetAtom index) = some (targetItems index))
    (fallback : Fin sourceContext.length → model.Carrier)
    (targetEnvironment : Fin targetContext.length → model.Carrier)
    (sourceRelations : RelEnv model.Carrier sourceRels)
    (targetRelations : RelEnv model.Carrier targetRels)
    (fixed : @FixedRelationWitness targetRels  input wrap
      comprehension occurrences raw trace model  targetBinders
        targetRelations)
    (environments : context.indexRelation.EnvironmentsAgree fallback
      targetEnvironment)
    (targetDenotes : denoteItemSeq model  targetEnvironment targetRelations
      (occurrenceFamilyAtomItems targetItems indices)) :
    ∃ sourceEnvironment : Fin sourceContext.length → model.Carrier,
      context.indexRelation.EnvironmentsAgree sourceEnvironment
          targetEnvironment ∧
        denoteItemSeq model  sourceEnvironment sourceRelations
          (occurrenceFamilyItems sourceItems indices) ∧
        (∀ hostIndex, (∀ index, index ∈ indices →
            sourceContext.get hostIndex ∉
              (occurrences.get index).selection.internalWires) →
          sourceEnvironment hostIndex = fallback hostIndex) := by
  classical
  have targetAtoms := (occurrenceFamilyAtomItems_denote_iff indices targetItems
    model  targetEnvironment targetRelations).1 targetDenotes
  have realized : ∀ index, index ∈ indices →
      ∃ environment : Fin sourceContext.length → model.Carrier,
        (∀ hostIndex, sourceContext.get hostIndex ∉
            (occurrences.get index).selection.internalWires →
          environment hostIndex = fallback hostIndex) ∧
        denoteItemSeq model  environment sourceRelations
          (sourceItems index) := by
    intro index member
    have anchor := anchored index member
    have exactAt : sourceContext.Exact
        (occurrences.get index).selection.val.anchor := by
      rw [anchor]
      exact sourceExact
    have coverAt : sourceBinders.Covers
        (occurrences.get index).selection.val.anchor := by
      rw [anchor]
      exact sourceCover
    have enumerationAt : Concrete.Elaboration.BinderContext.Enumeration
        input.val sourceBinders
          (occurrences.get index).selection.val.anchor := by
      rw [anchor]
      exact sourceEnumeration
    have relationDenotes :=
      (trace.compiledTargetAtom_denote_iff_fixed payload index model
        sourceContext targetContext context exactAt fallback targetEnvironment
        environments targetBinders targetRelations fixed (targetItems index)
        (targetCompiled index member)).1 (targetAtoms index member)
    exact relation_selectedOccurrence_environment input comprehension
      (occurrences.get index) (payload.witnesses index) model  hostFuel
      sourceContext sourceBinders enumerationAt coverAt exactAt
      (sourceItems index) (sourceCompiled index member) fallback sourceRelations
      relationDenotes
  let values : ∀ index : Fin occurrences.length,
      Fin sourceContext.length → model.Carrier := fun index =>
    if member : index ∈ indices then Classical.choose (realized index member)
    else fallback
  have preserves : ∀ index hostIndex,
      sourceContext.get hostIndex ∉
          (occurrences.get index).selection.internalWires →
        values index hostIndex = fallback hostIndex := by
    intro index hostIndex outside
    dsimp only [values]
    split
    · rename_i member
      exact (Classical.choose_spec (realized index member)).1 hostIndex outside
    · rfl
  let sourceEnvironment := occurrenceFamilyEnvironment input occurrences
    indices sourceContext values fallback
  have agreement : context.indexRelation.EnvironmentsAgree sourceEnvironment
      targetEnvironment := by
    exact trace.occurrenceFamilyEnvironment_agrees payload indices sourceContext
      targetContext context values fallback targetEnvironment environments
  refine ⟨sourceEnvironment, agreement, ?_, ?_⟩
  · apply (occurrenceFamilyItems_denote_iff indices sourceItems model
      sourceEnvironment sourceRelations).2
    intro index member
    have valueDenotes : denoteItemSeq model  (values index) sourceRelations
        (sourceItems index) := by
      dsimp only [values]
      rw [dif_pos member]
      exact (Classical.choose_spec (realized index member)).2
    apply (selectedOccurrence_denote_congr input (occurrences.get index)
      (payload.witnesses index) model  hostFuel sourceContext sourceBinders
      (by
        rw [anchored index member]
        exact sourceEnumeration)
      (by
        rw [anchored index member]
        exact sourceCover)
      (by
        rw [anchored index member]
        exact sourceExact)
      (sourceItems index) (sourceCompiled index member) (values index)
      sourceEnvironment sourceRelations ?_).1 valueDenotes
    intro hostIndex represented
    symm
    exact occurrenceFamilyEnvironment_eq_value_on_closure payload indices
      sourceContext values fallback preserves index member hostIndex represented
  · intro hostIndex outside
    exact occurrenceFamilyEnvironment_eq_fallback input occurrences indices
      sourceContext values fallback hostIndex outside

end AbstractionRawTrace

end VisualProof.Concrete
