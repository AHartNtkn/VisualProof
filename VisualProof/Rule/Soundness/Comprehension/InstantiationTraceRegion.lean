import VisualProof.Rule.Soundness.Comprehension.InstantiationTraceFixed
import VisualProof.Rule.Soundness.AttachmentAliasSemantic
import VisualProof.Rule.Soundness.Comprehension.InstantiationAttachmentSemantic

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- Every accepted executor step carries the complete fixed-relation region
simulation for every region enclosed by the moving quantified bubble. -/
def RegionSimulationsEveryStep
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {origin : CheckedDiagram signature}
    {fuel : Nat}
    {state result : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount}
    (trace : InstantiationTrace comprehension attachments binders payload fuel
      state result)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (relationValue : Relation model.Carrier payload.arity)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (parameterValues : Fin attachments.length → model.Carrier) : Prop :=
  match trace with
  | .done _ _ _ => True
  | .step _ state _ atom tail site _ arguments plan _ _ _ _ rest =>
      let hadmissible :=
        (Splice.Input.checkInput_sound plan.checkedInputChecked).2
      (∀ direction sourceFuel targetFuel
        (region : Fin state.diagram.val.regionCount),
        state.diagram.val.Encloses state.bubble region →
        FixedAdvanceRegionSimulation plan.materialization.result attachments
          binders plan.operationalPayload state atom tail site arguments
          hadmissible model named relationValue values parameterValues direction
          sourceFuel targetFuel region) ∧
      RegionSimulationsEveryStep rest model named relationValue values
        parameterValues

/-- The executor trace, shape ledger, target ledger, and fixed trace relation
jointly discharge every hypothesis of the one-step recursive simulation. -/
theorem regionSimulationsEveryStep_of
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {origin : CheckedDiagram signature}
    {fuel : Nat}
    {state result : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount}
    (trace : InstantiationTrace comprehension attachments binders payload fuel
      state result)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (relationValue : Relation model.Carrier payload.arity)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (parameterValues : Fin attachments.length → model.Carrier)
    (invariants : StepInvariantsEveryStep trace)
    (targets : BinderTargetsEveryStep trace)
    (relations : RelationContractsEveryStep trace model named relationValue
      values parameterValues) :
    RegionSimulationsEveryStep trace model named relationValue values
      parameterValues := by
  induction trace with
  | done => trivial
  | step fuel state result atom tail site candidate arguments plan
      pending_eq node_eq candidate_eq arguments_eq rest ih =>
      rcases invariants with ⟨invariant, restInvariants⟩
      rcases targets with ⟨targets, restTargets⟩
      rcases relations with ⟨nonemptyRelationEq, emptyRelationEq,
        restRelations⟩
      let hadmissible :=
        (Splice.Input.checkInput_sound plan.checkedInputChecked).2
      have operationalTargets : BinderTargetsAtBubble plan.operationalPayload
          state := by
        constructor
        · intro index
          simpa [InstantiationCopyPlan.operationalPayload,
            materializedInstantiationPayload,
            Splice.AttachmentAliasMaterialization.Certificate.spine,
            Splice.AttachmentAliasMaterialization.binderSpine] using
            targets.target_shape index
        · intro index
          exact targets.target_encloses index
        · intro index
          exact targets.target_ne index
      have operationalEmptyRelationEq :
          ∀ _hzero : plan.operationalPayload.binderSpine.proxyCount = 0,
            relationValue = plan.operationalPayload.interpretedRelation model
              named parameterValues := by
        intro hzero
        have sourceEq := emptyRelationEq (by
          simpa [InstantiationCopyPlan.operationalPayload,
            materializedInstantiationPayload,
            Splice.AttachmentAliasMaterialization.Certificate.spine,
            Splice.AttachmentAliasMaterialization.binderSpine] using hzero)
        apply sourceEq.trans
        funext relationArguments
        apply propext
        exact (plan.materialization.denote_iff model named
          (Fin.addCases relationArguments parameterValues ∘
            Fin.cast payload.boundarySplit)).symm
      refine ⟨?_, ih restInvariants restTargets restRelations⟩
      intro direction sourceFuel targetFuel region enclosed
      apply advance_enclosed_region_simulation_fixed plan.materialization.result
        attachments binders plan.operationalPayload state atom tail site
        arguments
      · simpa [candidate_eq] using node_eq
      · exact arguments_eq
      · exact pending_eq
      · exact invariant.ownedNodup
      · exact invariant.shape
      · exact operationalTargets
      · intro hnonempty
        have sourceNonempty : payload.binderSpine.proxyCount ≠ 0 := by
          simpa [InstantiationCopyPlan.operationalPayload,
            materializedInstantiationPayload,
            Splice.AttachmentAliasMaterialization.Certificate.spine,
            Splice.AttachmentAliasMaterialization.binderSpine] using hnonempty
        apply (nonemptyRelationEq sourceNonempty).trans
        exact terminalRelationOfParameterValues_materialized payload state site
          arguments plan.materialization sourceNonempty model named parameterValues
          values
      · exact operationalEmptyRelationEq
      · exact enclosed

theorem initial_regionSimulationsEveryStep
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (trace : InstantiationTrace comprehension attachments binders payload fuel
      (initialInstantiationState payload) result)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (relationValue : Relation model.Carrier payload.arity)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (parameterValues : Fin attachments.length → model.Carrier)
    (contract : TraceRelationContract payload input model named relationValue
      values parameterValues) :
    RegionSimulationsEveryStep trace model named relationValue values
      parameterValues := by
  exact regionSimulationsEveryStep_of trace model named relationValue values
    parameterValues (initial_stepInvariantsEveryStep trace)
    (initial_binderTargetsEveryStep trace)
    (contract.everyStep trace model named relationValue values parameterValues)

end InstantiationSemantic

end VisualProof.Rule
