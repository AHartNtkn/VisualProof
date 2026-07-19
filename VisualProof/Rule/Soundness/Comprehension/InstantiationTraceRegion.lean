import VisualProof.Rule.Soundness.Comprehension.InstantiationTraceFixed

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
  | .step _ state _ atom tail site _ arguments _ _ _ _ _ input_eq rest =>
      let hadmissible := (Splice.Input.checkInput_sound input_eq).2
      (∀ direction sourceFuel targetFuel
        (region : Fin state.diagram.val.regionCount),
        state.diagram.val.Encloses state.bubble region →
        FixedAdvanceRegionSimulation comprehension attachments binders payload
          state atom tail site arguments hadmissible model named relationValue
          values parameterValues direction sourceFuel targetFuel region) ∧
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
  | step fuel state result atom tail site candidate arguments checkedInput
      pending_eq node_eq candidate_eq arguments_eq input_eq rest ih =>
      rcases invariants with ⟨invariant, restInvariants⟩
      rcases targets with ⟨stepTargets, restTargets⟩
      rcases relations with
        ⟨nonemptyRelationEq, emptyRelationEq, restRelations⟩
      let hadmissible := (Splice.Input.checkInput_sound input_eq).2
      have node_eq' : state.diagram.val.nodes atom =
          .atom site state.bubble := by
        simpa [candidate_eq] using node_eq
      refine ⟨?_, ih restInvariants restTargets restRelations⟩
      exact advance_enclosed_region_simulation_fixed comprehension attachments
        binders payload state atom tail site arguments node_eq' arguments_eq
        pending_eq invariant.ownedNodup invariant.shape stepTargets hadmissible
        model named relationValue values parameterValues nonemptyRelationEq
        emptyRelationEq

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
