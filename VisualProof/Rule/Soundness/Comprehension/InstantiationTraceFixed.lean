import VisualProof.Rule.Soundness.Comprehension.InstantiationTraceInvariant
import VisualProof.Rule.Soundness.Comprehension.InstantiationTargetInvariant

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- One relation witness, one proxy family, and one ordered parameter
valuation determine the relation used at every accepted copy site.  The two
equalities are conditional on the executor's actual binder-spine case. -/
structure TraceRelationContract
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    (origin : CheckedDiagram signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (relationValue : Relation model.Carrier payload.arity)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (parameterValues : Fin attachments.length → model.Carrier) : Prop where
  nonempty : ∀
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (hnonempty : payload.binderSpine.proxyCount ≠ 0),
    relationValue = terminalRelationOfParameterValues payload state site
      arguments hnonempty model named parameterValues values
  empty : ∀ _hzero : payload.binderSpine.proxyCount = 0,
    relationValue = payload.interpretedRelation model named parameterValues

/-- A nonzero-spine relation selected at any one occurrence is the canonical
trace relation at every occurrence. -/
theorem TraceRelationContract.of_nonempty
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    (origin : CheckedDiagram signature)
    (reference : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (referenceSite : Fin reference.diagram.val.regionCount)
    (referenceArguments : Fin payload.arity →
      Fin reference.diagram.val.wireCount)
    (hnonempty : payload.binderSpine.proxyCount ≠ 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (relationValue : Relation model.Carrier payload.arity)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (parameterValues : Fin attachments.length → model.Carrier)
    (referenceEq : relationValue = terminalRelationOfParameterValues payload
      reference referenceSite referenceArguments hnonempty model named
      parameterValues values) :
    TraceRelationContract payload origin model named relationValue values
      parameterValues := by
  constructor
  · intro state site arguments hnonempty'
    have proofEq : hnonempty' = hnonempty := Subsingleton.elim _ _
    subst hnonempty'
    exact referenceEq.trans
      (terminalRelationOfParameterValues_eq payload reference state
        referenceSite site referenceArguments arguments hnonempty model named
        parameterValues values)
  · intro hzero
    exact False.elim (hnonempty hzero)

/-- In the zero-spine case the interpreted open comprehension is already the
single trace relation; all nonzero obligations are vacuous. -/
theorem TraceRelationContract.of_empty
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    (origin : CheckedDiagram signature)
    (hzero : payload.binderSpine.proxyCount = 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (relationValue : Relation model.Carrier payload.arity)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (parameterValues : Fin attachments.length → model.Carrier)
    (relationEq : relationValue =
      payload.interpretedRelation model named parameterValues) :
    TraceRelationContract payload origin model named relationValue values
      parameterValues := by
  constructor
  · intro _state _site _arguments hnonempty
    exact False.elim (hnonempty hzero)
  · intro _
    exact relationEq

/-- The fixed-relation premises consumed by every one-step region simulation
are available uniformly along an accepted executor trace. -/
def RelationContractsEveryStep
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
  | .step _ state _ _ _ site _ arguments _ _ _ _ _ rest =>
      (∀ hnonempty : payload.binderSpine.proxyCount ≠ 0,
        relationValue = terminalRelationOfParameterValues payload state site
          arguments hnonempty model named parameterValues values) ∧
      (∀ _hzero : payload.binderSpine.proxyCount = 0,
        relationValue = payload.interpretedRelation model named
          parameterValues) ∧
      RelationContractsEveryStep rest model named relationValue values
        parameterValues

theorem TraceRelationContract.everyStep
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
    (contract : TraceRelationContract payload origin model named relationValue
      values parameterValues) :
    RelationContractsEveryStep trace model named relationValue values
      parameterValues := by
  induction trace with
  | done => trivial
  | step fuel state result atom tail site candidate arguments plan
      pending_eq node_eq candidate_eq arguments_eq rest ih =>
      exact ⟨contract.nonempty state site arguments,
        contract.empty, ih⟩

end InstantiationSemantic

end VisualProof.Rule
