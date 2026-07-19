import VisualProof.Rule.Soundness.Comprehension.InstantiationCoalescedEnvironment

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- Truth of the trace's fixed comprehension relation exposes its ordered
boundary assignment in both the zero- and nonzero-proxy-spine cases. -/
theorem relation_boundaryAssignment_of_truth
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (relationValue : Relation model.Carrier payload.arity)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (parameterValues : Fin attachments.length → model.Carrier)
    (nonemptyRelationEq : ∀ hnonempty :
      payload.binderSpine.proxyCount ≠ 0,
      relationValue = terminalRelationOfParameterValues payload state site
        arguments hnonempty model named parameterValues values)
    (emptyRelationEq : ∀ _hzero : payload.binderSpine.proxyCount = 0,
      relationValue = payload.interpretedRelation model named parameterValues)
    (relationArguments : Fin payload.arity → model.Carrier)
    (truth : relationValue relationArguments) :
    ∃ assignment : BoundaryAssignment comprehension.elaborate model.Carrier,
      assignment.args =
        Fin.addCases relationArguments parameterValues ∘
          Fin.cast payload.boundarySplit := by
  by_cases hzero : payload.binderSpine.proxyCount = 0
  · have interpreted : payload.interpretedRelation model named parameterValues
        relationArguments := by
      rw [← emptyRelationEq hzero]
      exact truth
    have patternDenotes :=
      (payload.interpretedRelation_apply model named parameterValues
        relationArguments).mp interpreted
    exact ⟨patternDenotes.choose, patternDenotes.choose_spec.1⟩
  · have terminal : terminalRelationOfParameterValues payload state site
        arguments hzero model named parameterValues values relationArguments := by
      rw [← nonemptyRelationEq hzero]
      exact truth
    exact ⟨terminal.choose, terminal.choose_spec.1⟩

/-- The active fixed-relation atom therefore certifies every identification
made by the executor's attachment quotient. -/
theorem relation_truth_quotientWire_value_eq
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (wireValue : Fin state.diagram.val.wireCount → model.Carrier)
    (relationValue : Relation model.Carrier payload.arity)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (parameterValues : Fin attachments.length → model.Carrier)
    (parameters : wireValue ∘ state.parameters = parameterValues)
    (nonemptyRelationEq : ∀ hnonempty :
      payload.binderSpine.proxyCount ≠ 0,
      relationValue = terminalRelationOfParameterValues payload state site
        arguments hnonempty model named parameterValues values)
    (emptyRelationEq : ∀ _hzero : payload.binderSpine.proxyCount = 0,
      relationValue = payload.interpretedRelation model named parameterValues)
    (truth : relationValue (wireValue ∘ arguments))
    {left right : Fin state.diagram.val.wireCount}
    (sameClass :
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).quotientWire left =
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).quotientWire right) :
    wireValue left = wireValue right := by
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  obtain ⟨assignment, assignmentArgs⟩ :=
    relation_boundaryAssignment_of_truth payload state site arguments model
      named relationValue values parameterValues nonemptyRelationEq
      emptyRelationEq (wireValue ∘ arguments) truth
  apply quotientWire_value_eq_of_boundaryAssignment spliceInput wireValue
    assignment
  · intro position
    rw [assignmentArgs]
    let split := Fin.cast payload.boundarySplit position
    have recover : Fin.cast payload.boundarySplit.symm split = position := by
      apply Fin.ext
      rfl
    rw [← recover]
    refine Fin.addCases (fun argument => ?_) (fun parameter => ?_) split
    · simp [spliceInput, instantiateSpliceInput, Function.comp_def]
    · simpa [spliceInput, instantiateSpliceInput, Function.comp_def] using
        congrFun parameters parameter
  · exact sameClass

end InstantiationSemantic

end VisualProof.Rule
