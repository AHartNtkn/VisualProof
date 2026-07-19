import VisualProof.Rule.Soundness.Comprehension.InstantiationTerminalTrace

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram

namespace InstantiationSemantic

/-- Canonical nonzero-spine comprehension relation determined by the ordered
parameter valuation and fixed proxy family, with no arbitrary total wire
valuation in its interface. -/
noncomputable def terminalRelationOfParameterValues
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
    (hnonempty : payload.binderSpine.proxyCount ≠ 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (parameterValues : Fin attachments.length → model.Carrier)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index)) :
    Relation model.Carrier payload.arity :=
  fun relationArguments =>
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
    ∃ assignment : BoundaryAssignment comprehension.elaborate model.Carrier,
      assignment.args =
          Fin.addCases relationArguments parameterValues ∘
            Fin.cast payload.boundarySplit ∧
        ∃ relEnv : RelEnv model.Carrier pattern.witness.toFocus.holeRels,
          TerminalRelationsMatch payload state site arguments hnonempty values
              relEnv ∧
            denoteRegion model named
              (terminalInheritedEnvironment payload state site arguments
                hnonempty assignment)
              relEnv
              (ConcreteElaboration.finishRegion comprehension.val.diagram
                pattern.leaf.inheritedWires payload.binderSpine.bodyContainer
                pattern.leaf.items)

theorem terminalRelationOfValues_eq_parameterValues
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
    (hnonempty : payload.binderSpine.proxyCount ≠ 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (wireValue : Fin state.diagram.val.wireCount → model.Carrier)
    (parameterValues : Fin attachments.length → model.Carrier)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (parameters : wireValue ∘ state.parameters = parameterValues) :
    terminalRelationOfValues payload state site arguments hnonempty model named
        wireValue values =
      terminalRelationOfParameterValues payload state site arguments hnonempty
        model named parameterValues values := by
  funext relationArguments
  apply propext
  simp only [terminalRelationOfValues, terminalRelationOfParameterValues]
  rw [parameters]

/-- One ordered valuation for the executor's parameter wires in a concrete
compiler context.  Repeated parameter wires deliberately read the same
context entry while retaining their serialized positions. -/
def ParameterValuesAt
    (state : InstantiationState origin parameterCount proxyCount)
    (context : ConcreteElaboration.WireContext state.diagram.val)
    (environment : Fin context.length → D)
    (values : Fin parameterCount → D) : Prop :=
  ∀ position, ∃ index : Fin context.length,
    context.get index = state.parameters position ∧
      environment index = values position

/-- Extending a compiler context below the moving bubble preserves every
inherited parameter value. -/
theorem ParameterValuesAt.extend
    (state : InstantiationState origin parameterCount proxyCount)
    (context : ConcreteElaboration.WireContext state.diagram.val)
    (environment : Fin context.length → D)
    (values : Fin parameterCount → D)
    (fixed : ParameterValuesAt state context environment values)
    (region : Fin state.diagram.val.regionCount)
    (localEnv : Fin (ConcreteElaboration.exactScopeWires state.diagram.val
      region).length → D) :
    ParameterValuesAt state (context.extend region)
      (ConcreteElaboration.extendedEnvironment context region environment localEnv)
      values := by
  intro position
  obtain ⟨index, wireEq, valueEq⟩ := fixed position
  let extendedIndex : Fin (context.extend region).length :=
    Fin.cast (ConcreteElaboration.WireContext.length_extend context region).symm
      (Fin.castAdd
        (ConcreteElaboration.exactScopeWires state.diagram.val region).length
        index)
  refine ⟨extendedIndex, ?_, ?_⟩
  · simpa [extendedIndex] using
      (Splice.Input.PlugLayout.ConcreteElaboration.WireContext.extend_get_outer
        context region index).trans wireEq
  · simpa [ConcreteElaboration.extendedEnvironment, extendedIndex,
      extendWireEnv] using valueEq

/-- At an accepted splice site, the quotient-host valuation reads each source
parameter at the fixed value carried by the next state's exact target context. -/
theorem siteQuotientEnvironment_parameter
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpenDiagram signature)
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (atom : Fin state.diagram.val.nodeCount)
    (tail : List (Fin state.diagram.val.nodeCount))
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (context : ConcreteElaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw)
    (exact : context.Exact
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site))
    (environment : Fin context.length → D)
    (parameterValues : Fin attachments.length → D)
    (fixed : ParameterValuesAt
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible)
      context environment parameterValues)
    (fallback : D)
    (position : Fin attachments.length) :
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let quotientValues := Splice.Input.siteQuotientEnvironment spliceInput
      context exact environment fallback
    quotientValues (spliceInput.quotientWire (state.parameters position)) =
      parameterValues position := by
  dsimp only
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  obtain ⟨index, wireEq, valueEq⟩ := fixed position
  have nextParameter :
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).parameters position =
      spliceInput.plugLayout.frameWire
        (spliceInput.quotientWire (state.parameters position)) := rfl
  have indexWire : context.get index =
      spliceInput.plugLayout.frameWire
        (spliceInput.quotientWire (state.parameters position)) :=
    wireEq.trans nextParameter
  have visible : spliceInput.plugLayout.plugRaw.Encloses
      (spliceInput.plugLayout.plugRaw.wires
        (spliceInput.plugLayout.frameWire
          (spliceInput.quotientWire (state.parameters position)))).scope
      (spliceInput.plugLayout.frameRegion site) := by
    exact (exact.mem_iff _).1 (indexWire ▸ List.get_mem context index)
  have quotientEq := Splice.Input.siteQuotientEnvironment_eq spliceInput
    context exact environment fallback
    (spliceInput.quotientWire (state.parameters position)) visible index indexWire
  exact quotientEq.trans valueEq

end InstantiationSemantic

end VisualProof.Rule
