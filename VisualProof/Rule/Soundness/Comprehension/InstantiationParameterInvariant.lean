import VisualProof.Rule.Soundness.Comprehension.InstantiationTraceBackward

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram

namespace InstantiationSemantic

/-- The executor's ordered parameter wires remain inherited at the moving
quantified bubble.  Positions are retained even when several positions name
the same wire. -/
def ParameterScopesAtBubble
    (state : InstantiationState origin parameterCount proxyCount) : Prop :=
  ∀ position,
    state.diagram.val.Encloses
        (state.diagram.val.wires (state.parameters position)).scope
        state.bubble ∧
      (state.diagram.val.wires (state.parameters position)).scope ≠
        state.bubble

/-- One alias-free operational splice preserves inherited parameter scope. -/
theorem ParameterScopesAtBubble.advance
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
    (boundaryNodup : comprehension.val.boundary.Nodup)
    (scopes : ParameterScopesAtBubble state) :
    ParameterScopesAtBubble
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible) := by
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  intro position
  obtain ⟨visible, proper⟩ := scopes position
  have scopeEq : spliceInput.coalescedScope
        (spliceInput.quotientWire (state.parameters position)) =
      (state.diagram.val.wires (state.parameters position)).scope := by
    rw [Splice.Input.coalescedScope_eq_of_boundary_nodup spliceInput
      boundaryNodup]
    rw [Splice.Input.discreteQuotientWireEquiv_quotientWire]
    rfl
  constructor
  · change layout.plugRaw.Encloses
      (layout.plugRaw.wires
        (layout.frameWire
          (spliceInput.quotientWire (state.parameters position)))).scope
      (layout.frameRegion state.bubble)
    change layout.plugRaw.Encloses
      (layout.plugWire (layout.quotientBlockWire
        (spliceInput.quotientWire (state.parameters position)))).scope
      (layout.frameRegion state.bubble)
    rw [layout.plugWire_quotientBlockWire]
    rw [layout.frame_encloses_iff, scopeEq]
    exact visible
  · change
      (layout.plugRaw.wires
        (layout.frameWire
          (spliceInput.quotientWire (state.parameters position)))).scope ≠
        layout.frameRegion state.bubble
    change (layout.plugWire (layout.quotientBlockWire
        (spliceInput.quotientWire (state.parameters position)))).scope ≠
      layout.frameRegion state.bubble
    rw [layout.plugWire_quotientBlockWire]
    intro equal
    apply proper
    rw [← scopeEq]
    exact layout.frameRegion_injective equal

/-- Parameter scope persists through the executor's complete accepted trace. -/
theorem ParameterScopesAtBubble.afterTrace
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
    (boundaryNodup : comprehension.val.boundary.Nodup)
    (scopes : ParameterScopesAtBubble state) :
    ParameterScopesAtBubble result := by
  induction trace with
  | done => exact scopes
  | step fuel state result atom tail site candidate arguments checkedInput
      pending_eq node_eq candidate_eq arguments_eq input_eq rest ih =>
      let hadmissible := (Splice.Input.checkInput_sound input_eq).2
      exact ih
        (scopes.advance comprehension attachments binders payload state atom
          tail site arguments hadmissible boundaryNodup)

/-- The serialized parameter-scope certificate initializes the trace
invariant, including repeated ordered parameters. -/
theorem initial_parameterScopesAtBubble
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders) :
    ParameterScopesAtBubble (initialInstantiationState payload) := by
  intro position
  simpa [initialInstantiationState] using payload.parameterScopesProper position

end InstantiationSemantic

end VisualProof.Rule
