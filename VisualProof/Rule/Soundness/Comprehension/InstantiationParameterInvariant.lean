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

/-- Every inherited parameter occurs in the canonical compiler context of the
final dropped bubble, never in its bubble-local suffix. -/
theorem parameter_mem_droppedBubbleOuter
    (state : InstantiationState origin parameterCount proxyCount)
    (scopes : ParameterScopesAtBubble state)
    (position : Fin parameterCount) :
    state.parameters position ∈
      (droppedBubbleView state).compilerLeaf.inheritedWires := by
  let view := droppedBubbleView state
  let leaf := view.compilerLeaf
  have visible := (scopes position).1
  have droppedVisible : (dropInstantiationAtomsRaw state).Encloses
      ((dropInstantiationAtomsRaw state).wires
        (state.parameters position)).scope state.bubble := by
    simpa only [InstantiationDrop.raw_wire_scope] using
      (InstantiationDrop.raw_encloses_iff state
        (state.diagram.val.wires (state.parameters position)).scope
        state.bubble).2 visible
  have member : state.parameters position ∈
      leaf.inheritedWires.extend state.bubble :=
    (leaf.wiresExact.mem_iff (state.parameters position)).2 droppedVisible
  rcases List.mem_append.mp member with inherited | localMember
  · exact inherited
  · have localScope :
        ((dropInstantiationAtomsRaw state).wires
          (state.parameters position)).scope = state.bubble :=
      (ConcreteElaboration.mem_exactScopeWires _ _ _).1 localMember
    exact False.elim ((scopes position).2 (by
      simpa only [InstantiationDrop.raw_wire_scope] using localScope))

/-- Canonical index of one ordered parameter in the final bubble's inherited
compiler context. -/
noncomputable def droppedBubbleParameterIndex
    (state : InstantiationState origin parameterCount proxyCount)
    (scopes : ParameterScopesAtBubble state)
    (position : Fin parameterCount) :
    Fin (droppedBubbleView state).compilerLeaf.inheritedWires.length :=
  Classical.choose (ConcreteElaboration.WireContext.lookup?_complete
    (parameter_mem_droppedBubbleOuter state scopes position))

@[simp] theorem droppedBubbleParameterIndex_get
    (state : InstantiationState origin parameterCount proxyCount)
    (scopes : ParameterScopesAtBubble state)
    (position : Fin parameterCount) :
    (droppedBubbleView state).compilerLeaf.inheritedWires.get
        (droppedBubbleParameterIndex state scopes position) =
      state.parameters position :=
  ConcreteElaboration.WireContext.lookup?_sound
    (Classical.choose_spec (ConcreteElaboration.WireContext.lookup?_complete
      (parameter_mem_droppedBubbleOuter state scopes position)))

/-- Ordered parameter valuation read from the canonical final bubble focus.
Repeated parameter positions deliberately reuse the same context value. -/
noncomputable def droppedBubbleParameterValues
    (state : InstantiationState origin parameterCount proxyCount)
    (scopes : ParameterScopesAtBubble state)
    (environment : Fin
      (droppedBubbleView state).compilerLeaf.inheritedWires.length → D) :
    Fin parameterCount → D :=
  fun position => environment
    (droppedBubbleParameterIndex state scopes position)

theorem droppedBubbleParameterValues_fixed
    (state : InstantiationState origin parameterCount proxyCount)
    (scopes : ParameterScopesAtBubble state)
    (environment : Fin
      (droppedBubbleView state).compilerLeaf.inheritedWires.length → D) :
    ParameterValuesAt state
      (droppedBubbleView state).compilerLeaf.inheritedWires environment
      (droppedBubbleParameterValues state scopes environment) := by
  intro position
  exact ⟨droppedBubbleParameterIndex state scopes position,
    droppedBubbleParameterIndex_get state scopes position, rfl⟩

end InstantiationSemantic

end VisualProof.Rule
