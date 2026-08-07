import VisualProof.Rule.Soundness.Comprehension.InstantiationTerminalSemantic

namespace VisualProof.Rule

open VisualProof.Concrete

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- The terminal witness is invariant along the executor's complete copy
trace when wire values are pulled back through the trace's certified frame
map.  In particular, every occurrence is interpreted with one relation value,
not with an independently chosen per-splice approximation. -/
theorem terminalRelationOfValues_eq_along_trace
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {origin : Concrete.Checked }
    {fuel : Nat}
    {state result : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount}
    (trace : InstantiationTrace comprehension attachments binders payload fuel
      state result)
    (stateSite : Fin state.diagram.val.regionCount)
    (resultSite : Fin result.diagram.val.regionCount)
    (stateArguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (resultArguments : Fin payload.arity → Fin result.diagram.val.wireCount)
    (hnonempty : payload.binderSpine.proxyCount ≠ 0)
    (model : Model)
    (resultWire : Fin result.diagram.val.wireCount → model.Carrier)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index)) :
    terminalRelationOfValues payload state stateSite stateArguments hnonempty
        model  (resultWire ∘ trace.wireMap) values =
      terminalRelationOfValues payload result resultSite resultArguments
        hnonempty model  resultWire values := by
  apply terminalRelationOfValues_eq payload state result stateSite resultSite
    stateArguments resultArguments hnonempty model
      (resultWire ∘ trace.wireMap) resultWire values
  funext index
  change resultWire (trace.wireMap (state.parameters index)) =
    resultWire (result.parameters index)
  rw [trace.wireMap_parameters]

/-- Pulling both the parameter valuation and an occurrence's ordered argument
valuation back through a complete executor trace preserves application of the
single canonical terminal relation.  Repeated argument wires remain repeated:
the statement is pointwise over the executor's `Fin`-indexed argument vector. -/
theorem terminalRelationOfValues_apply_along_trace
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {origin : Concrete.Checked }
    {fuel : Nat}
    {state result : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount}
    (trace : InstantiationTrace comprehension attachments binders payload fuel
      state result)
    (stateSite : Fin state.diagram.val.regionCount)
    (resultSite : Fin result.diagram.val.regionCount)
    (stateArguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (resultArguments : Fin payload.arity → Fin result.diagram.val.wireCount)
    (arguments_eq : trace.wireMap ∘ stateArguments = resultArguments)
    (hnonempty : payload.binderSpine.proxyCount ≠ 0)
    (model : Model)
    (resultWire : Fin result.diagram.val.wireCount → model.Carrier)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index)) :
    terminalRelationOfValues payload state stateSite stateArguments hnonempty
        model  (resultWire ∘ trace.wireMap) values
        ((resultWire ∘ trace.wireMap) ∘ stateArguments) ↔
      terminalRelationOfValues payload result resultSite resultArguments
        hnonempty model  resultWire values
        (resultWire ∘ resultArguments) := by
  rw [terminalRelationOfValues_eq_along_trace trace stateSite resultSite
    stateArguments resultArguments hnonempty model  resultWire values]
  have argumentValues :
      ((resultWire ∘ trace.wireMap) ∘ stateArguments) =
        resultWire ∘ resultArguments := by
    funext index
    exact congrArg resultWire (congrFun arguments_eq index)
  rw [argumentValues]

end InstantiationSemantic

end VisualProof.Rule
