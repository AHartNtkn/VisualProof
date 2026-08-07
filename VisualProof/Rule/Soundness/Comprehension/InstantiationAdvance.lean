import VisualProof.Rule.Soundness.Comprehension.InstantiationTrace

namespace VisualProof.Rule

open VisualProof.Concrete

open VisualProof
open VisualProof.Diagram

/-- The checked splice exposed by one trace step returns exactly the next
executor diagram, including the proof-irrelevant well-formedness package. -/
theorem advanceInstantiationState_spliceChecked
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    (comprehension : Concrete.CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Concrete.Checked }
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (atom : Fin state.diagram.val.nodeCount)
    (tail : List (Fin state.diagram.val.nodeCount))
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (checkedInput : Concrete.Splice.Input.CheckedInput )
    (hinput : Concrete.Splice.Input.checkInput
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments) = .ok checkedInput) :
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let hadmissible := (Concrete.Splice.Input.checkInput_sound hinput).2
    let next := advanceInstantiationState comprehension attachments binders
      payload state atom tail site arguments hadmissible
    Concrete.Splice.Input.spliceChecked  spliceInput = .ok next.diagram := by
  dsimp only
  unfold Concrete.Splice.Input.spliceChecked
  rw [hinput]
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let hadmissible := (Concrete.Splice.Input.checkInput_sound hinput).2
  rw [checkWellFormed_complete
    (Concrete.Splice.Input.PlugLayout.plugRaw_wellFormed  spliceInput layout
      hadmissible)]
  rfl

@[simp] theorem advanceInstantiationState_diagram
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    (comprehension : Concrete.CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Concrete.Checked }
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (atom : Fin state.diagram.val.nodeCount)
    (tail : List (Fin state.diagram.val.nodeCount))
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible) :
    (advanceInstantiationState comprehension attachments binders payload state
      atom tail site arguments hadmissible).diagram.val =
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw :=
  rfl

@[simp] theorem advanceInstantiationState_interface
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    (comprehension : Concrete.CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Concrete.Checked }
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (atom : Fin state.diagram.val.nodeCount)
    (tail : List (Fin state.diagram.val.nodeCount))
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible) :
    (advanceInstantiationState comprehension attachments binders payload state
      atom tail site arguments hadmissible).interface =
      state.interface.compose (spliceFrameWireTransport
        (instantiateSpliceInput comprehension attachments binders payload state
          site arguments)) :=
  rfl

@[simp] theorem advanceInstantiationState_provenance
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    (comprehension : Concrete.CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Concrete.Checked }
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (atom : Fin state.diagram.val.nodeCount)
    (tail : List (Fin state.diagram.val.nodeCount))
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible) :
    (advanceInstantiationState comprehension attachments binders payload state
      atom tail site arguments hadmissible).provenance =
      state.provenance.compose (spliceFrameWireProvenance
        (instantiateSpliceInput comprehension attachments binders payload state
          site arguments)) :=
  rfl

end VisualProof.Rule
