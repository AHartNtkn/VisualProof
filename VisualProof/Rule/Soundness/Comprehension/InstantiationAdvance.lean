import VisualProof.Rule.Soundness.Comprehension.InstantiationTrace

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram

/-- The checked splice exposed by one trace step returns exactly the next
executor diagram, including the proof-irrelevant well-formedness package. -/
theorem advanceInstantiationState_spliceChecked
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
    (checkedInput : Splice.Input.CheckedInput signature)
    (hinput : Splice.Input.checkInput
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments) = .ok checkedInput) :
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let hadmissible := (Splice.Input.checkInput_sound hinput).2
    let next := advanceInstantiationState comprehension attachments binders
      payload state atom tail site arguments hadmissible
    Splice.Input.spliceChecked signature spliceInput = .ok next.diagram := by
  dsimp only
  unfold Splice.Input.spliceChecked
  rw [hinput]
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let hadmissible := (Splice.Input.checkInput_sound hinput).2
  rw [checkWellFormed_complete
    (Splice.Input.PlugLayout.plugRaw_wellFormed signature spliceInput layout
      hadmissible)]
  rfl

@[simp] theorem advanceInstantiationState_diagram
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
      payload state site arguments).Admissible) :
    (advanceInstantiationState comprehension attachments binders payload state
      atom tail site arguments hadmissible).diagram.val =
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw :=
  rfl

@[simp] theorem advanceInstantiationState_interface
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
      payload state site arguments).Admissible) :
    (advanceInstantiationState comprehension attachments binders payload state
      atom tail site arguments hadmissible).interface =
      state.interface.compose (spliceFrameInterfaceTransport
        (instantiateSpliceInput comprehension attachments binders payload state
          site arguments)) :=
  rfl

@[simp] theorem advanceInstantiationState_provenance
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
      payload state site arguments).Admissible) :
    (advanceInstantiationState comprehension attachments binders payload state
      atom tail site arguments hadmissible).provenance =
      state.provenance.compose (spliceFrameWireProvenance
        (instantiateSpliceInput comprehension attachments binders payload state
          site arguments)) :=
  rfl

end VisualProof.Rule
