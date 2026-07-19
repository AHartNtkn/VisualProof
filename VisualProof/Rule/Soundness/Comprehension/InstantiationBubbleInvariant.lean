import VisualProof.Rule.Soundness.Comprehension.InstantiationTargetInvariant
import VisualProof.Rule.Soundness.Comprehension.InstantiationCoalescedState

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram

namespace InstantiationSemantic

/-- The moving quantified region keeps the payload's declared relation arity
through every checked splice. -/
def BubbleHasPayloadArity
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
      payload.binderSpine.proxyCount) : Prop :=
  ∃ parent, state.diagram.val.regions state.bubble =
    .bubble parent payload.arity

theorem initial_bubbleHasPayloadArity
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders) :
    BubbleHasPayloadArity payload (initialInstantiationState payload) := by
  exact ⟨payload.parent, payload.bubble_eq⟩

theorem BubbleHasPayloadArity.coalesced
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
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (shape : BubbleHasPayloadArity payload state) :
    BubbleHasPayloadArity payload
      (coalescedInstantiationState comprehension attachments binders payload
        state site arguments hadmissible) := by
  obtain ⟨parent, bubbleShape⟩ := shape
  exact ⟨parent, by
    simpa [coalescedInstantiationState, instantiateSpliceInput,
      Splice.Input.coalesceFrameRaw_regions] using bubbleShape⟩

theorem BubbleHasPayloadArity.advance
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
    (shape : BubbleHasPayloadArity payload state) :
    BubbleHasPayloadArity payload
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible) := by
  obtain ⟨parent, bubbleShape⟩ := shape
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  refine ⟨layout.frameRegion parent, ?_⟩
  simpa [advanceInstantiationState, spliceInput, layout] using
    layout.plugRaw_frameRegion_bubble state.bubble parent payload.arity
      (by simpa [spliceInput, instantiateSpliceInput,
        Splice.Input.coalesceFrameRaw_regions] using bubbleShape)

/-- Every state visited by a successful executor trace carries the moving
binder's payload arity. -/
def BubbleShapeEveryStep
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
      state result) : Prop :=
  match trace with
  | .done _ state _ => BubbleHasPayloadArity payload state
  | .step _ state _ _ _ _ _ _ _ _ _ _ _ _ rest =>
      BubbleHasPayloadArity payload state ∧ BubbleShapeEveryStep rest

theorem bubbleShapeEveryStep_of
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
    (shape : BubbleHasPayloadArity payload state) :
    BubbleShapeEveryStep trace := by
  induction trace with
  | done => exact shape
  | step fuel state result atom tail site candidate arguments checkedInput
      pending_eq node_eq candidate_eq arguments_eq input_eq rest ih =>
      let hadmissible := (Splice.Input.checkInput_sound input_eq).2
      exact ⟨shape, ih (shape.advance comprehension attachments binders payload
        state atom tail site arguments hadmissible)⟩

theorem initial_bubbleShapeEveryStep
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
      (initialInstantiationState payload) result) :
    BubbleShapeEveryStep trace :=
  bubbleShapeEveryStep_of trace (initial_bubbleHasPayloadArity payload)

end InstantiationSemantic

end VisualProof.Rule
