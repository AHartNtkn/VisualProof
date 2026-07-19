import VisualProof.Rule.Soundness.Comprehension.InstantiationTerminalRelation

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram

namespace InstantiationSemantic

/-- One accepted splice preserves the retained target binders' shape and their
enclosure of the moving quantified bubble. -/
theorem BinderTargetsAtBubble.advance
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
    (atom : Fin state.diagram.val.nodeCount)
    (tail : List (Fin state.diagram.val.nodeCount))
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (targets : BinderTargetsAtBubble payload state) :
    BinderTargetsAtBubble payload
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible) := by
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  constructor
  · intro index
    obtain ⟨parent, htarget⟩ := targets.target_shape index
    refine ⟨layout.frameRegion parent, ?_⟩
    simpa [advanceInstantiationState, spliceInput, layout] using
      layout.plugRaw_frameRegion_bubble (state.binderTargets index) parent
        (payload.binderSpine.arity index) htarget
  · intro index
    simpa [advanceInstantiationState, spliceInput, layout] using
      layout.frame_encloses (targets.target_encloses index)

/-- Every nonterminal executor trace state carries the binder-target invariant
needed to interpret the terminal comprehension body at that copy. -/
def BinderTargetsEveryStep
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
  | .done _ _ _ => True
  | .step _ state _ _ _ _ _ _ _ _ _ _ _ _ rest =>
      BinderTargetsAtBubble payload state ∧ BinderTargetsEveryStep rest

theorem binderTargetsEveryStep_of
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
    (targets : BinderTargetsAtBubble payload state) :
    BinderTargetsEveryStep trace := by
  induction trace with
  | done => trivial
  | step fuel state result atom tail site candidate arguments checkedInput
      pending_eq node_eq candidate_eq arguments_eq input_eq rest ih =>
      let hadmissible := (Splice.Input.checkInput_sound input_eq).2
      exact ⟨targets, ih (targets.advance payload state atom tail site arguments
        hadmissible)⟩

/-- The retained binder targets remain well-shaped and enclosing at the final
state of an accepted executor trace. -/
theorem BinderTargetsAtBubble.afterTrace
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
    (targets : BinderTargetsAtBubble payload state) :
    BinderTargetsAtBubble payload result := by
  induction trace with
  | done => exact targets
  | step fuel state result atom tail site candidate arguments checkedInput
      pending_eq node_eq candidate_eq arguments_eq input_eq rest ih =>
      let hadmissible := (Splice.Input.checkInput_sound input_eq).2
      exact ih (targets.advance payload state atom tail site arguments
        hadmissible)

/-- The first accepted copy supplies target shape; the serialized payload
supplies the stronger target-to-bubble enclosure, and both persist thereafter. -/
theorem initial_binderTargetsEveryStep
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
    BinderTargetsEveryStep trace := by
  cases trace with
  | done => trivial
  | step fuel state result atom tail site candidate arguments checkedInput
      pending_eq node_eq candidate_eq arguments_eq input_eq rest =>
      let hadmissible := (Splice.Input.checkInput_sound input_eq).2
      have targets : BinderTargetsAtBubble payload
          (initialInstantiationState payload) := {
        target_shape := hadmissible.binder_targets_match
        target_encloses := fun index =>
          (payload.binderTargetsProper index).1
      }
      exact ⟨targets, binderTargetsEveryStep_of rest
        (targets.advance payload (initialInstantiationState payload) atom tail
          site arguments hadmissible)⟩

end InstantiationSemantic

end VisualProof.Rule
