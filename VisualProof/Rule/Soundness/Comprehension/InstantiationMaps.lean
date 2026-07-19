import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvance

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram

namespace InstantiationTrace

private theorem map_owned_step
    (first : List A) (head : A) (tail : List A)
    (map : A → B) (rest : B → C) :
    (first.map map ++ [map head] ++ tail.map map).map rest =
      (first ++ head :: tail).map (rest ∘ map) := by
  simp [Function.comp_def]

/-- Composite frame-region map carried by a successful copy trace. -/
def regionMap
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
      state result) :
    Fin state.diagram.val.regionCount → Fin result.diagram.val.regionCount :=
  match trace with
  | .done _ _ _ => id
  | .step _ _ _ _ _ site _ arguments _ _ _ _ _ input_eq rest =>
      rest.regionMap ∘
        (instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion

/-- Composite frame-node map carried by a successful copy trace. -/
def nodeMap
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
      state result) :
    Fin state.diagram.val.nodeCount → Fin result.diagram.val.nodeCount :=
  match trace with
  | .done _ _ _ => id
  | .step _ _ _ _ _ site _ arguments _ _ _ _ _ input_eq rest =>
      rest.nodeMap ∘
        (instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameNode

/-- Composite quotient/frame-wire map carried by a successful copy trace. -/
def wireMap
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
      state result) :
    Fin state.diagram.val.wireCount → Fin result.diagram.val.wireCount :=
  match trace with
  | .done _ _ _ => id
  | .step _ _ _ _ _ site _ arguments _ _ _ _ _ input_eq rest =>
      rest.wireMap ∘ fun wire =>
        let spliceInput := instantiateSpliceInput comprehension attachments
          binders payload state site arguments
        spliceInput.plugLayout.frameWire (spliceInput.quotientWire wire)

theorem regionMap_injective
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
      state result) :
    Function.Injective trace.regionMap := by
  induction trace with
  | done => exact Function.injective_id
  | step fuel state result atom tail site candidate arguments checkedInput
      pending_eq node_eq candidate_eq arguments_eq input_eq rest ih =>
      exact ih.comp
        (instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion_injective

theorem nodeMap_injective
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
      state result) :
    Function.Injective trace.nodeMap := by
  induction trace with
  | done => exact Function.injective_id
  | step fuel state result atom tail site candidate arguments checkedInput
      pending_eq node_eq candidate_eq arguments_eq input_eq rest ih =>
      exact ih.comp
        (instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameNode_injective

theorem regionMap_bubble
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
      state result) :
    trace.regionMap state.bubble = result.bubble := by
  induction trace with
  | done => rfl
  | step fuel state result atom tail site candidate arguments checkedInput
      pending_eq node_eq candidate_eq arguments_eq input_eq rest ih =>
      simpa [regionMap, advanceInstantiationState] using ih

theorem regionMap_binderTargets
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
    (index : Fin payload.binderSpine.proxyCount) :
    trace.regionMap (state.binderTargets index) =
      result.binderTargets index := by
  induction trace with
  | done => rfl
  | step fuel state result atom tail site candidate arguments checkedInput
      pending_eq node_eq candidate_eq arguments_eq input_eq rest ih =>
      simpa [regionMap, advanceInstantiationState] using ih

theorem wireMap_parameters
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
    (index : Fin attachments.length) :
    trace.wireMap (state.parameters index) = result.parameters index := by
  induction trace with
  | done => rfl
  | step fuel state result atom tail site candidate arguments checkedInput
      pending_eq node_eq candidate_eq arguments_eq input_eq rest ih =>
      simpa [wireMap, advanceInstantiationState] using ih

/-- The trace's composite node map transports exactly the executor-owned atom
list; no processed occurrence is lost between copy steps. -/
theorem ownedAtoms_eq_map
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
      state result) :
    result.ownedAtoms = state.ownedAtoms.map trace.nodeMap := by
  induction trace with
  | done => simp [InstantiationState.ownedAtoms, nodeMap]
  | step fuel state result atom tail site candidate arguments checkedInput
      pending_eq node_eq candidate_eq arguments_eq input_eq rest ih =>
      rw [ih]
      simp only [InstantiationState.ownedAtoms, advanceInstantiationState,
        nodeMap, pending_eq]
      exact map_owned_step state.processedAtoms atom tail
        (instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameNode rest.nodeMap

end InstantiationTrace

end VisualProof.Rule
