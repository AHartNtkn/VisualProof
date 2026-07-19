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

/-- The composite frame map preserves every retained region constructor and
maps its parent through the same composite region map. -/
theorem regionMap_shape
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
    (region : Fin state.diagram.val.regionCount) :
    result.diagram.val.regions (trace.regionMap region) =
      match state.diagram.val.regions region with
      | .sheet => .sheet
      | .cut parent => .cut (trace.regionMap parent)
      | .bubble parent arity => .bubble (trace.regionMap parent) arity := by
  induction trace with
  | done fuel state pending_empty =>
      simp only [regionMap, id_eq]
      cases state.diagram.val.regions region <;> rfl
  | step fuel state result atom tail site candidate arguments checkedInput
      pending_eq node_eq candidate_eq arguments_eq input_eq rest ih =>
      let spliceInput := instantiateSpliceInput comprehension attachments
        binders payload state site arguments
      let layout := spliceInput.plugLayout
      have mapped := ih (layout.frameRegion region)
      simp only [advanceInstantiationState] at mapped
      have frameShape : layout.plugRaw.regions (layout.frameRegion region) =
          match state.diagram.val.regions region with
          | .sheet => .sheet
          | .cut parent => .cut (layout.frameRegion parent)
          | .bubble parent arity =>
              .bubble (layout.frameRegion parent) arity := by
        change layout.plugRegion (layout.frameRegion region) = _
        rw [layout.plugRegion_frameRegion]
        cases shape : state.diagram.val.regions region <;>
          simp [Splice.Input.PlugLayout.mapFrameRegion, spliceInput,
            instantiateSpliceInput, shape] <;> rfl
      rw [frameShape] at mapped
      cases shape : state.diagram.val.regions region with
      | sheet =>
          simpa [regionMap, shape] using mapped
      | cut parent =>
          simpa [regionMap, shape] using mapped
      | bubble parent arity =>
          simpa [regionMap, shape] using mapped

/-- The composite frame map preserves every retained node constructor and
maps all region-valued fields through the composite region map. -/
theorem nodeMap_shape
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
    (node : Fin state.diagram.val.nodeCount) :
    result.diagram.val.nodes (trace.nodeMap node) =
      match state.diagram.val.nodes node with
      | .term owner freePorts term =>
          .term (trace.regionMap owner) freePorts term
      | .atom owner binder =>
          .atom (trace.regionMap owner) (trace.regionMap binder)
      | .named owner definition arity =>
          .named (trace.regionMap owner) definition arity := by
  induction trace with
  | done fuel state pending_empty =>
      simp only [nodeMap, regionMap, id_eq]
      cases state.diagram.val.nodes node <;> rfl
  | step fuel state result atom tail site candidate arguments checkedInput
      pending_eq node_eq candidate_eq arguments_eq input_eq rest ih =>
      let spliceInput := instantiateSpliceInput comprehension attachments
        binders payload state site arguments
      let layout := spliceInput.plugLayout
      have mapped := ih (layout.frameNode node)
      simp only [advanceInstantiationState] at mapped
      have frameShape : layout.plugRaw.nodes (layout.frameNode node) =
          match state.diagram.val.nodes node with
          | .term owner freePorts term =>
              .term (layout.frameRegion owner) freePorts term
          | .atom owner binder =>
              .atom (layout.frameRegion owner) (layout.frameRegion binder)
          | .named owner definition arity =>
              .named (layout.frameRegion owner) definition arity := by
        change layout.plugNode (layout.frameNode node) = _
        rw [layout.plugNode_frameNode]
        cases shape : state.diagram.val.nodes node <;>
          simp [Splice.Input.PlugLayout.mapFrameNode, spliceInput,
            instantiateSpliceInput, shape] <;> rfl
      rw [frameShape] at mapped
      cases shape : state.diagram.val.nodes node with
      | term owner freePorts term =>
          simpa [nodeMap, regionMap, shape] using mapped
      | atom owner binder =>
          simpa [nodeMap, regionMap, shape] using mapped
      | named owner definition arity =>
          simpa [nodeMap, regionMap, shape] using mapped

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

theorem regionMap_root
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
    trace.regionMap state.diagram.val.root = result.diagram.val.root := by
  induction trace with
  | done => rfl
  | step fuel state result atom tail site candidate arguments checkedInput
      pending_eq node_eq candidate_eq arguments_eq input_eq rest ih =>
      simpa [regionMap, advanceInstantiationState, instantiateSpliceInput,
        Splice.Input.PlugLayout.plugRaw] using ih

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

theorem result_pendingAtoms_empty
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
    result.pendingAtoms = [] := by
  induction trace with
  | done fuel state pending_empty => exact pending_empty
  | step fuel state result atom tail site candidate arguments checkedInput
      pending_eq node_eq candidate_eq arguments_eq input_eq rest ih =>
      exact ih

theorem initial_processedAtoms_eq_map
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
    result.processedAtoms =
      (boundAtoms input bubble).map trace.nodeMap := by
  have owned := trace.ownedAtoms_eq_map
  rw [InstantiationState.ownedAtoms, trace.result_pendingAtoms_empty,
    List.append_nil] at owned
  simpa [InstantiationState.ownedAtoms, initialInstantiationState] using owned

end InstantiationTrace

end VisualProof.Rule
