import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvance
import VisualProof.Diagram.Concrete.Subgraph.Splice.Input.Discrete

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
  | .done .. => id
  | .step _ _ _ _ _ _ _ _ plan _ _ _ _ rest => fun region =>
      rest.regionMap (Fin.cast (by rw [plan.next_eq]; rfl)
        (plan.spliceInput.plugLayout.frameRegion region))

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
  | .done .. => id
  | .step _ _ _ _ _ _ _ _ plan _ _ _ _ rest => fun node =>
      rest.nodeMap (Fin.cast (by rw [plan.next_eq]; rfl)
        (plan.spliceInput.plugLayout.frameNode node))

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
  | .done .. => id
  | .step _ _ _ _ _ _ _ _ plan _ _ _ _ rest => fun wire =>
      rest.wireMap (Fin.cast (by rw [plan.next_eq]; rfl)
        (plan.spliceInput.plugLayout.frameWire
          (plan.spliceInput.quotientWire wire)))

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
  | step fuel state result atom tail site candidate arguments plan
      pending_eq node_eq candidate_eq arguments_eq rest ih =>
      apply ih.comp
      intro left right equal
      apply plan.spliceInput.plugLayout.frameRegion_injective
      apply Fin.ext
      simpa using congrArg Fin.val equal

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
  | step fuel state result atom tail site candidate arguments plan
      pending_eq node_eq candidate_eq arguments_eq rest ih =>
      apply ih.comp
      intro left right equal
      apply plan.spliceInput.plugLayout.frameNode_injective
      apply Fin.ext
      simpa using congrArg Fin.val equal

/-- Alias materialization makes the composite host-wire map injective.  No
two pre-existing wire identities are coalesced by any accepted copy step. -/
theorem wireMap_injective
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
    Function.Injective trace.wireMap := by
  induction trace with
  | done => exact Function.injective_id
  | step fuel state result atom tail site candidate arguments plan
      pending_eq node_eq candidate_eq arguments_eq rest ih =>
      let spliceInput := plan.spliceInput
      let layout := spliceInput.plugLayout
      apply ih.comp
      intro left right equal
      have frameEqual : layout.frameWire (spliceInput.quotientWire left) =
          layout.frameWire (spliceInput.quotientWire right) := by
        apply Fin.ext
        simpa using congrArg Fin.val equal
      have quotientEqual := layout.frameWire_injective frameEqual
      have hostEqual := congrArg
        (Splice.Input.discreteQuotientWireEquivOfAttachmentsRespectBoundary
          spliceInput plan.attachmentsRespectBoundary)
        quotientEqual
      simpa [spliceInput] using hostEqual

/-- The composite executor frame maps preserve and reflect endpoint ownership
for every original wire/node pair.  Alias materialization makes each
intermediate host quotient discrete, so no distinct original wire can acquire
the mapped endpoint. -/
theorem endpointOccurs_wireMap_nodeMap_iff
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
    (wire : Fin state.diagram.val.wireCount)
    (node : Fin state.diagram.val.nodeCount)
    (port : CPort) :
    result.diagram.val.EndpointOccurs (trace.wireMap wire)
        ⟨trace.nodeMap node, port⟩ ↔
      state.diagram.val.EndpointOccurs wire ⟨node, port⟩ := by
  induction trace with
  | done => rfl
  | step fuel state result atom tail site candidate arguments plan
      pending_eq node_eq candidate_eq arguments_eq rest ih =>
      let spliceInput := plan.spliceInput
      let layout := spliceInput.plugLayout
      let quotient := spliceInput.quotientWire wire
      have restIff := ih
        (Fin.cast (by rw [plan.next_eq]; rfl) (layout.frameWire quotient))
        (Fin.cast (by rw [plan.next_eq]; rfl) (layout.frameNode node))
      simp only [wireMap, nodeMap]
      refine restIff.trans ?_
      let advanced := advanceMaterializedInstantiationState comprehension
        attachments binders payload state atom tail site arguments
        plan.materialization
          (Splice.Input.checkInput_sound plan.checkedInputChecked).2
      have rawIff : advanced.diagram.val.EndpointOccurs
          (layout.frameWire quotient) ⟨layout.frameNode node, port⟩ ↔
          state.diagram.val.EndpointOccurs wire ⟨node, port⟩ := by
        change layout.plugRaw.EndpointOccurs
            (layout.frameWire quotient) ⟨layout.frameNode node, port⟩ ↔ _
        constructor
        · intro occurs
          obtain ⟨sourceWire, mappedWire, coalescedOccurs⟩ :=
            layout.plugRaw_frameEndpoint_backward
              (layout.frameWire quotient) ⟨node, port⟩ (by
                simpa [Splice.Input.PlugLayout.mapFrameEndpoint] using occurs)
          have sourceWireEq : sourceWire = quotient :=
            layout.frameWire_injective mappedWire
          subst sourceWire
          change ⟨node, port⟩ ∈ spliceInput.coalescedEndpoints quotient
            at coalescedOccurs
          rw [Splice.Input.coalescedEndpoints_eq_of_attachmentsRespectBoundary
            spliceInput plan.attachmentsRespectBoundary] at coalescedOccurs
          simpa [quotient, spliceInput] using coalescedOccurs
        · intro occurs
          have coalesced := spliceInput.endpointOccurs_quotient wire
            ⟨node, port⟩ occurs
          have plugged := layout.plugRaw_frameEndpoint_forward quotient
            ⟨node, port⟩ coalesced
          simpa [Splice.Input.PlugLayout.mapFrameEndpoint] using plugged
      have transported : ∀ (next : InstantiationState origin attachments.length
          payload.binderSpine.proxyCount) (next_eq : next = advanced),
          next.diagram.val.EndpointOccurs
              (Fin.cast (by rw [next_eq]; rfl) (layout.frameWire quotient))
              ⟨Fin.cast (by rw [next_eq]; rfl) (layout.frameNode node), port⟩ ↔
            state.diagram.val.EndpointOccurs wire ⟨node, port⟩ := by
        intro next next_eq
        subst next
        simpa using rawIff
      exact transported plan.next plan.next_eq

/-- The composite host-wire map carries each retained wire scope through the
same composite region map. -/
theorem wireMap_scope
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
    (wire : Fin state.diagram.val.wireCount) :
    (result.diagram.val.wires (trace.wireMap wire)).scope =
      trace.regionMap (state.diagram.val.wires wire).scope := by
  induction trace with
  | done => rfl
  | step fuel state result atom tail site candidate arguments plan
      pending_eq node_eq candidate_eq arguments_eq rest ih =>
      let spliceInput := plan.spliceInput
      let layout := spliceInput.plugLayout
      let quotient := spliceInput.quotientWire wire
      let mappedWire : Fin plan.next.diagram.val.wireCount :=
        Fin.cast (by rw [plan.next_eq]; rfl)
        (layout.frameWire quotient)
      have mapped := ih mappedWire
      let advanced := advanceMaterializedInstantiationState comprehension
        attachments binders payload state atom tail site arguments
        plan.materialization
          (Splice.Input.checkInput_sound plan.checkedInputChecked).2
      have rawScope :
          (advanced.diagram.val.wires (layout.frameWire quotient)).scope =
            layout.frameRegion (state.diagram.val.wires wire).scope := by
        change (layout.plugWire (layout.quotientBlockWire quotient)).scope = _
        rw [layout.plugWire_quotientBlockWire]
        have scopeEq :=
          Splice.Input.coalescedScope_eq_of_attachmentsRespectBoundary
            spliceInput plan.attachmentsRespectBoundary quotient
        rw [scopeEq]
        simp [quotient, spliceInput] <;> rfl
      have transported : ∀ (next : InstantiationState origin attachments.length
          payload.binderSpine.proxyCount) (next_eq : next = advanced),
          (next.diagram.val.wires
              (Fin.cast (by rw [next_eq]; rfl)
                (layout.frameWire quotient))).scope =
            Fin.cast (by rw [next_eq]; rfl)
              (layout.frameRegion (state.diagram.val.wires wire).scope) := by
        intro next next_eq
        subst next
        simpa using rawScope
      have oneStep := transported plan.next plan.next_eq
      simp only [wireMap, regionMap]
      exact mapped.trans (congrArg rest.regionMap oneStep)

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
  | step fuel state result atom tail site candidate arguments plan
      pending_eq node_eq candidate_eq arguments_eq rest ih =>
      let spliceInput := plan.spliceInput
      let layout := spliceInput.plugLayout
      let mappedRegion : Fin plan.next.diagram.val.regionCount :=
        Fin.cast (by rw [plan.next_eq]; rfl) (layout.frameRegion region)
      have mapped := ih mappedRegion
      let advanced := advanceMaterializedInstantiationState comprehension
        attachments binders payload state atom tail site arguments
        plan.materialization
          (Splice.Input.checkInput_sound plan.checkedInputChecked).2
      have rawShape : advanced.diagram.val.regions (layout.frameRegion region) =
          match state.diagram.val.regions region with
          | .sheet => .sheet
          | .cut parent => .cut (layout.frameRegion parent)
          | .bubble parent arity =>
              .bubble (layout.frameRegion parent) arity := by
        change layout.plugRegion (layout.frameRegion region) = _
        rw [layout.plugRegion_frameRegion]
        cases shape : state.diagram.val.regions region <;>
          simp [Splice.Input.PlugLayout.mapFrameRegion, spliceInput,
            InstantiationCopyPlan.spliceInput, materializedInstantiationSpliceInput,
            instantiateSpliceInput, shape] <;> rfl
      have transported : ∀ (next : InstantiationState origin attachments.length
          payload.binderSpine.proxyCount) (next_eq : next = advanced),
          next.diagram.val.regions
              (Fin.cast (by rw [next_eq]; rfl) (layout.frameRegion region)) =
            match state.diagram.val.regions region with
            | .sheet => .sheet
            | .cut parent =>
                .cut (Fin.cast (by rw [next_eq]; rfl)
                  (layout.frameRegion parent))
            | .bubble parent arity =>
                .bubble (Fin.cast (by rw [next_eq]; rfl)
                  (layout.frameRegion parent)) arity := by
        intro next next_eq
        subst next
        simpa using rawShape
      have oneStep := transported plan.next plan.next_eq
      rw [oneStep] at mapped
      cases shape : state.diagram.val.regions region with
      | sheet => simpa [regionMap, shape] using mapped
      | cut parent => simpa [regionMap, shape] using mapped
      | bubble parent arity => simpa [regionMap, shape] using mapped

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
  | step fuel state result atom tail site candidate arguments plan
      pending_eq node_eq candidate_eq arguments_eq rest ih =>
      let spliceInput := plan.spliceInput
      let layout := spliceInput.plugLayout
      let mappedNode : Fin plan.next.diagram.val.nodeCount :=
        Fin.cast (by rw [plan.next_eq]; rfl) (layout.frameNode node)
      have mapped := ih mappedNode
      let advanced := advanceMaterializedInstantiationState comprehension
        attachments binders payload state atom tail site arguments
        plan.materialization
          (Splice.Input.checkInput_sound plan.checkedInputChecked).2
      have rawShape : advanced.diagram.val.nodes (layout.frameNode node) =
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
            InstantiationCopyPlan.spliceInput, materializedInstantiationSpliceInput,
            instantiateSpliceInput, shape] <;> rfl
      have transported : ∀ (next : InstantiationState origin attachments.length
          payload.binderSpine.proxyCount) (next_eq : next = advanced),
          next.diagram.val.nodes
              (Fin.cast (by rw [next_eq]; rfl) (layout.frameNode node)) =
            match state.diagram.val.nodes node with
            | .term owner freePorts term =>
                .term (Fin.cast (by rw [next_eq]; rfl)
                  (layout.frameRegion owner)) freePorts term
            | .atom owner binder =>
                .atom (Fin.cast (by rw [next_eq]; rfl)
                    (layout.frameRegion owner))
                  (Fin.cast (by rw [next_eq]; rfl)
                    (layout.frameRegion binder))
            | .named owner definition arity =>
                .named (Fin.cast (by rw [next_eq]; rfl)
                  (layout.frameRegion owner)) definition arity := by
        intro next next_eq
        subst next
        simpa using rawShape
      have oneStep := transported plan.next plan.next_eq
      rw [oneStep] at mapped
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
  | step fuel state result atom tail site candidate arguments plan
      pending_eq node_eq candidate_eq arguments_eq rest ih =>
      let layout := plan.spliceInput.plugLayout
      have oneStep : Fin.cast (by rw [plan.next_eq]; rfl)
          (layout.frameRegion state.bubble) = plan.next.bubble := by
        apply Fin.ext
        simpa [layout, InstantiationCopyPlan.spliceInput,
          advanceMaterializedInstantiationState, advanceInstantiationState]
          using congrArg (fun next => next.bubble.val) plan.next_eq.symm
      simp only [regionMap]
      rw [oneStep]
      exact ih

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
  | step fuel state result atom tail site candidate arguments plan
      pending_eq node_eq candidate_eq arguments_eq rest ih =>
      let layout := plan.spliceInput.plugLayout
      have oneStep : Fin.cast (by rw [plan.next_eq]; rfl)
          (layout.frameRegion state.diagram.val.root) =
          plan.next.diagram.val.root := by
        apply Fin.ext
        simpa [layout, InstantiationCopyPlan.spliceInput,
          materializedInstantiationSpliceInput, instantiateSpliceInput,
          advanceMaterializedInstantiationState, advanceInstantiationState,
          Splice.Input.PlugLayout.plugRaw]
          using congrArg (fun next => next.diagram.val.root.val)
            plan.next_eq.symm
      simp only [regionMap]
      rw [oneStep]
      exact ih

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
  | step fuel state result atom tail site candidate arguments plan
      pending_eq node_eq candidate_eq arguments_eq rest ih =>
      let layout := plan.spliceInput.plugLayout
      have oneStep : Fin.cast (by rw [plan.next_eq]; rfl)
          (layout.frameRegion (state.binderTargets index)) =
          plan.next.binderTargets index := by
        apply Fin.ext
        simpa [layout, InstantiationCopyPlan.spliceInput,
          advanceMaterializedInstantiationState, advanceInstantiationState]
          using congrArg (fun next => (next.binderTargets index).val)
            plan.next_eq.symm
      simp only [regionMap]
      rw [oneStep]
      exact ih

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
  | step fuel state result atom tail site candidate arguments plan
      pending_eq node_eq candidate_eq arguments_eq rest ih =>
      let spliceInput := plan.spliceInput
      let layout := spliceInput.plugLayout
      have oneStep : Fin.cast (by rw [plan.next_eq]; rfl)
          (layout.frameWire (spliceInput.quotientWire
            (state.parameters index))) = plan.next.parameters index := by
        apply Fin.ext
        simpa [layout, spliceInput, InstantiationCopyPlan.spliceInput,
          advanceMaterializedInstantiationState, advanceInstantiationState]
          using congrArg (fun next => (next.parameters index).val)
            plan.next_eq.symm
      simp only [wireMap]
      rw [oneStep]
      exact ih

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
  | step fuel state result atom tail site candidate arguments plan
      pending_eq node_eq candidate_eq arguments_eq rest ih =>
      let spliceInput := plan.spliceInput
      let layout := spliceInput.plugLayout
      let advanced := advanceMaterializedInstantiationState comprehension
        attachments binders payload state atom tail site arguments
        plan.materialization
          (Splice.Input.checkInput_sound plan.checkedInputChecked).2
      have rawOwned : advanced.ownedAtoms =
          state.ownedAtoms.map layout.frameNode := by
        dsimp [advanced, layout, spliceInput, InstantiationState.ownedAtoms,
          advanceMaterializedInstantiationState, advanceInstantiationState]
        rw [pending_eq]
        unfold InstantiationCopyPlan.spliceInput
        induction state.processedAtoms with
        | nil => rfl
        | cons head first ih =>
            simp only [List.cons_append]
            exact congrArg (List.cons _) ih
      have transported : ∀ (next : InstantiationState origin attachments.length
          payload.binderSpine.proxyCount) (next_eq : next = advanced),
          next.ownedAtoms = state.ownedAtoms.map (fun node =>
            Fin.cast (by rw [next_eq]; rfl) (layout.frameNode node)) := by
        intro next next_eq
        subst next
        simpa using rawOwned
      have oneStep := transported plan.next plan.next_eq
      rw [ih, oneStep, List.map_map]
      rfl

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
  | step fuel state result atom tail site candidate arguments plan
      pending_eq node_eq candidate_eq arguments_eq rest ih =>
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
