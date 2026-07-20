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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

end InstantiationTrace

end VisualProof.Rule
