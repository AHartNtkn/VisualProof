import VisualProof.Rule.Soundness.Comprehension.InstantiationShape

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram

namespace InstantiationTrace

/-- An original node outside the quantified bubble cannot be one of the bound
atoms deleted after copying, so its composite frame image survives compaction. -/
theorem nodeMap_survives_drop
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
      (initialInstantiationState payload) result)
    (node : Fin input.val.nodeCount)
    (outside : ¬input.val.Encloses bubble (input.val.nodes node).region) :
    (instantiationAtomDomain result).survives (trace.nodeMap node) = true := by
  simp only [instantiationAtomDomain, decide_eq_true_eq]
  intro member
  rw [trace.initial_processedAtoms_eq_map] at member
  obtain ⟨original, original_mem, mapped_eq⟩ := List.mem_map.mp member
  have original_eq : original = node :=
    trace.nodeMap_injective (mapped_eq.trans rfl)
  subst original
  obtain ⟨site, node_eq⟩ := (mem_boundAtoms_iff input bubble node).1 original_mem
  have encloses := input.property.atom_binders_enclose node
  rw [node_eq] at encloses
  apply outside
  simpa [node_eq, CNode.region] using encloses

/-- Dense target node index of an original node outside the rewritten bubble. -/
def droppedNodeMap
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
      (initialInstantiationState payload) result)
    (node : Fin input.val.nodeCount)
    (outside : ¬input.val.Encloses bubble (input.val.nodes node).region) :
    Fin (dropInstantiationAtomsRaw result).nodeCount :=
  (instantiationAtomDomain result).index (trace.nodeMap node)
    (trace.nodeMap_survives_drop node outside)

@[simp] theorem droppedNodeMap_origin
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
      (initialInstantiationState payload) result)
    (node : Fin input.val.nodeCount)
    (outside : ¬input.val.Encloses bubble (input.val.nodes node).region) :
    (instantiationAtomDomain result).origin
        (trace.droppedNodeMap node outside) = trace.nodeMap node := by
  exact (instantiationAtomDomain result).origin_index _ _

theorem dropped_region_shape
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
      (initialInstantiationState payload) result)
    (region : Fin input.val.regionCount) :
    (dropInstantiationAtomsRaw result).regions (trace.regionMap region) =
      mapRegionShape trace.regionMap (input.val.regions region) := by
  simpa [dropInstantiationAtomsRaw, initialInstantiationState] using
    trace.region_shape region

theorem dropped_node_shape
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
      (initialInstantiationState payload) result)
    (node : Fin input.val.nodeCount)
    (outside : ¬input.val.Encloses bubble (input.val.nodes node).region) :
    (dropInstantiationAtomsRaw result).nodes
        (trace.droppedNodeMap node outside) =
      mapNodeShape trace.regionMap (input.val.nodes node) := by
  change result.diagram.val.nodes
      ((instantiationAtomDomain result).origin
        (trace.droppedNodeMap node outside)) = _
  rw [trace.droppedNodeMap_origin node outside]
  simpa [initialInstantiationState] using trace.node_shape node

end InstantiationTrace

end VisualProof.Rule
