import VisualProof.Rule.Soundness.Comprehension.InstantiationFinalNodeCompiler

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram

namespace InstantiationTrace

def droppedParentForwardMap
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
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result) :
    ConcreteElaboration.LocalOccurrence input.val.regionCount input.val.nodeCount →
      ConcreteElaboration.LocalOccurrence
        (dropInstantiationAtomsRaw result).regionCount
        (dropInstantiationAtomsRaw result).nodeCount :=
  copyTrace.droppedOutsideOccurrenceMap payload.parent
    (payload_bubble_not_encloses_parent payload)

def DroppedParentPreimage
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
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    (dropped : ConcreteElaboration.LocalOccurrence
      (dropInstantiationAtomsRaw result).regionCount
      (dropInstantiationAtomsRaw result).nodeCount) : Prop :=
  ∃ original,
    original ∈ ConcreteElaboration.localOccurrences input.val payload.parent ∧
      copyTrace.droppedParentForwardMap original = dropped

noncomputable def droppedParentReverseMap
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
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result) :
    ConcreteElaboration.LocalOccurrence
        (dropInstantiationAtomsRaw result).regionCount
        (dropInstantiationAtomsRaw result).nodeCount →
      ConcreteElaboration.LocalOccurrence input.val.regionCount
        input.val.nodeCount := fun dropped => by
  classical
  exact if preimage : copyTrace.DroppedParentPreimage dropped then
    Classical.choose preimage
  else .child payload.parent

private theorem droppedParentForwardMap_injective_on_local
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
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    {left right : ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount}
    (leftMember : left ∈
      ConcreteElaboration.localOccurrences input.val payload.parent)
    (rightMember : right ∈
      ConcreteElaboration.localOccurrences input.val payload.parent)
    (mapped : copyTrace.droppedParentForwardMap left =
      copyTrace.droppedParentForwardMap right) :
    left = right := by
  cases left with
  | node leftNode =>
      have leftRegion :=
        (ConcreteElaboration.mem_localOccurrences_node input.val payload.parent
          leftNode).1 leftMember
      cases right with
      | node rightNode =>
          have rightRegion :=
            (ConcreteElaboration.mem_localOccurrences_node input.val
              payload.parent rightNode).1 rightMember
          have nodeEq : copyTrace.droppedNodeMap leftNode (fun enclosed =>
                payload_bubble_not_encloses_parent payload
                  (leftRegion ▸ enclosed)) =
              copyTrace.droppedNodeMap rightNode (fun enclosed =>
                payload_bubble_not_encloses_parent payload
                  (rightRegion ▸ enclosed)) := by
            exact ConcreteElaboration.LocalOccurrence.node.inj
              (regions := (dropInstantiationAtomsRaw result).regionCount) (by
              simpa [droppedParentForwardMap, droppedOutsideOccurrenceMap,
                leftRegion, rightRegion] using mapped)
          have originEq := congrArg (instantiationAtomDomain result).origin
            nodeEq
          rw [copyTrace.droppedNodeMap_origin,
            copyTrace.droppedNodeMap_origin] at originEq
          exact congrArg ConcreteElaboration.LocalOccurrence.node
            (copyTrace.nodeMap_injective originEq)
      | child rightChild =>
          simp [droppedParentForwardMap, droppedOutsideOccurrenceMap,
            leftRegion] at mapped
  | child leftChild =>
      cases right with
      | node rightNode =>
          have rightRegion :=
            (ConcreteElaboration.mem_localOccurrences_node input.val
              payload.parent rightNode).1 rightMember
          simp [droppedParentForwardMap, droppedOutsideOccurrenceMap,
            rightRegion] at mapped
      | child rightChild =>
          have childEq : copyTrace.regionMap leftChild =
              copyTrace.regionMap rightChild :=
            ConcreteElaboration.LocalOccurrence.child.inj
              (nodes := result.diagram.val.nodeCount) (by
              simpa [droppedParentForwardMap, droppedOutsideOccurrenceMap]
                using mapped)
          exact congrArg ConcreteElaboration.LocalOccurrence.child
            (copyTrace.regionMap_injective childEq)

@[simp] theorem droppedParentReverseMap_forward_of_mem
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
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    (original : ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount)
    (member : original ∈
      ConcreteElaboration.localOccurrences input.val payload.parent) :
    copyTrace.droppedParentReverseMap
        (copyTrace.droppedParentForwardMap original) = original := by
  classical
  let preimage : copyTrace.DroppedParentPreimage
      (copyTrace.droppedParentForwardMap original) :=
    ⟨original, member, rfl⟩
  rw [droppedParentReverseMap, dif_pos preimage]
  have chosenSpec := Classical.choose_spec preimage
  exact droppedParentForwardMap_injective_on_local copyTrace chosenSpec.1
    member chosenSpec.2

theorem droppedParent_localOccurrences_map_reverse
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
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result) :
    (ConcreteElaboration.localOccurrences (dropInstantiationAtomsRaw result)
        (copyTrace.regionMap payload.parent)).map
        copyTrace.droppedParentReverseMap =
      ConcreteElaboration.localOccurrences input.val payload.parent := by
  rw [copyTrace.dropped_localOccurrences_of_outside payload.parent
    (payload_bubble_not_encloses_parent payload)]
  let occurrences := ConcreteElaboration.localOccurrences input.val
    payload.parent
  change (occurrences.map copyTrace.droppedParentForwardMap).map
      copyTrace.droppedParentReverseMap = occurrences
  rw [List.map_map]
  calc
    occurrences.map
        (copyTrace.droppedParentReverseMap ∘
          copyTrace.droppedParentForwardMap) =
        occurrences.map id := by
      apply List.map_congr_left
      intro occurrence member
      exact copyTrace.droppedParentReverseMap_forward_of_mem occurrence member
    _ = occurrences := by
      induction occurrences with
      | nil => rfl
      | cons occurrence occurrences induction =>
          simp only [List.map_cons, id_eq]
          rw [induction]

@[simp] theorem droppedParentReverseMap_resultBubble
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
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result) :
    copyTrace.droppedParentReverseMap
        (.child result.bubble) = .child bubble := by
  have bubbleMember : ConcreteElaboration.LocalOccurrence.child bubble ∈
      ConcreteElaboration.localOccurrences input.val payload.parent :=
    (ConcreteElaboration.mem_localOccurrences_child input.val payload.parent
      bubble).2 (by simpa [payload.bubble_eq, CRegion.parent?])
  have mappedBubble : copyTrace.droppedParentForwardMap
      (.child bubble) = .child result.bubble := by
    change ConcreteElaboration.LocalOccurrence.child
      (copyTrace.regionMap bubble) = .child result.bubble
    exact congrArg ConcreteElaboration.LocalOccurrence.child
      copyTrace.regionMap_bubble
  rw [← mappedBubble]
  exact copyTrace.droppedParentReverseMap_forward_of_mem (.child bubble)
    bubbleMember

/-- Total final-focus occurrence map used for the kept frame partition. -/
noncomputable def finalFocusOccurrenceMap
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
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    {raw : ConcreteDiagram}
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw) :
    ConcreteElaboration.LocalOccurrence elimTrace.sourceDiagram.regionCount
        elimTrace.sourceDiagram.nodeCount →
      ConcreteElaboration.LocalOccurrence input.val.regionCount
        input.val.nodeCount :=
  copyTrace.droppedParentReverseMap ∘ elimTrace.occurrenceMap

/-- Every retained occurrence at the promoted focus has an exact original
parent occurrence whose forward image is its vacuous-elimination origin. -/
theorem keptOccurrence_original_preimage
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
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    {raw : ConcreteDiagram}
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (occurrence : ConcreteElaboration.LocalOccurrence
      elimTrace.sourceDiagram.regionCount elimTrace.sourceDiagram.nodeCount)
    (member : occurrence ∈ elimTrace.keptOccurrences finalWellFormed) :
    ∃ original,
      original ∈ ConcreteElaboration.localOccurrences input.val
        payload.parent ∧
      copyTrace.droppedParentForwardMap original =
        elimTrace.occurrenceMap occurrence ∧
      copyTrace.finalFocusOccurrenceMap elimTrace occurrence = original := by
  have droppedMember : elimTrace.occurrenceMap occurrence ∈
      ConcreteElaboration.localOccurrences (dropInstantiationAtomsRaw result)
        (copyTrace.regionMap payload.parent) := by
    cases occurrence with
    | node node =>
        have nodeRegion := elimTrace.kept_node_region finalWellFormed node member
        apply (ConcreteElaboration.mem_localOccurrences_node
          (dropInstantiationAtomsRaw result) (copyTrace.regionMap payload.parent)
          node).2
        simpa [copyTrace.regionMap_parent_eq_elimParent elimTrace] using
          nodeRegion
    | child child =>
        have childParent := elimTrace.kept_child_parent finalWellFormed child
          member
        apply (ConcreteElaboration.mem_localOccurrences_child
          (dropInstantiationAtomsRaw result) (copyTrace.regionMap payload.parent)
          (elimTrace.origin child)).2
        simpa [copyTrace.regionMap_parent_eq_elimParent elimTrace] using
          childParent
  rw [copyTrace.dropped_localOccurrences_of_outside payload.parent
    (payload_bubble_not_encloses_parent payload)] at droppedMember
  obtain ⟨original, originalMember, forwardEq⟩ := List.mem_map.mp droppedMember
  refine ⟨original, originalMember, forwardEq, ?_⟩
  rw [finalFocusOccurrenceMap, Function.comp_apply, ← forwardEq]
  exact copyTrace.droppedParentReverseMap_forward_of_mem original originalMember

theorem keptNode_original
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
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    {raw : ConcreteDiagram}
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (node : Fin elimTrace.sourceDiagram.nodeCount)
    (member : ConcreteElaboration.LocalOccurrence.node node ∈
      elimTrace.keptOccurrences finalWellFormed) :
    ∃ (originalNode : Fin input.val.nodeCount)
        (originalRegion : (input.val.nodes originalNode).region =
          payload.parent),
      copyTrace.finalFocusOccurrenceMap elimTrace (.node node) =
          .node originalNode ∧
      copyTrace.droppedNodeMap originalNode
          (fun enclosed => payload_bubble_not_encloses_parent payload
            (originalRegion ▸ enclosed)) = node := by
  obtain ⟨original, originalMember, forwardEq, reverseEq⟩ :=
    copyTrace.keptOccurrence_original_preimage elimTrace finalWellFormed
      (.node node) member
  cases original with
  | node originalNode =>
      have originalRegion :=
        (ConcreteElaboration.mem_localOccurrences_node input.val
          payload.parent originalNode).1 originalMember
      refine ⟨originalNode, originalRegion, reverseEq, ?_⟩
      exact ConcreteElaboration.LocalOccurrence.node.inj
        (regions := (dropInstantiationAtomsRaw result).regionCount) (by
          simpa [droppedParentForwardMap, droppedOutsideOccurrenceMap,
            originalRegion, VacuousElimTrace.occurrenceMap] using forwardEq)
  | child originalChild =>
      change ConcreteElaboration.LocalOccurrence.child
          (copyTrace.regionMap originalChild) =
        ConcreteElaboration.LocalOccurrence.node node at forwardEq
      cases forwardEq

theorem keptChild_original
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
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    {raw : ConcreteDiagram}
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (child : Fin elimTrace.sourceDiagram.regionCount)
    (member : ConcreteElaboration.LocalOccurrence.child child ∈
      elimTrace.keptOccurrences finalWellFormed) :
    ∃ originalChild,
      copyTrace.finalFocusOccurrenceMap elimTrace (.child child) =
          .child originalChild ∧
      (input.val.regions originalChild).parent? = some payload.parent := by
  obtain ⟨original, originalMember, forwardEq, reverseEq⟩ :=
    copyTrace.keptOccurrence_original_preimage elimTrace finalWellFormed
      (.child child) member
  cases original with
  | node originalNode =>
      have originalRegion :=
        (ConcreteElaboration.mem_localOccurrences_node input.val
          payload.parent originalNode).1 originalMember
      simp [droppedParentForwardMap, droppedOutsideOccurrenceMap,
        originalRegion, VacuousElimTrace.occurrenceMap] at forwardEq
  | child originalChild =>
      refine ⟨originalChild, reverseEq, ?_⟩
      exact (ConcreteElaboration.mem_localOccurrences_child input.val
        payload.parent originalChild).1 originalMember

/-- The final focus partitions into retained original-parent occurrences and
the selected block represented by the one original quantified-bubble child. -/
theorem finalFocusOccurrences_perm
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
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    {raw : ConcreteDiagram}
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature) :
    List.Perm
      ((elimTrace.keptOccurrences finalWellFormed).map
          (copyTrace.finalFocusOccurrenceMap elimTrace) ++
        [ConcreteElaboration.LocalOccurrence.child bubble])
      (ConcreteElaboration.localOccurrences input.val payload.parent) := by
  have promoted := elimTrace.targetFocusOccurrences_perm finalWellFormed
  have mapped := promoted.map copyTrace.droppedParentReverseMap
  rw [List.map_append, List.map_map] at mapped
  simp only [List.map_singleton,
    copyTrace.droppedParentReverseMap_resultBubble] at mapped
  change List.Perm
      ((elimTrace.keptOccurrences finalWellFormed).map
          (copyTrace.finalFocusOccurrenceMap elimTrace) ++
        [ConcreteElaboration.LocalOccurrence.child bubble])
      ((ConcreteElaboration.localOccurrences (dropInstantiationAtomsRaw result)
        elimTrace.parent).map copyTrace.droppedParentReverseMap) at mapped
  rw [← copyTrace.regionMap_parent_eq_elimParent elimTrace,
    copyTrace.droppedParent_localOccurrences_map_reverse] at mapped
  exact mapped

end InstantiationTrace

end VisualProof.Rule
