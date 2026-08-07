import VisualProof.Rule.Soundness.Comprehension.InstantiationFinalNodeCompiler

namespace VisualProof.Rule

open VisualProof.Concrete

open VisualProof
open VisualProof.Diagram

namespace InstantiationTrace

def droppedParentForwardMap
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result) :
    Concrete.Elaboration.LocalOccurrence input.val.regionCount input.val.nodeCount →
      Concrete.Elaboration.LocalOccurrence
        (dropInstantiationAtomsRaw result).regionCount
        (dropInstantiationAtomsRaw result).nodeCount :=
  copyTrace.droppedOutsideOccurrenceMap payload.parent
    (payload_bubble_not_encloses_parent payload)

def DroppedParentPreimage
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    (dropped : Concrete.Elaboration.LocalOccurrence
      (dropInstantiationAtomsRaw result).regionCount
      (dropInstantiationAtomsRaw result).nodeCount) : Prop :=
  ∃ original,
    original ∈ Concrete.Elaboration.localOccurrences input.val payload.parent ∧
      copyTrace.droppedParentForwardMap original = dropped

noncomputable def droppedParentReverseMap
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result) :
    Concrete.Elaboration.LocalOccurrence
        (dropInstantiationAtomsRaw result).regionCount
        (dropInstantiationAtomsRaw result).nodeCount →
      Concrete.Elaboration.LocalOccurrence input.val.regionCount
        input.val.nodeCount := fun dropped => by
  classical
  exact if preimage : copyTrace.DroppedParentPreimage dropped then
    Classical.choose preimage
  else .child payload.parent

private theorem droppedParentForwardMap_injective_on_local
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    {left right : Concrete.Elaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount}
    (leftMember : left ∈
      Concrete.Elaboration.localOccurrences input.val payload.parent)
    (rightMember : right ∈
      Concrete.Elaboration.localOccurrences input.val payload.parent)
    (mapped : copyTrace.droppedParentForwardMap left =
      copyTrace.droppedParentForwardMap right) :
    left = right := by
  cases left with
  | node leftNode =>
      have leftRegion :=
        (Concrete.Elaboration.mem_localOccurrences_node input.val payload.parent
          leftNode).1 leftMember
      cases right with
      | node rightNode =>
          have rightRegion :=
            (Concrete.Elaboration.mem_localOccurrences_node input.val
              payload.parent rightNode).1 rightMember
          have nodeEq : copyTrace.droppedNodeMap leftNode (fun enclosed =>
                payload_bubble_not_encloses_parent payload
                  (leftRegion ▸ enclosed)) =
              copyTrace.droppedNodeMap rightNode (fun enclosed =>
                payload_bubble_not_encloses_parent payload
                  (rightRegion ▸ enclosed)) := by
            exact Concrete.Elaboration.LocalOccurrence.node.inj
              (regions := (dropInstantiationAtomsRaw result).regionCount) (by
              simpa [droppedParentForwardMap, droppedOutsideOccurrenceMap,
                leftRegion, rightRegion] using mapped)
          have originEq := congrArg (instantiationAtomDomain result).origin
            nodeEq
          rw [copyTrace.droppedNodeMap_origin,
            copyTrace.droppedNodeMap_origin] at originEq
          exact congrArg Concrete.Elaboration.LocalOccurrence.node
            (copyTrace.nodeMap_injective originEq)
      | child rightChild =>
          simp [droppedParentForwardMap, droppedOutsideOccurrenceMap,
            leftRegion] at mapped
  | child leftChild =>
      cases right with
      | node rightNode =>
          have rightRegion :=
            (Concrete.Elaboration.mem_localOccurrences_node input.val
              payload.parent rightNode).1 rightMember
          simp [droppedParentForwardMap, droppedOutsideOccurrenceMap,
            rightRegion] at mapped
      | child rightChild =>
          have childEq : copyTrace.regionMap leftChild =
              copyTrace.regionMap rightChild :=
            Concrete.Elaboration.LocalOccurrence.child.inj
              (nodes := result.diagram.val.nodeCount) (by
              simpa [droppedParentForwardMap, droppedOutsideOccurrenceMap]
                using mapped)
          exact congrArg Concrete.Elaboration.LocalOccurrence.child
            (copyTrace.regionMap_injective childEq)

@[simp] theorem droppedParentReverseMap_forward_of_mem
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    (original : Concrete.Elaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount)
    (member : original ∈
      Concrete.Elaboration.localOccurrences input.val payload.parent) :
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
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result) :
    (Concrete.Elaboration.localOccurrences (dropInstantiationAtomsRaw result)
        (copyTrace.regionMap payload.parent)).map
        copyTrace.droppedParentReverseMap =
      Concrete.Elaboration.localOccurrences input.val payload.parent := by
  rw [copyTrace.dropped_localOccurrences_of_outside payload.parent
    (payload_bubble_not_encloses_parent payload)]
  let occurrences := Concrete.Elaboration.localOccurrences input.val
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
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result) :
    copyTrace.droppedParentReverseMap
        (.child result.bubble) = .child bubble := by
  have bubbleMember : Concrete.Elaboration.LocalOccurrence.child bubble ∈
      Concrete.Elaboration.localOccurrences input.val payload.parent :=
    (Concrete.Elaboration.mem_localOccurrences_child input.val payload.parent
      bubble).2 (by simpa [payload.bubble_eq, CRegion.parent?])
  have mappedBubble : copyTrace.droppedParentForwardMap
      (.child bubble) = .child result.bubble := by
    change Concrete.Elaboration.LocalOccurrence.child
      (copyTrace.regionMap bubble) = .child result.bubble
    exact congrArg Concrete.Elaboration.LocalOccurrence.child
      copyTrace.regionMap_bubble
  rw [← mappedBubble]
  exact copyTrace.droppedParentReverseMap_forward_of_mem (.child bubble)
    bubbleMember

/-- Total final-focus occurrence map used for the kept frame partition. -/
noncomputable def finalFocusOccurrenceMap
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    {raw : Concrete.Diagram}
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw) :
    Concrete.Elaboration.LocalOccurrence elimTrace.sourceDiagram.regionCount
        elimTrace.sourceDiagram.nodeCount →
      Concrete.Elaboration.LocalOccurrence input.val.regionCount
        input.val.nodeCount :=
  copyTrace.droppedParentReverseMap ∘ elimTrace.occurrenceMap

/-- Every retained occurrence at the promoted focus has an exact original
parent occurrence whose forward image is its vacuous-elimination origin. -/
theorem keptOccurrence_original_preimage
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    {raw : Concrete.Diagram}
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed )
    (occurrence : Concrete.Elaboration.LocalOccurrence
      elimTrace.sourceDiagram.regionCount elimTrace.sourceDiagram.nodeCount)
    (member : occurrence ∈ elimTrace.keptOccurrences finalWellFormed) :
    ∃ original,
      original ∈ Concrete.Elaboration.localOccurrences input.val
        payload.parent ∧
      copyTrace.droppedParentForwardMap original =
        elimTrace.occurrenceMap occurrence ∧
      copyTrace.finalFocusOccurrenceMap elimTrace occurrence = original := by
  have droppedMember : elimTrace.occurrenceMap occurrence ∈
      Concrete.Elaboration.localOccurrences (dropInstantiationAtomsRaw result)
        (copyTrace.regionMap payload.parent) := by
    cases occurrence with
    | node node =>
        have nodeRegion := elimTrace.kept_node_region finalWellFormed node member
        apply (Concrete.Elaboration.mem_localOccurrences_node
          (dropInstantiationAtomsRaw result) (copyTrace.regionMap payload.parent)
          node).2
        simpa [copyTrace.regionMap_parent_eq_elimParent elimTrace] using
          nodeRegion
    | child child =>
        have childParent := elimTrace.kept_child_parent finalWellFormed child
          member
        apply (Concrete.Elaboration.mem_localOccurrences_child
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
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    {raw : Concrete.Diagram}
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed )
    (node : Fin elimTrace.sourceDiagram.nodeCount)
    (member : Concrete.Elaboration.LocalOccurrence.node node ∈
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
        (Concrete.Elaboration.mem_localOccurrences_node input.val
          payload.parent originalNode).1 originalMember
      refine ⟨originalNode, originalRegion, reverseEq, ?_⟩
      exact Concrete.Elaboration.LocalOccurrence.node.inj
        (regions := (dropInstantiationAtomsRaw result).regionCount) (by
          simpa [droppedParentForwardMap, droppedOutsideOccurrenceMap,
            originalRegion, VacuousElimTrace.occurrenceMap] using forwardEq)
  | child originalChild =>
      change Concrete.Elaboration.LocalOccurrence.child
          (copyTrace.regionMap originalChild) =
        Concrete.Elaboration.LocalOccurrence.node node at forwardEq
      cases forwardEq

theorem keptChild_original
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    {raw : Concrete.Diagram}
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed )
    (child : Fin elimTrace.sourceDiagram.regionCount)
    (member : Concrete.Elaboration.LocalOccurrence.child child ∈
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
        (Concrete.Elaboration.mem_localOccurrences_node input.val
          payload.parent originalNode).1 originalMember
      simp [droppedParentForwardMap, droppedOutsideOccurrenceMap,
        originalRegion, VacuousElimTrace.occurrenceMap] at forwardEq
  | child originalChild =>
      refine ⟨originalChild, reverseEq, ?_⟩
      exact (Concrete.Elaboration.mem_localOccurrences_child input.val
        payload.parent originalChild).1 originalMember

theorem keptChild_finalFocus_eq_reverse
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    {raw : Concrete.Diagram}
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed )
    (child : Fin elimTrace.sourceDiagram.regionCount)
    (member : Concrete.Elaboration.LocalOccurrence.child child ∈
      elimTrace.keptOccurrences finalWellFormed) :
    copyTrace.finalFocusOccurrenceMap elimTrace (.child child) =
      .child (copyTrace.reverseRegionMap elimTrace finalWellFormed child) := by
  obtain ⟨original, originalMember, forwardEq, reverseEq⟩ :=
    copyTrace.keptOccurrence_original_preimage elimTrace finalWellFormed
      (.child child) member
  cases original with
  | node originalNode =>
      have originalRegion :=
        (Concrete.Elaboration.mem_localOccurrences_node input.val
          payload.parent originalNode).1 originalMember
      simp [droppedParentForwardMap, droppedOutsideOccurrenceMap,
        originalRegion, VacuousElimTrace.occurrenceMap] at forwardEq
  | child originalChild =>
      have childParent :=
        (Concrete.Elaboration.mem_localOccurrences_child input.val
          payload.parent originalChild).1 originalMember
      have mappedOrigin : copyTrace.regionMap originalChild =
          elimTrace.origin child := by
        exact Concrete.Elaboration.LocalOccurrence.child.inj
          (nodes := result.diagram.val.nodeCount) (by
            simpa [droppedParentForwardMap, droppedOutsideOccurrenceMap,
              VacuousElimTrace.occurrenceMap] using forwardEq)
      have childNeBubble : originalChild ≠ bubble := by
        intro childBubble
        subst originalChild
        apply elimTrace.origin_ne_bubble child
        exact mappedOrigin.symm.trans copyTrace.regionMap_bubble
      have finalChild : copyTrace.finalRegionMap elimTrace finalWellFormed
          originalChild = child := by
        apply elimTrace.origin_injective
        rw [copyTrace.origin_finalRegionMap_of_ne_bubble elimTrace
          finalWellFormed originalChild childNeBubble]
        exact mappedOrigin
      have childNeParent : originalChild ≠ payload.parent := by
        intro childParentEq
        subst originalChild
        exact (Concrete.Elaboration.checked_direct_child_not_encloses_parent
          input.property childParent)
          (Concrete.Diagram.Encloses.refl input.val payload.parent)
      have childRegular : FrameRegular payload originalChild := by
        constructor
        · intro bubbleEncloses
          rcases Concrete.Elaboration.encloses_direct_child childParent
              bubbleEncloses with bubbleChild | bubbleParent
          · exact childNeBubble bubbleChild.symm
          · exact payload_bubble_not_encloses_parent payload bubbleParent
        · exact childNeParent
      have reverseChild := copyTrace.reverseRegionMap_finalRegionMap elimTrace
        finalWellFormed originalChild childRegular
      rw [finalChild] at reverseChild
      rw [reverseEq, reverseChild]

/-- The final focus partitions into retained original-parent occurrences and
the selected block represented by the one original quantified-bubble child. -/
theorem finalFocusOccurrences_perm
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    {raw : Concrete.Diagram}
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed ) :
    List.Perm
      ((elimTrace.keptOccurrences finalWellFormed).map
          (copyTrace.finalFocusOccurrenceMap elimTrace) ++
        [Concrete.Elaboration.LocalOccurrence.child bubble])
      (Concrete.Elaboration.localOccurrences input.val payload.parent) := by
  have promoted := elimTrace.targetFocusOccurrences_perm finalWellFormed
  have mapped := promoted.map copyTrace.droppedParentReverseMap
  rw [List.map_append, List.map_map] at mapped
  simp only [List.map_singleton,
    copyTrace.droppedParentReverseMap_resultBubble] at mapped
  change List.Perm
      ((elimTrace.keptOccurrences finalWellFormed).map
          (copyTrace.finalFocusOccurrenceMap elimTrace) ++
        [Concrete.Elaboration.LocalOccurrence.child bubble])
      ((Concrete.Elaboration.localOccurrences (dropInstantiationAtomsRaw result)
        elimTrace.parent).map copyTrace.droppedParentReverseMap) at mapped
  rw [← copyTrace.regionMap_parent_eq_elimParent elimTrace,
    copyTrace.droppedParent_localOccurrences_map_reverse] at mapped
  exact mapped

end InstantiationTrace

end VisualProof.Rule
