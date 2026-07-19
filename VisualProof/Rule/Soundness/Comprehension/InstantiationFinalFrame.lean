import VisualProof.Rule.Soundness.Comprehension.InstantiationFinalMaps

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram

namespace InstantiationTrace

/-- A copied region can be the final moving bubble only when it was the
original quantified bubble. -/
theorem regionMap_ne_result_bubble
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
    (region : Fin input.val.regionCount)
    (notBubble : region ≠ bubble) :
    copyTrace.regionMap region ≠ result.bubble := by
  intro mapped
  have bubbleMap := copyTrace.regionMap_bubble
  change copyTrace.regionMap bubble = result.bubble at bubbleMap
  exact notBubble (copyTrace.regionMap_injective (mapped.trans bubbleMap.symm))

/-- Away from the deleted bubble, the composite final region map has the
expected copy-trace origin. -/
theorem origin_finalRegionMap_of_ne_bubble
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
    (region : Fin input.val.regionCount)
    (notBubble : region ≠ bubble) :
    elimTrace.origin
        (copyTrace.finalRegionMap elimTrace finalWellFormed region) =
      copyTrace.regionMap region := by
  unfold finalRegionMap
  exact elimTrace.origin_liftRegion_of_ne finalWellFormed
    (copyTrace.regionMap region)
    (copyTrace.regionMap_ne_result_bubble region notBubble)

/-- The copy trace preserves the direct-parent relation of every original
frame child through the post-copy atom compaction. -/
theorem dropped_region_parent
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
    (child parent : Fin input.val.regionCount)
    (childParent : (input.val.regions child).parent? = some parent) :
    ((dropInstantiationAtomsRaw result).regions
        (copyTrace.regionMap child)).parent? =
      some (copyTrace.regionMap parent) := by
  rw [copyTrace.dropped_region_shape child]
  cases shape : input.val.regions child with
  | sheet =>
      rw [shape] at childParent
      cases childParent
  | cut originalParent =>
      have ownerEq : originalParent = parent := by
        rw [shape] at childParent
        exact Option.some.inj childParent
      subst originalParent
      rfl
  | bubble originalParent arity =>
      have ownerEq : originalParent = parent := by
        rw [shape] at childParent
        exact Option.some.inj childParent
      subst originalParent
      rfl

/-- Every child of a regular source region remains a child of the mapped
regular region after copying, atom compaction, and vacuous promotion. -/
theorem final_region_parent_of_regular
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
    (parent child : Fin input.val.regionCount)
    (regular : ¬ input.val.Encloses payload.parent parent)
    (childParent : (input.val.regions child).parent? = some parent) :
    (elimTrace.sourceDiagram.regions
        (copyTrace.finalRegionMap elimTrace finalWellFormed child)).parent? =
      some (copyTrace.finalRegionMap elimTrace finalWellFormed parent) := by
  have parentNeBubble : parent ≠ bubble := by
    intro equal
    subst parent
    exact regular (payload_parent_encloses_bubble payload)
  have childNeBubble : child ≠ bubble := by
    intro equal
    subst child
    have direct := childParent
    rw [payload.bubble_eq] at direct
    have parentEq : payload.parent = parent := by
      exact Option.some.inj (by simpa [CRegion.parent?] using direct)
    subst parent
    exact regular (ConcreteDiagram.Encloses.refl input.val payload.parent)
  have mappedParentRegular :=
    copyTrace.finalRegionMap_ne_targetIndex_of_not_enclosed elimTrace
      finalWellFormed parent regular
  have originParent := copyTrace.origin_finalRegionMap_of_ne_bubble elimTrace
    finalWellFormed parent parentNeBubble
  have originChild := copyTrace.origin_finalRegionMap_of_ne_bubble elimTrace
    finalWellFormed child childNeBubble
  have droppedParent := copyTrace.dropped_region_parent child parent childParent
  have promotedParent :
      (elimTrace.promotion.regions
          (copyTrace.finalRegionMap elimTrace finalWellFormed child)).parent? =
        some (copyTrace.finalRegionMap elimTrace finalWellFormed parent) := by
    apply (elimTrace.promotedRegion_parent_eq_regular_iff finalWellFormed
      (copyTrace.finalRegionMap elimTrace finalWellFormed child)
      (copyTrace.finalRegionMap elimTrace finalWellFormed parent)
      mappedParentRegular).2
    simpa only [originChild, originParent] using droppedParent
  exact promotedParent

/-- Outside the quantified parent subtree, the complete operational trace
preserves each direct child constructor and maps its parent through the
composite final region map. -/
theorem final_region_shape_of_regular
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
    (parent : Fin input.val.regionCount)
    (regular : ¬ input.val.Encloses payload.parent parent)
    (child : Fin input.val.regionCount)
    (childParent : (input.val.regions child).parent? = some parent) :
    elimTrace.sourceDiagram.regions
        (copyTrace.finalRegionMap elimTrace finalWellFormed child) =
      match input.val.regions child with
      | .sheet => .sheet
      | .cut childParent =>
          .cut (copyTrace.finalRegionMap elimTrace finalWellFormed childParent)
      | .bubble childParent arity =>
          .bubble
            (copyTrace.finalRegionMap elimTrace finalWellFormed childParent)
            arity := by
  have parentNeBubble : parent ≠ bubble := by
    intro equal
    subst parent
    exact regular (payload_parent_encloses_bubble payload)
  have childNeBubble : child ≠ bubble := by
    intro equal
    subst child
    have direct := childParent
    rw [payload.bubble_eq] at direct
    have parentEq : payload.parent = parent := by
      exact Option.some.inj (by simpa [CRegion.parent?] using direct)
    subst parent
    exact regular (ConcreteDiagram.Encloses.refl input.val payload.parent)
  have mappedParentRegular :=
    copyTrace.finalRegionMap_ne_targetIndex_of_not_enclosed elimTrace
      finalWellFormed parent regular
  have originParent := copyTrace.origin_finalRegionMap_of_ne_bubble elimTrace
    finalWellFormed parent parentNeBubble
  have originChild := copyTrace.origin_finalRegionMap_of_ne_bubble elimTrace
    finalWellFormed child childNeBubble
  have finalParent := copyTrace.final_region_parent_of_regular elimTrace
    finalWellFormed parent child regular childParent
  have promotedShape := elimTrace.regular_regionShape finalWellFormed
    (copyTrace.finalRegionMap elimTrace finalWellFormed parent)
    mappedParentRegular
    (copyTrace.finalRegionMap elimTrace finalWellFormed child)
    finalParent
  rw [originChild, originParent] at promotedShape
  have copiedShape := copyTrace.dropped_region_shape child
  cases sourceShape : input.val.regions child with
  | sheet =>
      rw [sourceShape] at childParent
      cases childParent
  | cut originalParent =>
      have originalParentEq : originalParent = parent := by
        rw [sourceShape] at childParent
        exact Option.some.inj childParent
      subst originalParent
      rw [sourceShape] at copiedShape
      simp only [mapRegionShape] at copiedShape
      cases targetShape : elimTrace.sourceDiagram.regions
          (copyTrace.finalRegionMap elimTrace finalWellFormed child) with
      | sheet =>
          rw [targetShape] at finalParent
          cases finalParent
      | cut targetParent =>
          have targetParentEq : targetParent =
              copyTrace.finalRegionMap elimTrace finalWellFormed parent := by
            rw [targetShape] at finalParent
            exact Option.some.inj finalParent
          subst targetParent
          simpa [sourceShape] using targetShape
      | bubble targetParent targetArity =>
          have targetShape' : elimTrace.promotion.regions
              (copyTrace.finalRegionMap elimTrace finalWellFormed child) =
                .bubble targetParent targetArity := targetShape
          rw [targetShape'] at promotedShape
          rw [copiedShape] at promotedShape
          cases promotedShape
  | bubble originalParent sourceArity =>
      have originalParentEq : originalParent = parent := by
        rw [sourceShape] at childParent
        exact Option.some.inj childParent
      subst originalParent
      rw [sourceShape] at copiedShape
      simp only [mapRegionShape] at copiedShape
      cases targetShape : elimTrace.sourceDiagram.regions
          (copyTrace.finalRegionMap elimTrace finalWellFormed child) with
      | sheet =>
          rw [targetShape] at finalParent
          cases finalParent
      | cut targetParent =>
          have targetShape' : elimTrace.promotion.regions
              (copyTrace.finalRegionMap elimTrace finalWellFormed child) =
                .cut targetParent := targetShape
          rw [targetShape'] at promotedShape
          rw [copiedShape] at promotedShape
          cases promotedShape
      | bubble targetParent targetArity =>
          have targetParentEq : targetParent =
              copyTrace.finalRegionMap elimTrace finalWellFormed parent := by
            rw [targetShape] at finalParent
            exact Option.some.inj finalParent
          have arityEq : targetArity = sourceArity := by
            have targetShape' : elimTrace.promotion.regions
                (copyTrace.finalRegionMap elimTrace finalWellFormed child) =
                  .bubble targetParent targetArity := targetShape
            rw [targetShape'] at promotedShape
            rw [copiedShape] at promotedShape
            exact (CRegion.bubble.inj promotedShape).2.symm
          subst targetParent
          subst targetArity
          simpa [sourceShape] using targetShape

/-- A node owned by a regular region lies outside the quantified bubble and
therefore survives the executor's post-copy atom compaction. -/
theorem node_outside_bubble_of_regular
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    (region : Fin input.val.regionCount)
    (regular : ¬ input.val.Encloses payload.parent region)
    (node : Fin input.val.nodeCount)
    (nodeRegion : (input.val.nodes node).region = region) :
    ¬ input.val.Encloses bubble (input.val.nodes node).region := by
  intro enclosed
  apply regular
  rw [nodeRegion] at enclosed
  exact ConcreteElaboration.checked_encloses_trans input.property
    (payload_parent_encloses_bubble payload) enclosed

/-- Dense final node index of an original node known to lie outside the
quantified bubble.  Vacuous promotion preserves the compacted node carrier. -/
def finalNodeMap
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
    (node : Fin input.val.nodeCount)
    (outside : ¬ input.val.Encloses bubble (input.val.nodes node).region) :
    Fin elimTrace.sourceDiagram.nodeCount :=
  copyTrace.droppedNodeMap node outside

/-- The composite node map sends every node owned by a regular region to the
mapped regular region. -/
theorem finalNodeMap_region
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
    (region : Fin input.val.regionCount)
    (regular : ¬ input.val.Encloses payload.parent region)
    (node : Fin input.val.nodeCount)
    (nodeRegion : (input.val.nodes node).region = region) :
    (elimTrace.sourceDiagram.nodes
      (copyTrace.finalNodeMap elimTrace node
        (node_outside_bubble_of_regular payload region regular node
          nodeRegion))).region =
      copyTrace.finalRegionMap elimTrace finalWellFormed region := by
  let outside := node_outside_bubble_of_regular payload region regular node
    nodeRegion
  have regionNeBubble : region ≠ bubble := by
    intro equal
    exact regular (by
      simpa [equal] using payload_parent_encloses_bubble payload)
  have originRegion := copyTrace.origin_finalRegionMap_of_ne_bubble elimTrace
    finalWellFormed region regionNeBubble
  have droppedShape := copyTrace.dropped_node_shape node outside
  have droppedRegion :
      ((dropInstantiationAtomsRaw result).nodes
        (copyTrace.droppedNodeMap node outside)).region =
      copyTrace.regionMap region := by
    rw [droppedShape]
    cases shape : input.val.nodes node <;>
      simp only [shape, mapNodeShape, CNode.region] at nodeRegion ⊢ <;>
      exact congrArg copyTrace.regionMap nodeRegion
  apply (elimTrace.promotedNode_region_eq_regular_iff finalWellFormed
    (copyTrace.droppedNodeMap node outside)
    (copyTrace.finalRegionMap elimTrace finalWellFormed region)
    (copyTrace.finalRegionMap_ne_targetIndex_of_not_enclosed elimTrace
      finalWellFormed region regular)).2
  simpa only [originRegion] using droppedRegion

/-- Retained nodes in regular regions preserve their complete constructor,
including atom binders transported through the composite region map. -/
theorem final_node_shape_of_regular
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
    (region : Fin input.val.regionCount)
    (regular : ¬ input.val.Encloses payload.parent region)
    (node : Fin input.val.nodeCount)
    (nodeRegion : (input.val.nodes node).region = region) :
    let outside := node_outside_bubble_of_regular payload region regular node
      nodeRegion
    elimTrace.sourceDiagram.nodes
        (copyTrace.finalNodeMap elimTrace node outside) =
      match input.val.nodes node with
      | .term owner freePorts term =>
          .term (copyTrace.finalRegionMap elimTrace finalWellFormed owner)
            freePorts term
      | .atom owner binder =>
          .atom (copyTrace.finalRegionMap elimTrace finalWellFormed owner)
            (copyTrace.finalRegionMap elimTrace finalWellFormed binder)
      | .named owner definition arity =>
          .named (copyTrace.finalRegionMap elimTrace finalWellFormed owner)
            definition arity := by
  dsimp only
  let outside := node_outside_bubble_of_regular payload region regular node
    nodeRegion
  have regionNeBubble : region ≠ bubble := by
    intro equal
    exact regular (by
      simpa [equal] using payload_parent_encloses_bubble payload)
  have originRegion := copyTrace.origin_finalRegionMap_of_ne_bubble elimTrace
    finalWellFormed region regionNeBubble
  have mappedRegular :=
    copyTrace.finalRegionMap_ne_targetIndex_of_not_enclosed elimTrace
      finalWellFormed region regular
  have finalOwner := copyTrace.finalNodeMap_region elimTrace finalWellFormed
    region regular node nodeRegion
  have promotedShape := elimTrace.regular_nodeShape finalWellFormed
    (copyTrace.finalRegionMap elimTrace finalWellFormed region) mappedRegular
    (copyTrace.droppedNodeMap node outside) finalOwner
  have droppedShape := copyTrace.dropped_node_shape node outside
  cases sourceShape : input.val.nodes node with
  | term sourceOwner sourceFreePorts sourceTerm =>
      have sourceOwnerEq : sourceOwner = region := by
        rw [sourceShape] at nodeRegion
        exact nodeRegion
      subst sourceOwner
      rw [sourceShape] at droppedShape
      simp only [mapNodeShape] at droppedShape
      cases targetShape : elimTrace.sourceDiagram.nodes
          (copyTrace.finalNodeMap elimTrace node outside) with
      | term targetOwner targetFreePorts targetTerm =>
          have targetOwnerEq : targetOwner =
              copyTrace.finalRegionMap elimTrace finalWellFormed region := by
            rw [targetShape] at finalOwner
            exact finalOwner
          subst targetOwner
          have targetShape' : elimTrace.promotion.nodes
              (copyTrace.droppedNodeMap node outside) =
                .term (copyTrace.finalRegionMap elimTrace finalWellFormed region)
                  targetFreePorts targetTerm := targetShape
          rw [targetShape'] at promotedShape
          simp only at promotedShape
          rw [originRegion] at promotedShape
          rw [droppedShape] at promotedShape
          cases promotedShape
          simpa [sourceShape] using targetShape
      | atom targetOwner targetBinder =>
          have targetShape' : elimTrace.promotion.nodes
              (copyTrace.droppedNodeMap node outside) =
                .atom targetOwner targetBinder := targetShape
          rw [targetShape'] at promotedShape
          rw [droppedShape] at promotedShape
          cases promotedShape
      | named targetOwner targetDefinition targetArity =>
          have targetShape' : elimTrace.promotion.nodes
              (copyTrace.droppedNodeMap node outside) =
                .named targetOwner targetDefinition targetArity := targetShape
          rw [targetShape'] at promotedShape
          rw [droppedShape] at promotedShape
          cases promotedShape
  | atom sourceOwner sourceBinder =>
      have sourceOwnerEq : sourceOwner = region := by
        rw [sourceShape] at nodeRegion
        exact nodeRegion
      subst sourceOwner
      have binderNeBubble : sourceBinder ≠ bubble := by
        intro equal
        have binderEncloses := input.property.atom_binders_enclose node
        rw [sourceShape, equal] at binderEncloses
        apply regular
        exact ConcreteElaboration.checked_encloses_trans input.property
          (payload_parent_encloses_bubble payload) binderEncloses
      have mappedBinderOrigin :=
        copyTrace.origin_finalRegionMap_of_ne_bubble elimTrace finalWellFormed
          sourceBinder binderNeBubble
      rw [sourceShape] at droppedShape
      simp only [mapNodeShape] at droppedShape
      cases targetShape : elimTrace.sourceDiagram.nodes
          (copyTrace.finalNodeMap elimTrace node outside) with
      | term targetOwner targetFreePorts targetTerm =>
          have targetShape' : elimTrace.promotion.nodes
              (copyTrace.droppedNodeMap node outside) =
                .term targetOwner targetFreePorts targetTerm := targetShape
          rw [targetShape'] at promotedShape
          rw [droppedShape] at promotedShape
          cases promotedShape
      | atom targetOwner targetBinder =>
          have targetOwnerEq : targetOwner =
              copyTrace.finalRegionMap elimTrace finalWellFormed region := by
            rw [targetShape] at finalOwner
            exact finalOwner
          subst targetOwner
          have targetShape' : elimTrace.promotion.nodes
              (copyTrace.droppedNodeMap node outside) =
                .atom (copyTrace.finalRegionMap elimTrace finalWellFormed region)
                  targetBinder := targetShape
          rw [targetShape'] at promotedShape
          simp only at promotedShape
          rw [originRegion] at promotedShape
          have shapeEq := droppedShape.symm.trans promotedShape
          injection shapeEq with _ binderOrigin
          have targetBinderEq : targetBinder =
              copyTrace.finalRegionMap elimTrace finalWellFormed sourceBinder :=
            elimTrace.origin_injective
              (binderOrigin.symm.trans mappedBinderOrigin.symm)
          subst targetBinder
          simpa [sourceShape] using targetShape
      | named targetOwner targetDefinition targetArity =>
          have targetShape' : elimTrace.promotion.nodes
              (copyTrace.droppedNodeMap node outside) =
                .named targetOwner targetDefinition targetArity := targetShape
          rw [targetShape'] at promotedShape
          rw [droppedShape] at promotedShape
          cases promotedShape
  | named sourceOwner sourceDefinition sourceArity =>
      have sourceOwnerEq : sourceOwner = region := by
        rw [sourceShape] at nodeRegion
        exact nodeRegion
      subst sourceOwner
      rw [sourceShape] at droppedShape
      simp only [mapNodeShape] at droppedShape
      cases targetShape : elimTrace.sourceDiagram.nodes
          (copyTrace.finalNodeMap elimTrace node outside) with
      | term targetOwner targetFreePorts targetTerm =>
          have targetShape' : elimTrace.promotion.nodes
              (copyTrace.droppedNodeMap node outside) =
                .term targetOwner targetFreePorts targetTerm := targetShape
          rw [targetShape'] at promotedShape
          rw [droppedShape] at promotedShape
          cases promotedShape
      | atom targetOwner targetBinder =>
          have targetShape' : elimTrace.promotion.nodes
              (copyTrace.droppedNodeMap node outside) =
                .atom targetOwner targetBinder := targetShape
          rw [targetShape'] at promotedShape
          rw [droppedShape] at promotedShape
          cases promotedShape
      | named targetOwner targetDefinition targetArity =>
          have targetOwnerEq : targetOwner =
              copyTrace.finalRegionMap elimTrace finalWellFormed region := by
            rw [targetShape] at finalOwner
            exact finalOwner
          subst targetOwner
          have targetShape' : elimTrace.promotion.nodes
              (copyTrace.droppedNodeMap node outside) =
                .named (copyTrace.finalRegionMap elimTrace finalWellFormed region)
                  targetDefinition targetArity := targetShape
          rw [targetShape'] at promotedShape
          simp only at promotedShape
          rw [originRegion] at promotedShape
          rw [droppedShape] at promotedShape
          cases promotedShape
          simpa [sourceShape] using targetShape

end InstantiationTrace

end VisualProof.Rule
