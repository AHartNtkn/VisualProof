import VisualProof.Rule.Soundness.Comprehension.InstantiationFinalFocusedOccurrences

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationTrace

theorem reverseRegionMap_finalRegionMap_of_enclosing_parent
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
    (encloses : input.val.Encloses region payload.parent) :
    copyTrace.reverseRegionMap elimTrace finalWellFormed
        (copyTrace.finalRegionMap elimTrace finalWellFormed region) = region := by
  by_cases atFocus : region = payload.parent
  · subst region
    rw [copyTrace.finalRegionMap_parent elimTrace finalWellFormed]
    exact copyTrace.reverseRegionMap_targetIndex elimTrace finalWellFormed
  · have regular : FrameRegular payload region := by
      constructor
      · intro bubbleEncloses
        exact payload_bubble_not_encloses_parent payload
          (ConcreteElaboration.checked_encloses_trans input.property
            bubbleEncloses encloses)
      · exact atFocus
    exact copyTrace.reverseRegionMap_finalRegionMap elimTrace finalWellFormed
      region regular

theorem focusedKeptNode_shape
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
    (finalNode : Fin elimTrace.sourceDiagram.nodeCount)
    (member : ConcreteElaboration.LocalOccurrence.node finalNode ∈
      elimTrace.keptOccurrences finalWellFormed)
    (originalNode : Fin input.val.nodeCount)
    (originalRegion : (input.val.nodes originalNode).region = payload.parent)
    (droppedEq : copyTrace.droppedNodeMap originalNode
      (fun enclosed => payload_bubble_not_encloses_parent payload
        (originalRegion ▸ enclosed)) = finalNode) :
    input.val.nodes originalNode =
      match elimTrace.sourceDiagram.nodes finalNode with
      | .term owner freePorts term =>
          .term (copyTrace.reverseRegionMap elimTrace finalWellFormed owner)
            freePorts term
      | .atom owner binder =>
          .atom (copyTrace.reverseRegionMap elimTrace finalWellFormed owner)
            (copyTrace.reverseRegionMap elimTrace finalWellFormed binder)
      | .named owner definition arity =>
          .named (copyTrace.reverseRegionMap elimTrace finalWellFormed owner)
            definition arity := by
  let outside := fun enclosed => payload_bubble_not_encloses_parent payload
    (originalRegion ▸ enclosed)
  have finalOwner :
      (elimTrace.sourceDiagram.nodes finalNode).region =
        elimTrace.targetIndex finalWellFormed :=
    (ConcreteElaboration.mem_localOccurrences_node elimTrace.sourceDiagram
      (elimTrace.targetIndex finalWellFormed) finalNode).1
      (List.mem_filter.mp member).1
  have droppedShape := copyTrace.dropped_node_shape originalNode outside
  have droppedOwner : ((dropInstantiationAtomsRaw result).nodes
      (copyTrace.droppedNodeMap originalNode outside)).region =
        copyTrace.regionMap payload.parent := by
    rw [droppedShape]
    cases shape : input.val.nodes originalNode <;>
      simp only [shape, mapNodeShape, CNode.region] at originalRegion ⊢ <;>
      exact congrArg copyTrace.regionMap originalRegion
  have promotedShape := elimTrace.focused_nodeShape
    (copyTrace.droppedNodeMap originalNode outside)
    (copyTrace.regionMap payload.parent) droppedOwner
  cases originalShape : input.val.nodes originalNode with
  | term owner freePorts term =>
      have ownerEq : owner = payload.parent := by
        simpa [originalShape, CNode.region] using originalRegion
      subst owner
      rw [originalShape] at droppedShape
      simp only [mapNodeShape] at droppedShape
      cases finalShape : elimTrace.sourceDiagram.nodes finalNode with
      | term finalOwner' finalFreePorts finalTerm =>
          have finalOwnerEq : finalOwner' =
              elimTrace.targetIndex finalWellFormed := by
            simpa [finalShape, CNode.region] using finalOwner
          subst finalOwner'
          have finalShapeDropped : elimTrace.promotion.nodes
              (copyTrace.droppedNodeMap originalNode outside) =
                .term (elimTrace.targetIndex finalWellFormed) finalFreePorts
                  finalTerm := by
            rw [droppedEq]
            exact finalShape
          simp only [CNode.region] at finalOwner
          rw [finalShapeDropped, droppedShape] at promotedShape
          cases promotedShape
          simp [copyTrace.reverseRegionMap_targetIndex elimTrace
            finalWellFormed, finalOwner]
      | atom finalOwner' finalBinder =>
          have finalOwnerEq : finalOwner' =
              elimTrace.targetIndex finalWellFormed := by
            simpa [finalShape, CNode.region] using finalOwner
          subst finalOwner'
          have finalShapeDropped : elimTrace.promotion.nodes
              (copyTrace.droppedNodeMap originalNode outside) =
                .atom (elimTrace.targetIndex finalWellFormed) finalBinder := by
            rw [droppedEq]
            exact finalShape
          rw [finalShapeDropped, droppedShape] at promotedShape
          cases promotedShape
      | named finalOwner' finalDefinition finalArity =>
          have finalOwnerEq : finalOwner' =
              elimTrace.targetIndex finalWellFormed := by
            simpa [finalShape, CNode.region] using finalOwner
          subst finalOwner'
          have finalShapeDropped : elimTrace.promotion.nodes
              (copyTrace.droppedNodeMap originalNode outside) =
                .named (elimTrace.targetIndex finalWellFormed) finalDefinition
                  finalArity := by
            rw [droppedEq]
            exact finalShape
          rw [finalShapeDropped, droppedShape] at promotedShape
          cases promotedShape
  | atom owner binder =>
      have ownerEq : owner = payload.parent := by
        simpa [originalShape, CNode.region] using originalRegion
      subst owner
      have binderEncloses : input.val.Encloses binder payload.parent := by
        simpa [originalShape] using input.property.atom_binders_enclose
          originalNode
      have binderNeBubble : binder ≠ bubble := by
        intro binderBubble
        subst binder
        exact payload_bubble_not_encloses_parent payload binderEncloses
      have binderOrigin := copyTrace.origin_finalRegionMap_of_ne_bubble
        elimTrace finalWellFormed binder binderNeBubble
      rw [originalShape] at droppedShape
      simp only [mapNodeShape] at droppedShape
      cases finalShape : elimTrace.sourceDiagram.nodes finalNode with
      | term finalOwner' finalFreePorts finalTerm =>
          have finalOwnerEq : finalOwner' =
              elimTrace.targetIndex finalWellFormed := by
            simpa [finalShape, CNode.region] using finalOwner
          subst finalOwner'
          have finalShapeDropped : elimTrace.promotion.nodes
              (copyTrace.droppedNodeMap originalNode outside) =
                .term (elimTrace.targetIndex finalWellFormed) finalFreePorts
                  finalTerm := by
            rw [droppedEq]
            exact finalShape
          rw [finalShapeDropped, droppedShape] at promotedShape
          cases promotedShape
      | atom finalOwner' finalBinder =>
          have finalOwnerEq : finalOwner' =
              elimTrace.targetIndex finalWellFormed := by
            simpa [finalShape, CNode.region] using finalOwner
          subst finalOwner'
          have finalShapeDropped : elimTrace.promotion.nodes
              (copyTrace.droppedNodeMap originalNode outside) =
                .atom (elimTrace.targetIndex finalWellFormed) finalBinder := by
            rw [droppedEq]
            exact finalShape
          simp only [CNode.region] at finalOwner
          rw [finalShapeDropped, droppedShape] at promotedShape
          have finalBinderEq : finalBinder =
              copyTrace.finalRegionMap elimTrace finalWellFormed binder := by
            apply elimTrace.origin_injective
            exact (CNode.atom.inj promotedShape).2.symm.trans binderOrigin.symm
          subst finalBinder
          simp [copyTrace.reverseRegionMap_targetIndex elimTrace
            finalWellFormed, finalOwner,
            copyTrace.reverseRegionMap_finalRegionMap_of_enclosing_parent
              elimTrace finalWellFormed binder binderEncloses]
      | named finalOwner' finalDefinition finalArity =>
          have finalOwnerEq : finalOwner' =
              elimTrace.targetIndex finalWellFormed := by
            simpa [finalShape, CNode.region] using finalOwner
          subst finalOwner'
          have finalShapeDropped : elimTrace.promotion.nodes
              (copyTrace.droppedNodeMap originalNode outside) =
                .named (elimTrace.targetIndex finalWellFormed) finalDefinition
                  finalArity := by
            rw [droppedEq]
            exact finalShape
          rw [finalShapeDropped, droppedShape] at promotedShape
          cases promotedShape
  | named owner definition arity =>
      have ownerEq : owner = payload.parent := by
        simpa [originalShape, CNode.region] using originalRegion
      subst owner
      rw [originalShape] at droppedShape
      simp only [mapNodeShape] at droppedShape
      cases finalShape : elimTrace.sourceDiagram.nodes finalNode with
      | term finalOwner' finalFreePorts finalTerm =>
          have finalOwnerEq : finalOwner' =
              elimTrace.targetIndex finalWellFormed := by
            simpa [finalShape, CNode.region] using finalOwner
          subst finalOwner'
          have finalShapeDropped : elimTrace.promotion.nodes
              (copyTrace.droppedNodeMap originalNode outside) =
                .term (elimTrace.targetIndex finalWellFormed) finalFreePorts
                  finalTerm := by
            rw [droppedEq]
            exact finalShape
          rw [finalShapeDropped, droppedShape] at promotedShape
          cases promotedShape
      | atom finalOwner' finalBinder =>
          have finalOwnerEq : finalOwner' =
              elimTrace.targetIndex finalWellFormed := by
            simpa [finalShape, CNode.region] using finalOwner
          subst finalOwner'
          have finalShapeDropped : elimTrace.promotion.nodes
              (copyTrace.droppedNodeMap originalNode outside) =
                .atom (elimTrace.targetIndex finalWellFormed) finalBinder := by
            rw [droppedEq]
            exact finalShape
          rw [finalShapeDropped, droppedShape] at promotedShape
          cases promotedShape
      | named finalOwner' finalDefinition finalArity =>
          have finalOwnerEq : finalOwner' =
              elimTrace.targetIndex finalWellFormed := by
            simpa [finalShape, CNode.region] using finalOwner
          subst finalOwner'
          have finalShapeDropped : elimTrace.promotion.nodes
              (copyTrace.droppedNodeMap originalNode outside) =
                .named (elimTrace.targetIndex finalWellFormed) finalDefinition
                  finalArity := by
            rw [droppedEq]
            exact finalShape
          simp only [CNode.region] at finalOwner
          rw [finalShapeDropped, droppedShape] at promotedShape
          cases promotedShape
          simp [copyTrace.reverseRegionMap_targetIndex elimTrace
            finalWellFormed, finalOwner]

theorem focusedKeptChild_shape
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
    input.val.regions
        (copyTrace.reverseRegionMap elimTrace finalWellFormed child) =
      match elimTrace.sourceDiagram.regions child with
      | .sheet => .sheet
      | .cut _ => .cut payload.parent
      | .bubble _ arity => .bubble payload.parent arity := by
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
      have originalParent :=
        (ConcreteElaboration.mem_localOccurrences_child input.val
          payload.parent originalChild).1 originalMember
      have mappedOrigin : copyTrace.regionMap originalChild =
          elimTrace.origin child :=
        ConcreteElaboration.LocalOccurrence.child.inj
          (nodes := result.diagram.val.nodeCount) (by
            simpa [droppedParentForwardMap, droppedOutsideOccurrenceMap,
              VacuousElimTrace.occurrenceMap] using forwardEq)
      have focusReverse := copyTrace.keptChild_finalFocus_eq_reverse elimTrace
        finalWellFormed child member
      have originalEq : originalChild =
          copyTrace.reverseRegionMap elimTrace finalWellFormed child :=
        ConcreteElaboration.LocalOccurrence.child.inj
          (nodes := input.val.nodeCount) (reverseEq.symm.trans focusReverse)
      rw [← originalEq]
      have droppedShape := copyTrace.dropped_region_shape originalChild
      rw [mappedOrigin] at droppedShape
      have droppedParent :
          ((dropInstantiationAtomsRaw result).regions
            (elimTrace.origin child)).parent? =
              some (copyTrace.regionMap payload.parent) := by
        have keptParent := elimTrace.kept_child_parent finalWellFormed child
          member
        simpa [copyTrace.regionMap_parent_eq_elimParent elimTrace] using
          keptParent
      have promotedShape := elimTrace.focused_regionShape child
        (copyTrace.regionMap payload.parent) droppedParent
      cases originalShape : input.val.regions originalChild with
      | sheet =>
          rw [originalShape] at originalParent droppedShape
          simp [CRegion.parent?] at originalParent
      | cut parent =>
          have parentEq : parent = payload.parent := by
            rw [originalShape] at originalParent
            exact Option.some.inj originalParent
          subst parent
          rw [originalShape] at droppedShape
          simp only [mapRegionShape] at droppedShape
          cases finalShape : elimTrace.sourceDiagram.regions child with
          | sheet =>
              have finalShapePromoted : elimTrace.promotion.regions child =
                  .sheet := finalShape
              rw [finalShapePromoted, droppedShape] at promotedShape
              cases promotedShape
          | cut finalParent =>
              rfl
          | bubble finalParent arity =>
              have finalShapePromoted : elimTrace.promotion.regions child =
                  .bubble finalParent arity := finalShape
              rw [finalShapePromoted, droppedShape] at promotedShape
              cases promotedShape
      | bubble parent arity =>
          have parentEq : parent = payload.parent := by
            rw [originalShape] at originalParent
            exact Option.some.inj originalParent
          subst parent
          rw [originalShape] at droppedShape
          simp only [mapRegionShape] at droppedShape
          cases finalShape : elimTrace.sourceDiagram.regions child with
          | sheet =>
              have finalShapePromoted : elimTrace.promotion.regions child =
                  .sheet := finalShape
              rw [finalShapePromoted, droppedShape] at promotedShape
              cases promotedShape
          | cut finalParent =>
              have finalShapePromoted : elimTrace.promotion.regions child =
                  .cut finalParent := finalShape
              rw [finalShapePromoted, droppedShape] at promotedShape
              cases promotedShape
          | bubble finalParent finalArity =>
              have finalShapePromoted : elimTrace.promotion.regions child =
                  .bubble finalParent finalArity := finalShape
              rw [finalShapePromoted] at promotedShape
              rw [droppedShape] at promotedShape
              cases promotedShape
              rfl

theorem focusedKeptNode_endpointOccurs_iff
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
    (boundaryNodup : comprehension.val.boundary.Nodup)
    (finalNode : Fin elimTrace.sourceDiagram.nodeCount)
    (originalNode : Fin input.val.nodeCount)
    (originalRegion : (input.val.nodes originalNode).region = payload.parent)
    (droppedEq : copyTrace.droppedNodeMap originalNode
      (fun enclosed => payload_bubble_not_encloses_parent payload
        (originalRegion ▸ enclosed)) = finalNode)
    (wire : Fin input.val.wireCount)
    (port : CPort) :
    elimTrace.sourceDiagram.EndpointOccurs
        (copyTrace.finalWireMap elimTrace wire) ⟨finalNode, port⟩ ↔
      input.val.EndpointOccurs wire ⟨originalNode, port⟩ := by
  let outside := fun enclosed => payload_bubble_not_encloses_parent payload
    (originalRegion ▸ enclosed)
  change ⟨finalNode, port⟩ ∈
      (elimTrace.promotion.wires (copyTrace.wireMap wire)).endpoints ↔
    input.val.EndpointOccurs wire ⟨originalNode, port⟩
  rw [← droppedEq, elimTrace.promotedWire_endpoints]
  change (dropInstantiationAtomsRaw result).EndpointOccurs
      (copyTrace.wireMap wire)
        ⟨copyTrace.droppedNodeMap originalNode outside, port⟩ ↔
    input.val.EndpointOccurs wire ⟨originalNode, port⟩
  rw [InstantiationSemantic.drop_endpointOccurs_origin_iff]
  rw [copyTrace.droppedNodeMap_origin originalNode outside]
  exact copyTrace.endpointOccurs_wireMap_nodeMap_iff wire originalNode port

theorem focusedKeptNode_resolvedPorts_related
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
    (sourceWellFormed : elimTrace.sourceDiagram.WellFormed signature)
    (boundaryNodup : comprehension.val.boundary.Nodup)
    (sourceContext : ConcreteElaboration.WireContext
      elimTrace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input.val)
    (context : FinalContextWitness copyTrace elimTrace sourceContext
      targetContext)
    (sourceNodup : sourceContext.Nodup)
    (finalNode : Fin elimTrace.sourceDiagram.nodeCount)
    (originalNode : Fin input.val.nodeCount)
    (originalRegion : (input.val.nodes originalNode).region = payload.parent)
    (droppedEq : copyTrace.droppedNodeMap originalNode
      (fun enclosed => payload_bubble_not_encloses_parent payload
        (originalRegion ▸ enclosed)) = finalNode)
    (port : CPort)
    (sourceIndex : Fin sourceContext.length)
    (targetIndex : Fin targetContext.length)
    (sourceResolved : ConcreteElaboration.resolvePort?
      elimTrace.sourceDiagram sourceContext finalNode port = some sourceIndex)
    (targetResolved : ConcreteElaboration.resolvePort? input.val targetContext
      originalNode port = some targetIndex) :
    context.indexRelation.Rel sourceIndex targetIndex := by
  obtain ⟨sourceWire, sourceOccurs, sourceGet⟩ :=
    ConcreteElaboration.resolvePort?_sound sourceResolved
  obtain ⟨targetWire, targetOccurs, targetGet⟩ :=
    ConcreteElaboration.resolvePort?_sound targetResolved
  have mappedTargetOccurs : elimTrace.sourceDiagram.EndpointOccurs
      (copyTrace.finalWireMap elimTrace targetWire) ⟨finalNode, port⟩ :=
    (copyTrace.focusedKeptNode_endpointOccurs_iff elimTrace boundaryNodup
      finalNode originalNode originalRegion droppedEq targetWire port).2
      targetOccurs
  have wireEq : sourceWire = copyTrace.finalWireMap elimTrace targetWire :=
    ConcreteElaboration.endpoint_wire_unique
      sourceWellFormed.wire_endpoints_are_disjoint sourceOccurs
        mappedTargetOccurs
  have mappedLookup := context.sourceIndex_lookup targetIndex
  change targetContext.get targetIndex = targetWire at targetGet
  change sourceContext.lookup?
      (copyTrace.finalWireMap elimTrace (targetContext.get targetIndex)) =
        some (context.sourceIndex targetIndex) at mappedLookup
  rw [targetGet] at mappedLookup
  change context.sourceIndex targetIndex = sourceIndex
  exact (ConcreteElaboration.WireContext.lookup?_unique sourceNodup mappedLookup
    (sourceGet.trans wireEq)).symm

/-- Every retained node at the promoted focus compiles to the corresponding
original-parent item under the composite final context and binder maps. -/
theorem focusedKeptNode_itemSimulation
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
    (sourceWellFormed : elimTrace.sourceDiagram.WellFormed signature)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (boundaryNodup : comprehension.val.boundary.Nodup)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (sourceContext : ConcreteElaboration.WireContext
      elimTrace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input.val)
    (context : FinalContextWitness copyTrace elimTrace sourceContext
      targetContext)
    (sourceNodup : sourceContext.Nodup)
    (sourceBinders : ConcreteElaboration.BinderContext
      elimTrace.sourceDiagram sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext input.val targetRels)
    (binderWitness : FinalBinderWitness copyTrace elimTrace finalWellFormed
      sourceBinders targetBinders)
    (finalNode : Fin elimTrace.sourceDiagram.nodeCount)
    (member : ConcreteElaboration.LocalOccurrence.node finalNode ∈
      elimTrace.keptOccurrences finalWellFormed)
    (targetNode : Fin input.val.nodeCount)
    (mapped : copyTrace.finalFocusOccurrenceMap elimTrace (.node finalNode) =
      .node targetNode)
    (sourceItem : Item signature sourceContext.length sourceRels)
    (targetItem : Item signature targetContext.length targetRels)
    (sourceCompiled : ConcreteElaboration.compileNode? signature
      elimTrace.sourceDiagram sourceContext sourceBinders finalNode =
        some sourceItem)
    (targetCompiled : ConcreteElaboration.compileNode? signature input.val
      targetContext targetBinders targetNode = some targetItem) :
    ConcreteElaboration.ItemSimulation model named direction
      context.indexRelation
      (sourceItem.renameRelations binderWitness.relationMap) targetItem := by
  obtain ⟨originalNode, originalRegion, reverseEq, droppedEq⟩ :=
    copyTrace.keptNode_original elimTrace finalWellFormed finalNode member
  have targetNodeEq : targetNode = originalNode :=
    ConcreteElaboration.LocalOccurrence.node.inj
      (regions := input.val.regionCount) (mapped.symm.trans reverseEq)
  subst targetNode
  apply ConcreteElaboration.compileNode?_itemSimulation_of_related_ports
    model named direction sourceContext targetContext context.indexRelation
    sourceBinders targetBinders binderWitness.relationMap finalNode originalNode
    (copyTrace.reverseRegionMap elimTrace finalWellFormed)
    (copyTrace.reverseRegionMap elimTrace finalWellFormed)
  · have shape := copyTrace.focusedKeptNode_shape elimTrace
      finalWellFormed finalNode member originalNode originalRegion droppedEq
    cases sourceShape : elimTrace.sourceDiagram.nodes finalNode <;>
      simp only [sourceShape] at shape ⊢ <;> exact shape
  · intro port sourceIndex targetIndex sourceResolved targetResolved
    exact copyTrace.focusedKeptNode_resolvedPorts_related elimTrace
      sourceWellFormed boundaryNodup sourceContext targetContext context
      sourceNodup finalNode originalNode originalRegion droppedEq port
      sourceIndex targetIndex sourceResolved targetResolved
  · intro region binder arity sourceRelation sourceShape sourceLookup
    exact binderWitness.bindersMapped binder arity sourceRelation sourceLookup
  · exact sourceCompiled
  · exact targetCompiled

end InstantiationTrace

end VisualProof.Rule
