import VisualProof.Rule.Soundness.Comprehension.AbstractionAllowed

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

namespace AbstractionRawTrace

/-- Total presentation of the partial survivor occurrence map.  The fallback
is unreachable on every list to which the focused compiler applies it. -/
def survivorOccurrence
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw) :
    ConcreteElaboration.LocalOccurrence input.val.regionCount input.val.nodeCount →
      ConcreteElaboration.LocalOccurrence trace.diagram.regionCount
        trace.diagram.nodeCount :=
  fun occurrence =>
    match trace.survivingOccurrence? occurrence with
    | some target => target
    | none => .child trace.diagram.root

theorem survivorOccurrence_eq_of_some
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (source : ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount)
    (target : ConcreteElaboration.LocalOccurrence trace.diagram.regionCount
      trace.diagram.nodeCount)
    (mapped : trace.survivingOccurrence? source = some target) :
    trace.survivorOccurrence source = target := by
  simp [survivorOccurrence, mapped]

theorem filterMap_eq_map_survivor
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (values : List (ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount))
    (survives : ∀ occurrence, occurrence ∈ values →
      ∃ target, trace.survivingOccurrence? occurrence = some target) :
    values.filterMap trace.survivingOccurrence? =
      values.map trace.survivorOccurrence := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      obtain ⟨target, headMapped⟩ := survives head (by simp)
      have tailSurvives : ∀ occurrence, occurrence ∈ tail →
          ∃ target, trace.survivingOccurrence? occurrence = some target := by
        intro occurrence member
        exact survives occurrence (by simp [member])
      simp [headMapped, trace.survivorOccurrence_eq_of_some head target
        headMapped, induction tailSurvives]

theorem kept_node_survives
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (node : Fin input.val.nodeCount)
    (member : ConcreteElaboration.LocalOccurrence.node node ∈
      ModalSoundness.keptOccurrences input.val wrap) :
    trace.domains.nodes.survives node = true := by
  have kept := (mem_keptOccurrences_node_iff input wrap node).1 member
  apply (node_survives_iff input occurrences node).2
  intro selected
  rw [abstractionNodes, List.mem_flatMap] at selected
  obtain ⟨occurrence, occurrenceMember, occurrenceSelected⟩ := selected
  obtain ⟨index, occurrenceEq⟩ := List.mem_iff_get.mp occurrenceMember
  rw [← occurrenceEq] at occurrenceSelected
  have wrapSelected := payload.nodes_inside index node occurrenceSelected
  rcases (wrap.mem_selectedNodes node).1 wrapSelected with
    direct | ownerSelected
  · exact kept.2 direct
  · have anchorSelected : wrap.val.anchor ∈ wrap.selectedRegions := by
      simpa [kept.1] using ownerSelected
    exact selection_anchor_not_selected input wrap anchorSelected

theorem kept_child_survives
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (child : Fin input.val.regionCount)
    (member : ConcreteElaboration.LocalOccurrence.child child ∈
      ModalSoundness.keptOccurrences input.val wrap) :
    trace.domains.regions.survives child = true := by
  have kept := (mem_keptOccurrences_child_iff input wrap child).1 member
  apply (region_survives_iff input occurrences child).2
  intro selected
  rw [abstractionRegions, List.mem_flatMap] at selected
  obtain ⟨occurrence, occurrenceMember, occurrenceSelected⟩ := selected
  obtain ⟨index, occurrenceEq⟩ := List.mem_iff_get.mp occurrenceMember
  rw [← occurrenceEq] at occurrenceSelected
  have wrapSelected := payload.regions_inside index child occurrenceSelected
  obtain ⟨root, rootMember, encloses⟩ :=
    (wrap.mem_selectedRegions child).1 wrapSelected
  have rootEq : root = child := by
    have rootParent := wrap.property.childRoots_direct root rootMember
    rcases ConcreteElaboration.encloses_direct_child kept.1 encloses with
      equal | enclosesParent
    · exact equal
    · exact False.elim
        (ConcreteElaboration.checked_direct_child_not_encloses_parent
          input.property rootParent enclosesParent)
  exact kept.2 (rootEq ▸ rootMember)

theorem kept_occurrence_survives
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (occurrence : ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount)
    (member : occurrence ∈ ModalSoundness.keptOccurrences input.val wrap) :
    ∃ target, trace.survivingOccurrence? occurrence = some target := by
  cases occurrence with
  | node node =>
      let survives := trace.kept_node_survives payload node member
      exact ⟨.node (trace.targetNode node survives),
        trace.survivingOccurrence?_node node survives⟩
  | child child =>
      let survives := trace.kept_child_survives payload child member
      exact ⟨.child (trace.targetRegion child survives),
        trace.survivingOccurrence?_child child survives⟩

theorem kept_filterMap_eq_map
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences) :
    (ModalSoundness.keptOccurrences input.val wrap).filterMap
        trace.survivingOccurrence? =
      (ModalSoundness.keptOccurrences input.val wrap).map
        trace.survivorOccurrence :=
  trace.filterMap_eq_map_survivor _
    (fun occurrence member => trace.kept_occurrence_survives payload
      occurrence member)

/-- A retained node at the wrap anchor compiles through the exact survivor
contexts and binder renaming in either polarity. -/
theorem focusedKeptNode_itemSimulation
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (sourceContext : ConcreteElaboration.WireContext input.val)
    (targetContext : ConcreteElaboration.WireContext trace.diagram)
    (context : ContextWitness trace sourceContext targetContext)
    (sourceNodup : sourceContext.Nodup)
    (sourceBinders : ConcreteElaboration.BinderContext input.val sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext trace.diagram targetRels)
    (binderWitness : BinderWitness trace sourceBinders targetBinders)
    (node : Fin input.val.nodeCount)
    (member : ConcreteElaboration.LocalOccurrence.node node ∈
      ModalSoundness.keptOccurrences input.val wrap)
    (sourceItem : Item signature sourceContext.length sourceRels)
    (targetItem : Item signature targetContext.length targetRels)
    (sourceCompiled : ConcreteElaboration.compileNode? signature input.val
      sourceContext sourceBinders node = some sourceItem)
    (targetCompiled : ConcreteElaboration.compileNode? signature trace.diagram
      targetContext targetBinders
      (trace.targetNode node (trace.kept_node_survives payload node member)) =
        some targetItem) :
    ConcreteElaboration.ItemSimulation model named direction
      context.indexRelation
      (sourceItem.renameRelations binderWitness.relationMap) targetItem := by
  let nodeSurvives := trace.kept_node_survives payload node member
  have kept := (mem_keptOccurrences_node_iff input wrap node).1 member
  apply ConcreteElaboration.compileNode?_itemSimulation_of_related_ports
    model named direction sourceContext targetContext context.indexRelation
    sourceBinders targetBinders binderWitness.relationMap node
    (trace.targetNode node nodeSurvives) trace.regionMap trace.regionMap
  · have shape := trace.node_shape_of_surviving_not_direct node nodeSurvives
      kept.2
    cases sourceShape : input.val.nodes node <;>
      simp only [sourceShape] at shape ⊢ <;> exact shape
  · intro port sourceIndex targetIndex sourceResolved targetResolved
    obtain ⟨sourceWire, sourceOccurs, sourceGet⟩ :=
      ConcreteElaboration.resolvePort?_sound sourceResolved
    obtain ⟨targetWire, targetOccurs, targetGet⟩ :=
      ConcreteElaboration.resolvePort?_sound targetResolved
    have originOccurs := trace.targetNode_endpoint_origin_occurs node
      nodeSurvives targetWire port targetOccurs
    have wireEq : trace.domains.wires.origin targetWire = sourceWire :=
      ConcreteElaboration.endpoint_wire_unique
        input.property.wire_endpoints_are_disjoint originOccurs sourceOccurs
    have targetGet' : targetContext.get targetIndex = targetWire := by
      simpa only [List.get_eq_getElem] using targetGet
    have sourceGet' : sourceContext.get sourceIndex = sourceWire := by
      simpa only [List.get_eq_getElem] using sourceGet
    have mappedGet : sourceContext.get (context.sourceIndex targetIndex) =
        sourceWire := by
      rw [context.sourceIndex_get, targetGet', wireEq]
    change context.sourceIndex targetIndex = sourceIndex
    apply Fin.ext
    exact (List.getElem_inj sourceNodup).mp (by
      simpa only [List.get_eq_getElem] using mappedGet.trans sourceGet'.symm)
  · intro owner binder arity sourceRelation sourceShape sourceLookup
    have binderSurvives := trace.atomBinder_survives node nodeSurvives owner
      binder sourceShape
    rw [trace.regionMap_of_survives binder binderSurvives]
    exact binderWitness.bindersMapped binder binderSurvives arity
      sourceRelation sourceLookup
  · exact sourceCompiled
  · exact targetCompiled

/-- Pointwise compiler simulation for the unselected material retained at the
outer wrap anchor.  Child regions recurse only through the outer frame. -/
theorem focusedKeptOccurrence_itemSimulation
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (targetWellFormed : trace.diagram.WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (sourceContext : ConcreteElaboration.WireContext input.val)
    (targetContext : ConcreteElaboration.WireContext trace.diagram)
    (context : ContextWitness trace sourceContext targetContext)
    (sourceBinders : ConcreteElaboration.BinderContext input.val sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext trace.diagram targetRels)
    (binderWitness : BinderWitness trace sourceBinders targetBinders)
    (sourceExact : sourceContext.Exact wrap.val.anchor)
    (targetExact : targetContext.Exact
      (trace.regionMap wrap.val.anchor))
    (sourceBindersCover : sourceBinders.Covers wrap.val.anchor)
    (targetBindersCover : targetBinders.Covers
      (trace.regionMap wrap.val.anchor))
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      input.val sourceBinders wrap.val.anchor)
    (targetEnumeration : ConcreteElaboration.BinderContext.Enumeration
      trace.diagram targetBinders (trace.regionMap wrap.val.anchor))
    (allowed : AbstractionAllowed input.val wrap.val.anchor direction
      wrap.val.anchor)
    (recurseAt : ∀
      {childDirection : ConcreteElaboration.SimulationDirection}
      {child : Fin input.val.regionCount}
      {childSourceRels childTargetRels : RelCtx}
      {childSourceBinders : ConcreteElaboration.BinderContext input.val
        childSourceRels}
      {childTargetBinders : ConcreteElaboration.BinderContext trace.diagram
        childTargetRels}
      (childFuelTarget : Nat)
      (childSourceContext : ConcreteElaboration.WireContext input.val)
      (childTargetContext : ConcreteElaboration.WireContext trace.diagram)
      (childContext : ContextWitness trace childSourceContext childTargetContext),
      trace.OuterReachable child →
      AbstractionAllowed input.val wrap.val.anchor childDirection child →
      (childBinderWitness : BinderWitness trace childSourceBinders
        childTargetBinders) →
      childSourceBinders.Covers child →
      childTargetBinders.Covers (trace.regionMap child) →
      ConcreteElaboration.BinderContext.Enumeration input.val
        childSourceBinders child →
      ConcreteElaboration.BinderContext.Enumeration trace.diagram
        childTargetBinders (trace.regionMap child) →
      (childSourceContext.extend child).Exact child →
      (childTargetContext.extend (trace.regionMap child)).Exact
        (trace.regionMap child) →
      ∀ (sourceBody : Region signature childSourceContext.length
          childSourceRels)
        (targetBody : Region signature childTargetContext.length
          childTargetRels),
      ConcreteElaboration.compileRegion? signature input.val fuelSource child
          childSourceContext childSourceBinders = some sourceBody →
      ConcreteElaboration.compileRegion? signature trace.diagram
          childFuelTarget (trace.regionMap child) childTargetContext
          childTargetBinders = some targetBody →
      ConcreteElaboration.RegionSimulation model named childDirection
        childContext.indexRelation
        (sourceBody.renameRelations childBinderWitness.relationMap)
        targetBody)
    (occurrence : ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount)
    (member : occurrence ∈ ModalSoundness.keptOccurrences input.val wrap)
    (sourceItem : Item signature sourceContext.length sourceRels)
    (targetItem : Item signature targetContext.length targetRels)
    (sourceCompiled : ConcreteElaboration.compileOccurrenceWith? signature
      input.val (ConcreteElaboration.compileRegion? signature input.val
        fuelSource) sourceContext sourceBinders occurrence = some sourceItem)
    (targetCompiled : ConcreteElaboration.compileOccurrenceWith? signature
      trace.diagram (ConcreteElaboration.compileRegion? signature trace.diagram
        fuelTarget) targetContext targetBinders
        (trace.survivorOccurrence occurrence) = some targetItem) :
    ConcreteElaboration.ItemSimulation model named direction
      context.indexRelation
      (sourceItem.renameRelations binderWitness.relationMap) targetItem := by
  cases occurrence with
  | node node =>
      let survives := trace.kept_node_survives payload node member
      have mapped := trace.survivingOccurrence?_node node survives
      have mapEq := trace.survivorOccurrence_eq_of_some (.node node)
        (.node (trace.targetNode node survives)) mapped
      rw [mapEq] at targetCompiled
      exact trace.focusedKeptNode_itemSimulation payload model named direction
        sourceContext targetContext context sourceExact.nodup sourceBinders
        targetBinders binderWitness node member sourceItem targetItem
        sourceCompiled targetCompiled
  | child child =>
      have kept := (mem_keptOccurrences_child_iff input wrap child).1 member
      let survives := trace.kept_child_survives payload child member
      have mapped := trace.survivingOccurrence?_child child survives
      have mapEq := trace.survivorOccurrence_eq_of_some (.child child)
        (.child (trace.targetRegion child survives)) mapped
      rw [mapEq] at targetCompiled
      have childShape := trace.region_shape_of_surviving_not_root child survives
        kept.2
      have targetParent :
          (trace.diagram.regions (trace.targetRegion child survives)).parent? =
            some (trace.regionMap wrap.val.anchor) := by
        rw [trace.regionMap_of_survives wrap.val.anchor
          (wrap_anchor_survives payload)]
        exact (trace.targetRegion_parent_wrap_iff child survives
          (wrap_anchor_survives payload)).2 kept
      have childOuter : trace.OuterReachable child := by
        refine ⟨survives, Or.inr ?_⟩
        intro selected
        obtain ⟨root, rootMember, encloses⟩ :=
          (wrap.mem_selectedRegions child).1 selected
        have rootEq : root = child := by
          have rootParent := wrap.property.childRoots_direct root rootMember
          rcases ConcreteElaboration.encloses_direct_child kept.1 encloses with
            equal | enclosesParent
          · exact equal
          · exact False.elim
              (ConcreteElaboration.checked_direct_child_not_encloses_parent
                input.property rootParent enclosesParent)
        exact kept.2 (rootEq ▸ rootMember)
      cases sourceKind : input.val.regions child with
      | sheet =>
          simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind]
            at sourceCompiled
      | cut parent =>
          have parentEq : parent = wrap.val.anchor := by
            rw [sourceKind] at kept
            exact Option.some.inj kept.1
          subst parent
          simp only [sourceKind, mapRegionShape] at childShape
          cases sourceResult : ConcreteElaboration.compileRegion? signature
              input.val fuelSource child sourceContext sourceBinders with
          | none =>
              simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
                sourceResult] at sourceCompiled
          | some sourceBody =>
              simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
                sourceResult] at sourceCompiled
              subst sourceItem
              cases targetResult : ConcreteElaboration.compileRegion? signature
                  trace.diagram fuelTarget (trace.targetRegion child survives)
                  targetContext targetBinders with
              | none =>
                  simp [ConcreteElaboration.compileOccurrenceWith?, childShape,
                    targetResult] at targetCompiled
              | some targetBody =>
                  simp [ConcreteElaboration.compileOccurrenceWith?, childShape,
                    targetResult] at targetCompiled
                  subst targetItem
                  have childAllowed : AbstractionAllowed input.val
                      wrap.val.anchor direction.flip child := by
                    exact abstractionAllowed_cut input.val wrap.val.anchor
                      direction child wrap.val.anchor sourceKind allowed
                  have childShapeMapped : trace.diagram.regions
                      (trace.regionMap child) =
                        .cut (trace.regionMap wrap.val.anchor) := by
                    rw [trace.regionMap_of_survives child survives]
                    exact childShape
                  have targetParentMapped :
                      (trace.diagram.regions (trace.regionMap child)).parent? =
                        some (trace.regionMap wrap.val.anchor) := by
                    rw [trace.regionMap_of_survives child survives]
                    exact targetParent
                  have targetResultMapped :
                      ConcreteElaboration.compileRegion? signature trace.diagram
                          fuelTarget (trace.regionMap child) targetContext
                          targetBinders = some targetBody := by
                    rw [trace.regionMap_of_survives child survives]
                    exact targetResult
                  have bodies := recurseAt fuelTarget sourceContext targetContext
                    context childOuter childAllowed binderWitness
                    (ConcreteElaboration.BinderContext.covers_cut_child
                      sourceBindersCover sourceKind)
                    (ConcreteElaboration.BinderContext.covers_cut_child
                      targetBindersCover childShapeMapped)
                    (sourceEnumeration.cutChild input.property sourceKind)
                    (targetEnumeration.cutChild targetWellFormed
                      childShapeMapped)
                    (sourceExact.extend_child input.property kept.1)
                    (targetExact.extend_child targetWellFormed targetParentMapped)
                    sourceBody targetBody sourceResult targetResultMapped
                  intro sourceEnv targetEnv relEnv environments
                  have bodyEntailment := bodies sourceEnv targetEnv relEnv
                    environments
                  simp only [Item.renameRelations, cut_denotes_negation]
                  cases direction with
                  | forward =>
                      exact fun sourceNot targetDenotes =>
                        sourceNot (bodyEntailment targetDenotes)
                  | backward =>
                      exact fun targetNot sourceDenotes =>
                        targetNot (bodyEntailment sourceDenotes)
      | bubble parent arity =>
          have parentEq : parent = wrap.val.anchor := by
            rw [sourceKind] at kept
            exact Option.some.inj kept.1
          subst parent
          simp only [sourceKind, mapRegionShape] at childShape
          let sourcePushed := sourceBinders.push child arity
          let targetPushed := targetBinders.push
            (trace.targetRegion child survives) arity
          cases sourceResult : ConcreteElaboration.compileRegion? signature
              input.val fuelSource child sourceContext sourcePushed with
          | none =>
              simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
                sourcePushed, sourceResult] at sourceCompiled
          | some sourceBody =>
              simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
                sourcePushed, sourceResult] at sourceCompiled
              subst sourceItem
              cases targetResult : ConcreteElaboration.compileRegion? signature
                  trace.diagram fuelTarget (trace.targetRegion child survives)
                  targetContext targetPushed with
              | none =>
                  simp [ConcreteElaboration.compileOccurrenceWith?, childShape,
                    targetPushed, targetResult] at targetCompiled
              | some targetBody =>
                  simp [ConcreteElaboration.compileOccurrenceWith?, childShape,
                    targetPushed, targetResult] at targetCompiled
                  subst targetItem
                  let childWitness : BinderWitness trace sourcePushed
                      targetPushed := by
                    exact binderWitness.push child survives arity
                  have childAllowed : AbstractionAllowed input.val
                      wrap.val.anchor direction child := by
                    exact abstractionAllowed_bubble input.val wrap.val.anchor
                      direction child wrap.val.anchor arity sourceKind allowed
                  have childShapeMapped : trace.diagram.regions
                      (trace.regionMap child) =
                        .bubble (trace.regionMap wrap.val.anchor) arity := by
                    rw [trace.regionMap_of_survives child survives]
                    exact childShape
                  have targetParentMapped :
                      (trace.diagram.regions (trace.regionMap child)).parent? =
                        some (trace.regionMap wrap.val.anchor) := by
                    rw [trace.regionMap_of_survives child survives]
                    exact targetParent
                  have targetResultMapped :
                      ConcreteElaboration.compileRegion? signature trace.diagram
                          fuelTarget (trace.regionMap child) targetContext
                          targetPushed = some targetBody := by
                    rw [trace.regionMap_of_survives child survives]
                    exact targetResult
                  have bodies := recurseAt fuelTarget sourceContext targetContext
                    context childOuter childAllowed childWitness
                    (ConcreteElaboration.BinderContext.push_covers_bubble_child
                      sourceBindersCover sourceKind)
                    (by
                      simpa [targetPushed,
                        trace.regionMap_of_survives child survives] using
                          ConcreteElaboration.BinderContext.push_covers_bubble_child
                            targetBindersCover childShapeMapped)
                    (sourceEnumeration.bubbleChild input.property sourceKind)
                    (by
                      simpa [targetPushed,
                        trace.regionMap_of_survives child survives] using
                          targetEnumeration.bubbleChild targetWellFormed
                            childShapeMapped)
                    (sourceExact.extend_child input.property kept.1)
                    (targetExact.extend_child targetWellFormed targetParentMapped)
                    sourceBody targetBody sourceResult targetResultMapped
                  have pushedMap :
                      (childWitness.relationMap :
                        RelationRenaming (arity :: sourceRels)
                          (arity :: targetRels)) =
                        (RelationRenaming.lift binderWitness.relationMap arity :
                          RelationRenaming (arity :: sourceRels)
                            (arity :: targetRels)) := by
                    rfl
                  rw [pushedMap] at bodies
                  intro sourceEnv targetEnv relEnv environments
                  simp only [Item.renameRelations, bubble_denotes_exists]
                  cases direction with
                  | forward =>
                      rintro ⟨relationValue, sourceDenotes⟩
                      exact ⟨relationValue, bodies sourceEnv targetEnv
                        (relationValue, relEnv) environments sourceDenotes⟩
                  | backward =>
                      rintro ⟨relationValue, targetDenotes⟩
                      exact ⟨relationValue, bodies sourceEnv targetEnv
                        (relationValue, relEnv) environments targetDenotes⟩

end AbstractionRawTrace

end VisualProof.Rule
