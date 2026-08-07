import VisualProof.Rule.Soundness.Comprehension.AbstractionOccurrenceFamilySemantic

namespace VisualProof.Concrete


open VisualProof.Concrete

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace AbstractionRawTrace

/-- Semantic simulation below the fresh abstraction bubble.  Unlike the
outer generic simulation, this predicate records that the fresh target
relation has the fixed comprehension interpretation. -/
def FixedRegionSimulation
    {input : Concrete.Checked }
    {wrap : CheckedSelection input.val}
    {comprehension : Concrete.CheckedOpen }
    {occurrences : List (OperationAbstractionOccurrence input)}
    {raw : Concrete.Diagram}
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (model : Model)
    (direction : Concrete.Elaboration.SimulationDirection)
    (sourceFuel targetFuel : Nat)
    (region : Fin input.val.regionCount) : Prop :=
  forall {sourceRels targetRels : RelCtx}
    (sourceContext : Concrete.Elaboration.WireContext input.val)
    (targetContext : Concrete.Elaboration.WireContext trace.diagram)
    (context : ContextWitness trace sourceContext targetContext)
    (sourceNodup : sourceContext.Nodup)
    (sourceBinders : Concrete.Elaboration.BinderContext input.val sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext trace.diagram targetRels)
    (binderWitness : BinderWitness trace sourceBinders targetBinders)
    (sourceCover : sourceBinders.Covers region)
    (targetCover : targetBinders.Covers (trace.regionMap region))
    (sourceEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      input.val sourceBinders region)
    (targetEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      trace.diagram targetBinders (trace.regionMap region))
    (sourceExact : (sourceContext.extend region).Exact region)
    (targetExact : (targetContext.extend (trace.regionMap region)).Exact
      (trace.regionMap region))
    (sourceBody : Region  sourceContext.length sourceRels)
    (targetBody : Region  targetContext.length targetRels),
    Concrete.Elaboration.compileRegion?  input.val sourceFuel region
        sourceContext sourceBinders = some sourceBody ->
    Concrete.Elaboration.compileRegion?  trace.diagram targetFuel
        (trace.regionMap region) targetContext targetBinders = some targetBody ->
    forall (sourceEnvironment : Fin sourceContext.length -> model.Carrier)
      (targetEnvironment : Fin targetContext.length -> model.Carrier)
      (targetRelations : RelEnv model.Carrier targetRels),
      context.indexRelation.EnvironmentsAgree sourceEnvironment
          targetEnvironment ->
      @FixedRelationWitness targetRels  input wrap comprehension
          occurrences raw trace model  targetBinders targetRelations ->
      direction.Entails
        (denoteRegion model  sourceEnvironment targetRelations
          (sourceBody.renameRelations binderWitness.relationMap))
        (denoteRegion model  targetEnvironment targetRelations targetBody)

/-- A surviving node at a non-wrap focused anchor preserves its intrinsic
meaning under the survivor context and binder maps. -/
theorem focusedSurvivingNode_semantic
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (model : Model)
    (direction : Concrete.Elaboration.SimulationDirection)
    (sourceContext : Concrete.Elaboration.WireContext input.val)
    (targetContext : Concrete.Elaboration.WireContext trace.diagram)
    (context : ContextWitness trace sourceContext targetContext)
    (sourceNodup : sourceContext.Nodup)
    (sourceBinders : Concrete.Elaboration.BinderContext input.val sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext trace.diagram targetRels)
    (binderWitness : BinderWitness trace sourceBinders targetBinders)
    (parent : Fin input.val.regionCount)
    (notWrap : parent ≠ wrap.val.anchor)
    (node : Fin input.val.nodeCount)
    (nodeRegion : (input.val.nodes node).region = parent)
    (survives : trace.domains.nodes.survives node = true)
    (sourceItem : Item  sourceContext.length sourceRels)
    (targetItem : Item  targetContext.length targetRels)
    (sourceCompiled : Concrete.Elaboration.compileNode?  input.val
      sourceContext sourceBinders node = some sourceItem)
    (targetCompiled : Concrete.Elaboration.compileNode?  trace.diagram
      targetContext targetBinders (trace.targetNode node survives) =
        some targetItem) :
    Concrete.Elaboration.ItemSimulation model  direction
      context.indexRelation
      (sourceItem.renameRelations binderWitness.relationMap) targetItem := by
  have notDirect : node ∉ wrap.val.directNodes := by
    intro direct
    exact notWrap (nodeRegion.symm.trans
      (wrap.property.directNodes_at_anchor node direct))
  apply Concrete.Elaboration.compileNode?_itemSimulation_of_related_ports
    model  direction sourceContext targetContext context.indexRelation
    sourceBinders targetBinders binderWitness.relationMap node
    (trace.targetNode node survives) trace.regionMap trace.regionMap
  · have shape := trace.node_shape_of_surviving_not_direct node survives notDirect
    cases sourceShape : input.val.nodes node <;>
      simp only [sourceShape] at shape |- <;> exact shape
  · intro port sourceIndex targetIndex sourceResolved targetResolved
    obtain ⟨sourceWire, sourceOccurs, sourceGet⟩ :=
      Concrete.Elaboration.resolvePort?_sound sourceResolved
    obtain ⟨targetWire, targetOccurs, targetGet⟩ :=
      Concrete.Elaboration.resolvePort?_sound targetResolved
    have originOccurs := trace.targetNode_endpoint_origin_occurs node survives
      targetWire port targetOccurs
    have wireEq : trace.domains.wires.origin targetWire = sourceWire :=
      Concrete.Elaboration.endpoint_wire_unique
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
    have binderSurvives := trace.atomBinder_survives node survives owner binder
      sourceShape
    rw [trace.regionMap_of_survives binder binderSurvives]
    exact binderWitness.bindersMapped binder binderSurvives arity
      sourceRelation sourceLookup
  · exact sourceCompiled
  · exact targetCompiled

def reparentMappedNodeShape (owner : Fin targetRegions)
    (binderMap : Fin sourceRegions → Fin targetRegions) :
    CNode sourceRegions → CNode targetRegions
  | .atom _ binder => .atom owner (binderMap binder)
  | .identity _ arity => .identity owner arity
/-- A surviving node selected directly at the wrap is reparented to the fresh
bubble while retaining every compiler-relevant field. -/
theorem node_shape_of_surviving_direct
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (node : Fin input.val.nodeCount)
    (survives : trace.domains.nodes.survives node = true)
    (direct : node ∈ wrap.val.directNodes) :
    trace.diagram.nodes (trace.targetNode node survives) =
      reparentMappedNodeShape trace.bubble trace.regionMap
        (input.val.nodes node) := by
  have result := trace.abstractNode?_targetNode node survives
  unfold abstractNode? at result
  cases sourceShape : input.val.nodes node with
  | identity owner arity =>
      simp only [sourceShape, direct, if_pos, Option.map_some] at result
      simp only [reparentMappedNodeShape]
      exact (Option.some.inj result).symm
  | atom owner binder =>
      have binderSurvives := trace.atomBinder_survives node survives owner binder
        sourceShape
      simp only [sourceShape, direct, if_pos,
        trace.domains.regions.index?_index binder binderSurvives,
        Option.bind_some, Option.map_some] at result
      simp only [reparentMappedNodeShape]
      rw [trace.regionMap_of_survives binder binderSurvives]
      exact (Option.some.inj result).symm
/-- Directly selected surviving nodes compile semantically through the fresh
bubble context. -/
theorem focusedSelectedNode_semantic
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (model : Model)
    (sourceContext : Concrete.Elaboration.WireContext input.val)
    (targetContext : Concrete.Elaboration.WireContext trace.diagram)
    (context : ContextWitness trace sourceContext targetContext)
    (sourceNodup : sourceContext.Nodup)
    (sourceBinders : Concrete.Elaboration.BinderContext input.val sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext trace.diagram targetRels)
    (binderWitness : BinderWitness trace sourceBinders targetBinders)
    (node : Fin input.val.nodeCount)
    (direct : node ∈ wrap.val.directNodes)
    (survives : trace.domains.nodes.survives node = true)
    (sourceItem : Item  sourceContext.length sourceRels)
    (targetItem : Item  targetContext.length targetRels)
    (sourceCompiled : Concrete.Elaboration.compileNode?  input.val
      sourceContext sourceBinders node = some sourceItem)
    (targetCompiled : Concrete.Elaboration.compileNode?  trace.diagram
      targetContext targetBinders (trace.targetNode node survives) =
        some targetItem) :
    Concrete.Elaboration.ItemSimulation model  .forward
      context.indexRelation
      (sourceItem.renameRelations binderWitness.relationMap) targetItem := by
  apply Concrete.Elaboration.compileNode?_itemSimulation_of_related_ports
    model  .forward sourceContext targetContext context.indexRelation
    sourceBinders targetBinders binderWitness.relationMap node
    (trace.targetNode node survives) (fun _ => trace.bubble) trace.regionMap
  · have shape := trace.node_shape_of_surviving_direct node survives direct
    cases sourceShape : input.val.nodes node with
    | identity owner arity =>
        simpa only [sourceShape, reparentMappedNodeShape] using shape
    | atom owner binder =>
        simpa only [sourceShape, reparentMappedNodeShape] using shape
  · intro port sourceIndex targetIndex sourceResolved targetResolved
    obtain ⟨sourceWire, sourceOccurs, sourceGet⟩ :=
      Concrete.Elaboration.resolvePort?_sound sourceResolved
    obtain ⟨targetWire, targetOccurs, targetGet⟩ :=
      Concrete.Elaboration.resolvePort?_sound targetResolved
    have originOccurs := trace.targetNode_endpoint_origin_occurs node survives
      targetWire port targetOccurs
    have wireEq : trace.domains.wires.origin targetWire = sourceWire :=
      Concrete.Elaboration.endpoint_wire_unique
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
    have binderSurvives := trace.atomBinder_survives node survives owner binder
      sourceShape
    rw [trace.regionMap_of_survives binder binderSurvives]
    exact binderWitness.bindersMapped binder binderSurvives arity
      sourceRelation sourceLookup
  · exact sourceCompiled
  · exact targetCompiled

def reparentRegionShape (parent : Fin targetRegions) :
    CRegion sourceRegions → CRegion targetRegions
  | .sheet => .sheet
  | .cut _ => .cut parent
  | .bubble _ arity => .bubble parent arity

/-- A surviving child selected directly at the wrap is reparented to the
fresh bubble while retaining its cut or bubble constructor. -/
theorem region_shape_of_surviving_direct
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (child : Fin input.val.regionCount)
    (survives : trace.domains.regions.survives child = true)
    (direct : child ∈ wrap.val.childRoots) :
    trace.diagram.regions (trace.targetRegion child survives) =
      reparentRegionShape trace.bubble (input.val.regions child) := by
  have result := trace.abstractRegion?_targetRegion child survives
  unfold abstractRegion? at result
  cases sourceShape : input.val.regions child with
  | sheet =>
      simp only [sourceShape] at result
      simp only [reparentRegionShape]
      exact (Option.some.inj result).symm
  | cut parent =>
      simp only [sourceShape, direct, if_pos, Option.map_some] at result
      simp only [reparentRegionShape]
      exact (Option.some.inj result).symm
  | bubble parent arity =>
      simp only [sourceShape, direct, if_pos, Option.map_some] at result
      simp only [reparentRegionShape]
      exact (Option.some.inj result).symm

/-- The executor-created abstraction bubble owns no wires.  Every surviving
target wire retains the image of its original source scope. -/
theorem bubble_exactScopeWires_nil
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw) :
    Concrete.Elaboration.exactScopeWires trace.diagram trace.bubble = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro targetWire member
  have scopeEq := (Concrete.Elaboration.mem_exactScopeWires trace.diagram
    trace.bubble targetWire).1 member
  let sourceWire := trace.domains.wires.origin targetWire
  have survives : trace.domains.wires.survives sourceWire = true :=
    trace.domains.wires.origin_survives targetWire
  have targetEq : trace.targetWire sourceWire survives = targetWire := by
    exact trace.targetWire_origin_index targetWire
  have transportedScope := trace.targetWire_scope sourceWire survives
  rw [targetEq] at transportedScope
  exact trace.targetRegion_ne_bubble (input.val.wires sourceWire).scope
    (trace.wireScope_survives sourceWire survives)
    (transportedScope.symm.trans scopeEq)

@[simp] theorem extend_bubble_eq
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (context : Concrete.Elaboration.WireContext trace.diagram) :
    context.extend trace.bubble = context := by
  simp [Concrete.Elaboration.WireContext.extend,
    trace.bubble_exactScopeWires_nil]

def emptyBubbleEnvironment
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (D : Type) :
    Fin (Concrete.Elaboration.exactScopeWires trace.diagram
      trace.bubble).length → D :=
  fun index => Fin.elim0
    (Fin.cast (congrArg List.length trace.bubble_exactScopeWires_nil) index)

theorem extendedEnvironment_bubble_empty
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (context : Concrete.Elaboration.WireContext trace.diagram)
    (environment : Fin context.length → D) :
    Concrete.Elaboration.extendedEnvironment context trace.bubble environment
        (trace.emptyBubbleEnvironment D) =
      fun index => environment
        (Fin.cast (congrArg List.length (trace.extend_bubble_eq context))
          index) := by
  funext index
  unfold Concrete.Elaboration.extendedEnvironment emptyBubbleEnvironment
  simp only [Function.comp_apply]
  let sourceLocal :
      Fin (Concrete.Elaboration.exactScopeWires trace.diagram
        trace.bubble).length → D := trace.emptyBubbleEnvironment D
  let countEq :
      (Concrete.Elaboration.exactScopeWires trace.diagram
        trace.bubble).length = 0 :=
    congrArg List.length trace.bubble_exactScopeWires_nil
  have transported := VisualProof.Rule.ModalSoundness.extendWireEnv_transport
    (countEq := countEq.symm)
    (sourceLocal := sourceLocal)
    (targetLocal := (Fin.elim0 : Fin 0 → D))
    (localValues := by
      intro impossible
      exact Fin.elim0 impossible)
    (sourceIndex := Fin.cast
      (Concrete.Elaboration.WireContext.length_extend context trace.bubble)
      index)
    (targetIndex := Fin.cast
      ((congrArg List.length (trace.extend_bubble_eq context)).trans
        (Nat.add_zero context.length).symm)
      index)
    (indexValue := rfl)
    environment
  simpa [sourceLocal, emptyBubbleEnvironment, extendWireEnv_zero] using
    transported

/-- Pointwise semantic transport for surviving material selected directly at
the wrap and moved beneath the fresh abstraction bubble. -/
theorem focusedSelectedOccurrence_semantic
    {input : Concrete.Checked }
    {wrap : CheckedSelection input.val}
    {comprehension : Concrete.CheckedOpen }
    {occurrences : List (OperationAbstractionOccurrence input)}
    {raw : Concrete.Diagram}
    {sourceRels targetRels : RelCtx}
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : OperationComprehensionAbstractPayload input wrap comprehension occurrences)
    (targetWellFormed : trace.diagram.WellFormed )
    (model : Model)
    (sourceFuel targetFuel : Nat)
    (sourceContext : Concrete.Elaboration.WireContext input.val)
    (targetContext : Concrete.Elaboration.WireContext trace.diagram)
    (context : ContextWitness trace sourceContext targetContext)
    (sourceBinders : Concrete.Elaboration.BinderContext input.val sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext trace.diagram targetRels)
    (binderWitness : BinderWitness trace sourceBinders targetBinders)
    (sourceExact : sourceContext.Exact wrap.val.anchor)
    (targetExact : targetContext.Exact (trace.regionMap wrap.val.anchor))
    (sourceCover : sourceBinders.Covers wrap.val.anchor)
    (targetCover : targetBinders.Covers (trace.regionMap wrap.val.anchor))
    (sourceEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      input.val sourceBinders wrap.val.anchor)
    (targetEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      trace.diagram targetBinders (trace.regionMap wrap.val.anchor))
    (allowed : AbstractionAllowed input.val wrap.val.anchor .forward
      wrap.val.anchor)
    (recurseAt : ∀ (childDirection : Concrete.Elaboration.SimulationDirection)
      (child : Fin input.val.regionCount),
      child ∈ wrap.selectedRegions →
      trace.domains.regions.survives child = true →
      child ≠ wrap.val.anchor →
      AbstractionAllowed input.val wrap.val.anchor childDirection child →
      FixedRegionSimulation trace model  childDirection sourceFuel
        targetFuel child)
    (occurrence : Concrete.Elaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount)
    {targetOccurrence : Concrete.Elaboration.LocalOccurrence
      trace.diagram.regionCount trace.diagram.nodeCount}
    (selected : occurrence ∈
      VisualProof.Rule.ModalSoundness.selectedOccurrences input.val wrap)
    (mapped : trace.survivingOccurrence? occurrence = some targetOccurrence)
    (sourceItem : Item  sourceContext.length sourceRels)
    (targetItem : Item  targetContext.length
      (comprehension.val.boundary.length :: targetRels))
    (sourceCompiled : Concrete.Elaboration.compileOccurrenceWith?
      input.val (Concrete.Elaboration.compileRegion?  input.val
        sourceFuel) sourceContext sourceBinders occurrence = some sourceItem)
    (targetCompiled : Concrete.Elaboration.compileOccurrenceWith?
      trace.diagram (Concrete.Elaboration.compileRegion?  trace.diagram
        targetFuel) targetContext
          (targetBinders.push trace.bubble comprehension.val.boundary.length)
          targetOccurrence = some targetItem) :
    ∀ (sourceEnvironment : Fin sourceContext.length → model.Carrier)
      (targetEnvironment : Fin targetContext.length → model.Carrier)
      (targetRelations : RelEnv model.Carrier
        (comprehension.val.boundary.length :: targetRels)),
      context.indexRelation.EnvironmentsAgree sourceEnvironment
          targetEnvironment →
      FixedRelationWitness  (input := input)
        (wrap := wrap) (comprehension := comprehension)
        (occurrences := occurrences) (raw := raw) trace model
          (targetBinders.push trace.bubble comprehension.val.boundary.length)
          targetRelations →
      Concrete.Elaboration.SimulationDirection.forward.Entails
        (denoteItem model  sourceEnvironment targetRelations
          (sourceItem.renameRelations
            (binderWitness.intoFreshBubble
              comprehension.val.boundary.length).relationMap))
        (denoteItem model  targetEnvironment targetRelations
          targetItem) := by
  let targetPushed := targetBinders.push trace.bubble
    comprehension.val.boundary.length
  let freshWitness := binderWitness.intoFreshBubble
    comprehension.val.boundary.length
  have wrapMapEq : trace.regionMap wrap.val.anchor =
      trace.targetRegion wrap.val.anchor (wrap_anchor_survives payload) :=
    trace.regionMap_of_survives wrap.val.anchor (wrap_anchor_survives payload)
  have bubbleShape : trace.diagram.regions trace.bubble =
      .bubble (trace.regionMap wrap.val.anchor)
        comprehension.val.boundary.length := by
    have parent := trace.bubble_parent payload
    rw [trace.diagram_bubble] at parent ⊢
    have parentEq := Option.some.inj parent
    rw [wrapMapEq, parentEq]
  have targetBubbleExact : targetContext.Exact trace.bubble := by
    have bubbleParentMapped :
        (trace.diagram.regions trace.bubble).parent? =
          some (trace.regionMap wrap.val.anchor) := by
      rw [wrapMapEq]
      exact trace.bubble_parent payload
    have extended := targetExact.extend_child targetWellFormed
      bubbleParentMapped
    simpa using extended
  have targetBubbleCover : targetPushed.Covers trace.bubble := by
    exact Concrete.Elaboration.BinderContext.push_covers_bubble_child
      targetCover bubbleShape
  have targetBubbleEnumeration :
      Concrete.Elaboration.BinderContext.Enumeration trace.diagram targetPushed
        trace.bubble := by
    exact targetEnumeration.bubbleChild targetWellFormed bubbleShape
  cases occurrence with
  | node node =>
      by_cases survives : trace.domains.nodes.survives node = true
      · rw [trace.survivingOccurrence?_node node survives] at mapped
        cases targetOccurrence with
        | child targetChild => simp at mapped
        | node targetNode =>
            have targetEq := Concrete.Elaboration.LocalOccurrence.node.inj
              (Option.some.inj mapped)
            subst targetNode
            have direct :=
              (mem_selectedOccurrences_node_iff input wrap node).1 selected
            have semantic := trace.focusedSelectedNode_semantic model
              sourceContext targetContext context sourceExact.nodup sourceBinders
              targetPushed freshWitness node direct survives sourceItem targetItem
              sourceCompiled targetCompiled
            intro sourceEnvironment targetEnvironment targetRelations
              environments _
            exact semantic sourceEnvironment targetEnvironment targetRelations
              environments
      · simp [survivingOccurrence?, survives] at mapped
  | child child =>
      by_cases survives : trace.domains.regions.survives child = true
      · rw [trace.survivingOccurrence?_child child survives] at mapped
        cases targetOccurrence with
        | node targetNode => simp at mapped
        | child targetChild =>
            have targetEq := Concrete.Elaboration.LocalOccurrence.child.inj
              (Option.some.inj mapped)
            subst targetChild
            change Concrete.Elaboration.compileOccurrenceWith?
              trace.diagram
                (Concrete.Elaboration.compileRegion?  trace.diagram
                  targetFuel) targetContext targetPushed
                (.child (trace.targetRegion child survives)) = some targetItem
              at targetCompiled
            have direct :=
              (mem_selectedOccurrences_child_iff input wrap child).1 selected
            have childShape := trace.region_shape_of_surviving_direct child
              survives direct
            have childSelected : child ∈ wrap.selectedRegions :=
              (wrap.mem_selectedRegions child).2
                ⟨child, direct, Concrete.Diagram.Encloses.refl input.val child⟩
            have childNotWrap : child ≠ wrap.val.anchor := by
              intro equal
              subst child
              exact selection_anchor_not_selected input wrap childSelected
            have sourceParent := wrap.property.childRoots_direct child direct
            have targetParent :
                (trace.diagram.regions
                  (trace.targetRegion child survives)).parent? =
                    some trace.bubble :=
              (trace.targetRegion_parent_bubble_iff child survives).2 direct
            cases sourceKind : input.val.regions child with
            | sheet =>
                simp [Concrete.Elaboration.compileOccurrenceWith?, sourceKind]
                  at sourceCompiled
            | cut actualParent =>
                have parentEq : actualParent = wrap.val.anchor := by
                  rw [sourceKind] at sourceParent
                  exact Option.some.inj sourceParent
                subst actualParent
                simp only [sourceKind, reparentRegionShape] at childShape
                cases sourceResult : Concrete.Elaboration.compileRegion?
                    input.val sourceFuel child sourceContext sourceBinders with
                | none =>
                    simp [Concrete.Elaboration.compileOccurrenceWith?, sourceKind,
                      sourceResult] at sourceCompiled
                | some sourceBody =>
                    simp [Concrete.Elaboration.compileOccurrenceWith?, sourceKind,
                      sourceResult] at sourceCompiled
                    subst sourceItem
                    cases targetResult : Concrete.Elaboration.compileRegion?
                         trace.diagram targetFuel
                        (trace.targetRegion child survives) targetContext
                        targetPushed with
                    | none =>
                        simp [Concrete.Elaboration.compileOccurrenceWith?, childShape,
                          targetResult] at targetCompiled
                    | some targetBody =>
                        simp [Concrete.Elaboration.compileOccurrenceWith?, childShape,
                          targetResult] at targetCompiled
                        subst targetItem
                        have childAllowed : AbstractionAllowed input.val
                            wrap.val.anchor .backward child :=
                          abstractionAllowed_cut input.val wrap.val.anchor
                            .forward child wrap.val.anchor sourceKind allowed
                        have targetResultMapped :
                            Concrete.Elaboration.compileRegion?
                              trace.diagram targetFuel (trace.regionMap child)
                              targetContext targetPushed = some targetBody := by
                          rw [trace.regionMap_of_survives child survives]
                          exact targetResult
                        have bodies := recurseAt .backward child childSelected
                          survives childNotWrap childAllowed sourceContext
                          targetContext context sourceExact.nodup sourceBinders
                          targetPushed freshWitness
                          (Concrete.Elaboration.BinderContext.covers_cut_child
                            sourceCover sourceKind)
                          (by
                            rw [trace.regionMap_of_survives child survives]
                            exact Concrete.Elaboration.BinderContext.covers_cut_child
                              targetBubbleCover childShape)
                          (sourceEnumeration.cutChild input.property sourceKind)
                          (by
                            rw [trace.regionMap_of_survives child survives]
                            exact targetBubbleEnumeration.cutChild targetWellFormed
                              childShape)
                          (sourceExact.extend_child input.property sourceParent)
                          (by
                            rw [trace.regionMap_of_survives child survives]
                            exact targetBubbleExact.extend_child targetWellFormed
                              targetParent)
                          sourceBody targetBody sourceResult targetResultMapped
                        intro sourceEnvironment targetEnvironment targetRelations
                          environments fixed
                        have bodyEntailment := bodies sourceEnvironment
                          targetEnvironment targetRelations environments fixed
                        simpa only [Item.renameRelations, cut_denotes_negation]
                          using (fun sourceNot targetDenotes =>
                            sourceNot (bodyEntailment targetDenotes))
            | bubble actualParent arity =>
                have parentEq : actualParent = wrap.val.anchor := by
                  rw [sourceKind] at sourceParent
                  exact Option.some.inj sourceParent
                subst actualParent
                simp only [sourceKind, reparentRegionShape] at childShape
                let sourceChildBinders := sourceBinders.push child arity
                let targetChildBinders := targetPushed.push
                  (trace.targetRegion child survives) arity
                cases sourceResult : Concrete.Elaboration.compileRegion?
                    input.val sourceFuel child sourceContext sourceChildBinders with
                | none =>
                    simp [Concrete.Elaboration.compileOccurrenceWith?, sourceKind,
                      sourceChildBinders, sourceResult] at sourceCompiled
                | some sourceBody =>
                    simp [Concrete.Elaboration.compileOccurrenceWith?, sourceKind,
                      sourceChildBinders, sourceResult] at sourceCompiled
                    subst sourceItem
                    cases targetResult : Concrete.Elaboration.compileRegion?
                         trace.diagram targetFuel
                        (trace.targetRegion child survives) targetContext
                        targetChildBinders with
                    | none =>
                        simp [Concrete.Elaboration.compileOccurrenceWith?, childShape,
                          targetChildBinders, targetResult] at targetCompiled
                    | some targetBody =>
                        simp [Concrete.Elaboration.compileOccurrenceWith?, childShape,
                          targetChildBinders, targetResult] at targetCompiled
                        subst targetItem
                        let childWitness : BinderWitness trace sourceChildBinders
                            targetChildBinders := freshWitness.push child survives
                              arity
                        have childAllowed : AbstractionAllowed input.val
                            wrap.val.anchor .forward child :=
                          abstractionAllowed_bubble input.val wrap.val.anchor
                            .forward child wrap.val.anchor arity sourceKind allowed
                        have targetResultMapped :
                            Concrete.Elaboration.compileRegion?
                              trace.diagram targetFuel (trace.regionMap child)
                              targetContext targetChildBinders = some targetBody := by
                          rw [trace.regionMap_of_survives child survives]
                          exact targetResult
                        have bodies := recurseAt .forward child childSelected
                          survives childNotWrap childAllowed sourceContext
                          targetContext context sourceExact.nodup sourceChildBinders
                          targetChildBinders childWitness
                          (Concrete.Elaboration.BinderContext.push_covers_bubble_child
                            sourceCover sourceKind)
                          (by
                            rw [trace.regionMap_of_survives child survives]
                            exact Concrete.Elaboration.BinderContext.push_covers_bubble_child
                              targetBubbleCover childShape)
                          (sourceEnumeration.bubbleChild input.property sourceKind)
                          (by
                            rw [trace.regionMap_of_survives child survives]
                            exact targetBubbleEnumeration.bubbleChild
                              targetWellFormed childShape)
                          (sourceExact.extend_child input.property sourceParent)
                          (by
                            rw [trace.regionMap_of_survives child survives]
                            exact targetBubbleExact.extend_child targetWellFormed
                              targetParent)
                          sourceBody targetBody sourceResult targetResultMapped
                        intro sourceEnvironment targetEnvironment targetRelations
                          environments fixed
                        simp only [Item.renameRelations, bubble_denotes_exists]
                        rintro ⟨relationValue, sourceDenotes⟩
                        have fixedChild := fixed.pushOther
                          (trace.targetRegion child survives) arity
                          (trace.targetRegion_ne_bubble child survives)
                          relationValue
                        exact ⟨relationValue, bodies sourceEnvironment
                          targetEnvironment (relationValue, targetRelations)
                          environments fixedChild sourceDenotes⟩
      · simp [survivingOccurrence?, survives] at mapped

/-- Pointwise semantic transport for one surviving occurrence inside the
selected material.  Child regions recurse under the fixed fresh relation. -/
theorem focusedSurvivingOccurrence_semantic
    {input : Concrete.Checked }
    {wrap : CheckedSelection input.val}
    {comprehension : Concrete.CheckedOpen }
    {occurrences : List (OperationAbstractionOccurrence input)}
    {raw : Concrete.Diagram}
    {sourceRels targetRels : RelCtx}
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (targetWellFormed : trace.diagram.WellFormed )
    (model : Model)
    (direction : Concrete.Elaboration.SimulationDirection)
    (sourceFuel targetFuel : Nat)
    (parent : Fin input.val.regionCount)
    (parentSurvives : trace.domains.regions.survives parent = true)
    (notWrap : parent ≠ wrap.val.anchor)
    (parentSelected : parent ∈ wrap.selectedRegions)
    (sourceContext : Concrete.Elaboration.WireContext input.val)
    (targetContext : Concrete.Elaboration.WireContext trace.diagram)
    (context : ContextWitness trace sourceContext targetContext)
    (sourceBinders : Concrete.Elaboration.BinderContext input.val sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext trace.diagram targetRels)
    (binderWitness : BinderWitness trace sourceBinders targetBinders)
    (sourceExact : sourceContext.Exact parent)
    (targetExact : targetContext.Exact (trace.regionMap parent))
    (sourceCover : sourceBinders.Covers parent)
    (targetCover : targetBinders.Covers (trace.regionMap parent))
    (sourceEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      input.val sourceBinders parent)
    (targetEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      trace.diagram targetBinders (trace.regionMap parent))
    (allowed : AbstractionAllowed input.val wrap.val.anchor direction parent)
    (recurseAt : ∀ (childDirection : Concrete.Elaboration.SimulationDirection)
      (child : Fin input.val.regionCount),
      child ∈ wrap.selectedRegions →
      trace.domains.regions.survives child = true →
      child ≠ wrap.val.anchor →
      AbstractionAllowed input.val wrap.val.anchor childDirection child →
      FixedRegionSimulation trace model  childDirection sourceFuel
        targetFuel child)
    (occurrence : Concrete.Elaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount)
    {targetOccurrence : Concrete.Elaboration.LocalOccurrence
      trace.diagram.regionCount trace.diagram.nodeCount}
    (localMember : occurrence ∈
      Concrete.Elaboration.localOccurrences input.val parent)
    (mapped : trace.survivingOccurrence? occurrence = some targetOccurrence)
    (sourceItem : Item  sourceContext.length sourceRels)
    (targetItem : Item  targetContext.length targetRels)
    (sourceCompiled : Concrete.Elaboration.compileOccurrenceWith?
      input.val (Concrete.Elaboration.compileRegion?  input.val
        sourceFuel) sourceContext sourceBinders occurrence = some sourceItem)
    (targetCompiled : Concrete.Elaboration.compileOccurrenceWith?
      trace.diagram (Concrete.Elaboration.compileRegion?  trace.diagram
        targetFuel) targetContext targetBinders targetOccurrence =
          some targetItem) :
    ∀ (sourceEnvironment : Fin sourceContext.length → model.Carrier)
      (targetEnvironment : Fin targetContext.length → model.Carrier)
      (targetRelations : RelEnv model.Carrier targetRels),
      context.indexRelation.EnvironmentsAgree sourceEnvironment
          targetEnvironment →
      FixedRelationWitness  (input := input)
        (wrap := wrap) (comprehension := comprehension)
        (occurrences := occurrences) (raw := raw) trace model
        targetBinders targetRelations →
      direction.Entails
        (denoteItem model  sourceEnvironment targetRelations
          (sourceItem.renameRelations binderWitness.relationMap))
        (denoteItem model  targetEnvironment targetRelations targetItem) := by
  cases occurrence with
  | node node =>
      by_cases survives : trace.domains.nodes.survives node = true
      · rw [trace.survivingOccurrence?_node node survives] at mapped
        cases targetOccurrence with
        | child targetChild => simp at mapped
        | node targetNode =>
            have targetEq := Concrete.Elaboration.LocalOccurrence.node.inj
              (Option.some.inj mapped)
            subst targetNode
            have nodeRegion :=
              (Concrete.Elaboration.mem_localOccurrences_node input.val parent
                node).1 localMember
            have semantic := trace.focusedSurvivingNode_semantic model
              direction sourceContext targetContext context sourceExact.nodup
              sourceBinders targetBinders binderWitness parent notWrap node
              nodeRegion survives sourceItem targetItem sourceCompiled
              targetCompiled
            intro sourceEnvironment targetEnvironment targetRelations
              environments _
            exact semantic sourceEnvironment targetEnvironment targetRelations
              environments
      · simp [survivingOccurrence?, survives] at mapped
  | child child =>
      by_cases survives : trace.domains.regions.survives child = true
      · rw [trace.survivingOccurrence?_child child survives] at mapped
        cases targetOccurrence with
        | node targetNode => simp at mapped
        | child targetChild =>
            have targetEq := Concrete.Elaboration.LocalOccurrence.child.inj
              (Option.some.inj mapped)
            subst targetChild
            have childParent :=
              (Concrete.Elaboration.mem_localOccurrences_child input.val parent
                child).1 localMember
            have notRoot : child ∉ wrap.val.childRoots := by
              intro root
              have direct := wrap.property.childRoots_direct child root
              exact notWrap (Option.some.inj (childParent.symm.trans direct))
            have childShape := trace.region_shape_of_surviving_not_root child
              survives notRoot
            have targetParent :
                (trace.diagram.regions
                  (trace.targetRegion child survives)).parent? =
                    some (trace.regionMap parent) := by
              rw [trace.regionMap_of_survives parent parentSurvives]
              exact (trace.targetRegion_parent_iff_nonwrap child survives parent
                parentSurvives notWrap).2 childParent
            have parentSelectedRaw :=
              (wrap.mem_selectedRegions parent).1 parentSelected
            obtain ⟨root, rootMember, rootEnclosesParent⟩ := parentSelectedRaw
            have parentEnclosesChild : input.val.Encloses parent child := by
              refine ⟨⟨1, by
                have positive : 0 < input.val.regionCount :=
                  Nat.lt_of_le_of_lt (Nat.zero_le child.val) child.isLt
                omega⟩, ?_⟩
              simp [Concrete.Diagram.climb, childParent]
            have childSelected : child ∈ wrap.selectedRegions := by
              apply (wrap.mem_selectedRegions child).2
              exact ⟨root, rootMember,
                Concrete.Elaboration.checked_encloses_trans input.property
                  rootEnclosesParent parentEnclosesChild⟩
            have childNotWrap : child ≠ wrap.val.anchor := by
              intro equal
              subst child
              exact selection_anchor_not_selected input wrap childSelected
            cases sourceKind : input.val.regions child with
            | sheet =>
                simp [Concrete.Elaboration.compileOccurrenceWith?, sourceKind]
                  at sourceCompiled
            | cut actualParent =>
                have parentEq : actualParent = parent := by
                  rw [sourceKind] at childParent
                  exact Option.some.inj childParent
                subst actualParent
                simp only [sourceKind, mapRegionShape] at childShape
                cases sourceResult : Concrete.Elaboration.compileRegion?
                    input.val sourceFuel child sourceContext sourceBinders with
                | none =>
                    simp [Concrete.Elaboration.compileOccurrenceWith?, sourceKind,
                      sourceResult] at sourceCompiled
                | some sourceBody =>
                    simp [Concrete.Elaboration.compileOccurrenceWith?, sourceKind,
                      sourceResult] at sourceCompiled
                    subst sourceItem
                    cases targetResult : Concrete.Elaboration.compileRegion?
                        trace.diagram targetFuel (trace.targetRegion child survives)
                        targetContext targetBinders with
                    | none =>
                        simp [Concrete.Elaboration.compileOccurrenceWith?, childShape,
                          targetResult] at targetCompiled
                    | some targetBody =>
                        simp [Concrete.Elaboration.compileOccurrenceWith?, childShape,
                          targetResult] at targetCompiled
                        subst targetItem
                        have childAllowed : AbstractionAllowed input.val
                            wrap.val.anchor direction.flip child :=
                          abstractionAllowed_cut input.val wrap.val.anchor direction
                            child parent sourceKind allowed
                        have targetResultMapped :
                            Concrete.Elaboration.compileRegion?  trace.diagram
                              targetFuel (trace.regionMap child) targetContext
                              targetBinders = some targetBody := by
                          rw [trace.regionMap_of_survives child survives]
                          exact targetResult
                        have bodies := recurseAt direction.flip child childSelected
                          survives childNotWrap childAllowed sourceContext
                              targetContext context sourceExact.nodup sourceBinders
                              targetBinders binderWitness
                              (Concrete.Elaboration.BinderContext.covers_cut_child
                                sourceCover sourceKind)
                              (by
                                rw [trace.regionMap_of_survives child survives]
                                exact Concrete.Elaboration.BinderContext.covers_cut_child
                                  targetCover childShape)
                              (sourceEnumeration.cutChild input.property sourceKind)
                              (by
                                rw [trace.regionMap_of_survives child survives]
                                exact targetEnumeration.cutChild targetWellFormed
                                  childShape)
                              (sourceExact.extend_child input.property childParent)
                              (by
                                rw [trace.regionMap_of_survives child survives]
                                exact targetExact.extend_child targetWellFormed targetParent)
                              sourceBody targetBody sourceResult targetResultMapped
                        intro sourceEnvironment targetEnvironment targetRelations
                          environments fixed
                        have bodyEntailment := bodies sourceEnvironment
                          targetEnvironment targetRelations environments fixed
                        simp only [Item.renameRelations, cut_denotes_negation]
                        cases direction with
                        | forward =>
                            exact fun sourceNot targetDenotes =>
                              sourceNot (bodyEntailment targetDenotes)
                        | backward =>
                            exact fun targetNot sourceDenotes =>
                              targetNot (bodyEntailment sourceDenotes)
            | bubble actualParent arity =>
                have parentEq : actualParent = parent := by
                  rw [sourceKind] at childParent
                  exact Option.some.inj childParent
                subst actualParent
                simp only [sourceKind, mapRegionShape] at childShape
                let sourcePushed := sourceBinders.push child arity
                let targetPushed := targetBinders.push
                  (trace.targetRegion child survives) arity
                cases sourceResult : Concrete.Elaboration.compileRegion?
                    input.val sourceFuel child sourceContext sourcePushed with
                | none =>
                    simp [Concrete.Elaboration.compileOccurrenceWith?, sourceKind,
                      sourcePushed, sourceResult] at sourceCompiled
                | some sourceBody =>
                    simp [Concrete.Elaboration.compileOccurrenceWith?, sourceKind,
                      sourcePushed, sourceResult] at sourceCompiled
                    subst sourceItem
                    cases targetResult : Concrete.Elaboration.compileRegion?
                        trace.diagram targetFuel (trace.targetRegion child survives)
                        targetContext targetPushed with
                    | none =>
                        simp [Concrete.Elaboration.compileOccurrenceWith?, childShape,
                          targetPushed, targetResult] at targetCompiled
                    | some targetBody =>
                        simp [Concrete.Elaboration.compileOccurrenceWith?, childShape,
                          targetPushed, targetResult] at targetCompiled
                        subst targetItem
                        let childWitness : BinderWitness trace sourcePushed
                            targetPushed := binderWitness.push child survives arity
                        have childAllowed : AbstractionAllowed input.val
                            wrap.val.anchor direction child :=
                          abstractionAllowed_bubble input.val wrap.val.anchor
                            direction child parent arity sourceKind allowed
                        have targetResultMapped :
                            Concrete.Elaboration.compileRegion?  trace.diagram
                              targetFuel (trace.regionMap child) targetContext
                              targetPushed = some targetBody := by
                          rw [trace.regionMap_of_survives child survives]
                          exact targetResult
                        have bodies := recurseAt direction child childSelected
                          survives childNotWrap childAllowed sourceContext
                              targetContext context sourceExact.nodup sourcePushed
                              targetPushed childWitness
                              (Concrete.Elaboration.BinderContext.push_covers_bubble_child
                                sourceCover sourceKind)
                              (by
                                rw [trace.regionMap_of_survives child survives]
                                exact Concrete.Elaboration.BinderContext.push_covers_bubble_child
                                  targetCover childShape)
                              (sourceEnumeration.bubbleChild input.property sourceKind)
                              (by
                                rw [trace.regionMap_of_survives child survives]
                                exact targetEnumeration.bubbleChild targetWellFormed
                                  childShape)
                              (sourceExact.extend_child input.property childParent)
                              (by
                                rw [trace.regionMap_of_survives child survives]
                                exact targetExact.extend_child targetWellFormed targetParent)
                              sourceBody targetBody sourceResult targetResultMapped
                        intro sourceEnvironment targetEnvironment targetRelations
                          environments fixed
                        simp only [Item.renameRelations, bubble_denotes_exists]
                        cases direction with
                        | forward =>
                            rintro ⟨relationValue, sourceDenotes⟩
                            have fixedChild := fixed.pushOther
                              (trace.targetRegion child survives) arity
                              (trace.targetRegion_ne_bubble child survives)
                              relationValue
                            exact ⟨relationValue, bodies sourceEnvironment
                              targetEnvironment (relationValue, targetRelations)
                              environments fixedChild sourceDenotes⟩
                        | backward =>
                            rintro ⟨relationValue, targetDenotes⟩
                            have fixedChild := fixed.pushOther
                              (trace.targetRegion child survives) arity
                              (trace.targetRegion_ne_bubble child survives)
                              relationValue
                            exact ⟨relationValue, bodies sourceEnvironment
                              targetEnvironment (relationValue, targetRelations)
                              environments fixedChild targetDenotes⟩
      · simp [survivingOccurrence?, survives] at mapped

end AbstractionRawTrace

end VisualProof.Concrete
