import VisualProof.Rule.Soundness.Comprehension.AbstractionOccurrenceFamilySemantic

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace AbstractionRawTrace

/-- Semantic simulation below the fresh abstraction bubble.  Unlike the
outer generic simulation, this predicate records that the fresh target
relation has the fixed comprehension interpretation. -/
def FixedRegionSimulation
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {wrap : CheckedSelection input.val}
    {comprehension : CheckedOpenDiagram signature}
    {occurrences : List (AbstractionOccurrence input)}
    {raw : ConcreteDiagram}
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (sourceFuel targetFuel : Nat)
    (region : Fin input.val.regionCount) : Prop :=
  forall {sourceRels targetRels : RelCtx}
    (sourceContext : ConcreteElaboration.WireContext input.val)
    (targetContext : ConcreteElaboration.WireContext trace.diagram)
    (context : ContextWitness trace sourceContext targetContext)
    (sourceNodup : sourceContext.Nodup)
    (sourceBinders : ConcreteElaboration.BinderContext input.val sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext trace.diagram targetRels)
    (binderWitness : BinderWitness trace sourceBinders targetBinders)
    (sourceCover : sourceBinders.Covers region)
    (targetCover : targetBinders.Covers (trace.regionMap region))
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      input.val sourceBinders region)
    (targetEnumeration : ConcreteElaboration.BinderContext.Enumeration
      trace.diagram targetBinders (trace.regionMap region))
    (sourceExact : (sourceContext.extend region).Exact region)
    (targetExact : (targetContext.extend (trace.regionMap region)).Exact
      (trace.regionMap region))
    (sourceBody : Region signature sourceContext.length sourceRels)
    (targetBody : Region signature targetContext.length targetRels),
    ConcreteElaboration.compileRegion? signature input.val sourceFuel region
        sourceContext sourceBinders = some sourceBody ->
    ConcreteElaboration.compileRegion? signature trace.diagram targetFuel
        (trace.regionMap region) targetContext targetBinders = some targetBody ->
    forall (sourceEnvironment : Fin sourceContext.length -> model.Carrier)
      (targetEnvironment : Fin targetContext.length -> model.Carrier)
      (targetRelations : RelEnv model.Carrier targetRels),
      context.indexRelation.EnvironmentsAgree sourceEnvironment
          targetEnvironment ->
      @FixedRelationWitness targetRels signature input wrap comprehension
          occurrences raw trace model named targetBinders targetRelations ->
      direction.Entails
        (denoteRegion model named sourceEnvironment targetRelations
          (sourceBody.renameRelations binderWitness.relationMap))
        (denoteRegion model named targetEnvironment targetRelations targetBody)

/-- A surviving node at a non-wrap focused anchor preserves its intrinsic
meaning under the survivor context and binder maps. -/
theorem focusedSurvivingNode_semantic
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
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
    (parent : Fin input.val.regionCount)
    (notWrap : parent ≠ wrap.val.anchor)
    (node : Fin input.val.nodeCount)
    (nodeRegion : (input.val.nodes node).region = parent)
    (survives : trace.domains.nodes.survives node = true)
    (sourceItem : Item signature sourceContext.length sourceRels)
    (targetItem : Item signature targetContext.length targetRels)
    (sourceCompiled : ConcreteElaboration.compileNode? signature input.val
      sourceContext sourceBinders node = some sourceItem)
    (targetCompiled : ConcreteElaboration.compileNode? signature trace.diagram
      targetContext targetBinders (trace.targetNode node survives) =
        some targetItem) :
    ConcreteElaboration.ItemSimulation model named direction
      context.indexRelation
      (sourceItem.renameRelations binderWitness.relationMap) targetItem := by
  have notDirect : node ∉ wrap.val.directNodes := by
    intro direct
    exact notWrap (nodeRegion.symm.trans
      (wrap.property.directNodes_at_anchor node direct))
  apply ConcreteElaboration.compileNode?_itemSimulation_of_related_ports
    model named direction sourceContext targetContext context.indexRelation
    sourceBinders targetBinders binderWitness.relationMap node
    (trace.targetNode node survives) trace.regionMap trace.regionMap
  · have shape := trace.node_shape_of_surviving_not_direct node survives notDirect
    cases sourceShape : input.val.nodes node <;>
      simp only [sourceShape] at shape |- <;> exact shape
  · intro port sourceIndex targetIndex sourceResolved targetResolved
    obtain ⟨sourceWire, sourceOccurs, sourceGet⟩ :=
      ConcreteElaboration.resolvePort?_sound sourceResolved
    obtain ⟨targetWire, targetOccurs, targetGet⟩ :=
      ConcreteElaboration.resolvePort?_sound targetResolved
    have originOccurs := trace.targetNode_endpoint_origin_occurs node survives
      targetWire port targetOccurs
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
    have binderSurvives := trace.atomBinder_survives node survives owner binder
      sourceShape
    rw [trace.regionMap_of_survives binder binderSurvives]
    exact binderWitness.bindersMapped binder binderSurvives arity
      sourceRelation sourceLookup
  · exact sourceCompiled
  · exact targetCompiled

/-- Pointwise semantic transport for one surviving occurrence inside the
selected material.  Child regions recurse under the fixed fresh relation. -/
theorem focusedSurvivingOccurrence_semantic
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {wrap : CheckedSelection input.val}
    {comprehension : CheckedOpenDiagram signature}
    {occurrences : List (AbstractionOccurrence input)}
    {raw : ConcreteDiagram}
    {sourceRels targetRels : RelCtx}
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (targetWellFormed : trace.diagram.WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (sourceFuel targetFuel : Nat)
    (parent : Fin input.val.regionCount)
    (parentSurvives : trace.domains.regions.survives parent = true)
    (notWrap : parent ≠ wrap.val.anchor)
    (sourceContext : ConcreteElaboration.WireContext input.val)
    (targetContext : ConcreteElaboration.WireContext trace.diagram)
    (context : ContextWitness trace sourceContext targetContext)
    (sourceBinders : ConcreteElaboration.BinderContext input.val sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext trace.diagram targetRels)
    (binderWitness : BinderWitness trace sourceBinders targetBinders)
    (sourceExact : sourceContext.Exact parent)
    (targetExact : targetContext.Exact (trace.regionMap parent))
    (sourceCover : sourceBinders.Covers parent)
    (targetCover : targetBinders.Covers (trace.regionMap parent))
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      input.val sourceBinders parent)
    (targetEnumeration : ConcreteElaboration.BinderContext.Enumeration
      trace.diagram targetBinders (trace.regionMap parent))
    (allowed : AbstractionAllowed input.val wrap.val.anchor direction parent)
    (recurseAt : ∀ (childDirection : ConcreteElaboration.SimulationDirection)
      (child : Fin input.val.regionCount),
      FixedRegionSimulation trace model named childDirection sourceFuel
        targetFuel child)
    (occurrence : ConcreteElaboration.LocalOccurrence input.val.regionCount
      input.val.nodeCount)
    {targetOccurrence : ConcreteElaboration.LocalOccurrence
      trace.diagram.regionCount trace.diagram.nodeCount}
    (localMember : occurrence ∈
      ConcreteElaboration.localOccurrences input.val parent)
    (mapped : trace.survivingOccurrence? occurrence = some targetOccurrence)
    (sourceItem : Item signature sourceContext.length sourceRels)
    (targetItem : Item signature targetContext.length targetRels)
    (sourceCompiled : ConcreteElaboration.compileOccurrenceWith? signature
      input.val (ConcreteElaboration.compileRegion? signature input.val
        sourceFuel) sourceContext sourceBinders occurrence = some sourceItem)
    (targetCompiled : ConcreteElaboration.compileOccurrenceWith? signature
      trace.diagram (ConcreteElaboration.compileRegion? signature trace.diagram
        targetFuel) targetContext targetBinders targetOccurrence =
          some targetItem) :
    ∀ (sourceEnvironment : Fin sourceContext.length → model.Carrier)
      (targetEnvironment : Fin targetContext.length → model.Carrier)
      (targetRelations : RelEnv model.Carrier targetRels),
      context.indexRelation.EnvironmentsAgree sourceEnvironment
          targetEnvironment →
      FixedRelationWitness (signature := signature) (input := input)
        (wrap := wrap) (comprehension := comprehension)
        (occurrences := occurrences) (raw := raw) trace model named
        targetBinders targetRelations →
      direction.Entails
        (denoteItem model named sourceEnvironment targetRelations
          (sourceItem.renameRelations binderWitness.relationMap))
        (denoteItem model named targetEnvironment targetRelations targetItem) := by
  cases occurrence with
  | node node =>
      by_cases survives : trace.domains.nodes.survives node = true
      · rw [trace.survivingOccurrence?_node node survives] at mapped
        cases targetOccurrence with
        | child targetChild => simp at mapped
        | node targetNode =>
            have targetEq := ConcreteElaboration.LocalOccurrence.node.inj
              (Option.some.inj mapped)
            subst targetNode
            have nodeRegion :=
              (ConcreteElaboration.mem_localOccurrences_node input.val parent
                node).1 localMember
            have semantic := trace.focusedSurvivingNode_semantic model named
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
            have targetEq := ConcreteElaboration.LocalOccurrence.child.inj
              (Option.some.inj mapped)
            subst targetChild
            have childParent :=
              (ConcreteElaboration.mem_localOccurrences_child input.val parent
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
            cases sourceKind : input.val.regions child with
            | sheet =>
                simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind]
                  at sourceCompiled
            | cut actualParent =>
                have parentEq : actualParent = parent := by
                  rw [sourceKind] at childParent
                  exact Option.some.inj childParent
                subst actualParent
                simp only [sourceKind, mapRegionShape] at childShape
                cases sourceResult : ConcreteElaboration.compileRegion? signature
                    input.val sourceFuel child sourceContext sourceBinders with
                | none =>
                    simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
                      sourceResult] at sourceCompiled
                | some sourceBody =>
                    simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
                      sourceResult] at sourceCompiled
                    subst sourceItem
                    cases targetResult : ConcreteElaboration.compileRegion? signature
                        trace.diagram targetFuel (trace.targetRegion child survives)
                        targetContext targetBinders with
                    | none =>
                        simp [ConcreteElaboration.compileOccurrenceWith?, childShape,
                          targetResult] at targetCompiled
                    | some targetBody =>
                        simp [ConcreteElaboration.compileOccurrenceWith?, childShape,
                          targetResult] at targetCompiled
                        subst targetItem
                        have childAllowed : AbstractionAllowed input.val
                            wrap.val.anchor direction.flip child :=
                          abstractionAllowed_cut input.val wrap.val.anchor direction
                            child parent sourceKind allowed
                        have targetResultMapped :
                            ConcreteElaboration.compileRegion? signature trace.diagram
                              targetFuel (trace.regionMap child) targetContext
                              targetBinders = some targetBody := by
                          rw [trace.regionMap_of_survives child survives]
                          exact targetResult
                        have bodies := recurseAt direction.flip child sourceContext
                          targetContext context sourceExact.nodup sourceBinders
                          targetBinders binderWitness
                          (ConcreteElaboration.BinderContext.covers_cut_child
                            sourceCover sourceKind)
                          (by
                            rw [trace.regionMap_of_survives child survives]
                            exact ConcreteElaboration.BinderContext.covers_cut_child
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
                cases sourceResult : ConcreteElaboration.compileRegion? signature
                    input.val sourceFuel child sourceContext sourcePushed with
                | none =>
                    simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
                      sourcePushed, sourceResult] at sourceCompiled
                | some sourceBody =>
                    simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
                      sourcePushed, sourceResult] at sourceCompiled
                    subst sourceItem
                    cases targetResult : ConcreteElaboration.compileRegion? signature
                        trace.diagram targetFuel (trace.targetRegion child survives)
                        targetContext targetPushed with
                    | none =>
                        simp [ConcreteElaboration.compileOccurrenceWith?, childShape,
                          targetPushed, targetResult] at targetCompiled
                    | some targetBody =>
                        simp [ConcreteElaboration.compileOccurrenceWith?, childShape,
                          targetPushed, targetResult] at targetCompiled
                        subst targetItem
                        let childWitness : BinderWitness trace sourcePushed
                            targetPushed := binderWitness.push child survives arity
                        have childAllowed : AbstractionAllowed input.val
                            wrap.val.anchor direction child :=
                          abstractionAllowed_bubble input.val wrap.val.anchor
                            direction child parent arity sourceKind allowed
                        have targetResultMapped :
                            ConcreteElaboration.compileRegion? signature trace.diagram
                              targetFuel (trace.regionMap child) targetContext
                              targetPushed = some targetBody := by
                          rw [trace.regionMap_of_survives child survives]
                          exact targetResult
                        have bodies := recurseAt direction child sourceContext
                          targetContext context sourceExact.nodup sourcePushed
                          targetPushed childWitness
                          (ConcreteElaboration.BinderContext.push_covers_bubble_child
                            sourceCover sourceKind)
                          (by
                            rw [trace.regionMap_of_survives child survives]
                            exact ConcreteElaboration.BinderContext.push_covers_bubble_child
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

end VisualProof.Rule
