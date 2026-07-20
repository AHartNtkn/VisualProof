import VisualProof.Rule.Soundness.Comprehension.AbstractionFocusedRegionSemantic

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

namespace AbstractionRawTrace

/-- Complete regular-frame simulation. The only unfinished field is the
focused wrap kernel, which owns existential relation introduction and every
occurrence replacement inside the wrapped material. -/
noncomputable def semanticSimulation
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {wrap : CheckedSelection input.val}
    {comprehension : CheckedOpenDiagram signature}
    {occurrences : List (AbstractionOccurrence input)}
    {raw : ConcreteDiagram}
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (payload : ComprehensionAbstractPayload input wrap comprehension occurrences)
    (targetWellFormed : trace.diagram.WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature) :
    ConcreteElaboration.ConcreteSemanticSimulation signature input.val
      trace.diagram model named where
  source_wellFormed := input.property
  target_wellFormed := targetWellFormed
  regionMap := trace.regionMap
  binderMap := trace.regionMap
  Distinguished := fun region => ¬ trace.FrameRegular region
  occurrenceMap := fun region regular =>
    trace.occurrenceMap region (Classical.not_not.mp regular)
  occurrenceMap_node := by
    intro region regular node nodeRegion
    let regular' := Classical.not_not.mp regular
    exact ⟨trace.targetNode node
      (trace.node_survives_of_regular region regular' node nodeRegion),
      trace.occurrenceMap_node_of_region region regular' node nodeRegion⟩
  occurrenceMap_child := by simp
  root_eq := trace.regionMap_root.symm
  region_shape := by
    intro parent regular child childParent
    have shape := trace.region_shape_of_regular parent
      (Classical.not_not.mp regular) child childParent
    cases sourceShape : input.val.regions child <;>
      simp only [sourceShape] at shape ⊢ <;> exact shape
  localOccurrences_map := by
    intro region regular
    exact trace.localOccurrences_map_of_regular payload region
      (Classical.not_not.mp regular)
  BinderWitness := fun sourceBinders targetBinders =>
    BinderWitness trace sourceBinders targetBinders
  relationMap := fun witness => witness.relationMap
  binders_empty := BinderWitness.empty trace
  binders_push := by
    intro sourceRels targetRels sourceBinders targetBinders witness child parent
      arity childKind regular
    let regular' := Classical.not_not.mp regular
    have childParent : (input.val.regions child).parent? = some parent := by
      rw [childKind]
      rfl
    have survives := trace.child_survives_of_regular parent child regular'
      childParent
    exact witness.pushMapped child survives arity
  relationMap_push := by
    intro sourceRels targetRels sourceBinders targetBinders witness child parent
      arity childKind regular
    let regular' := Classical.not_not.mp regular
    have childParent : (input.val.regions child).parent? = some parent := by
      rw [childKind]
      rfl
    have survives := trace.child_survives_of_regular parent child regular'
      childParent
    exact witness.relationMap_pushMapped child survives arity
  Allowed := AbstractionAllowed input.val wrap.val.anchor
  allowed_cut := by
    intro direction child parent childKind regular allowed
    exact abstractionAllowed_cut input.val wrap.val.anchor direction child parent
      childKind allowed
  allowed_bubble := by
    intro direction child parent arity childKind regular allowed
    exact abstractionAllowed_bubble input.val wrap.val.anchor direction child
      parent arity childKind allowed
  ContextWitness := fun sourceContext targetContext =>
    PLift (ContextWitness trace sourceContext targetContext)
  AtRegion := fun _ region => trace.OuterReachable region
  indexRelation := fun context => context.down.indexRelation
  extendContext := by
    intro sourceContext targetContext context region regular sourceExact
      targetExact
    exact PLift.up
      (context.down.extend region (Classical.not_not.mp regular).1)
  extendFocusedContext := by
    intro sourceContext targetContext context region reachable focused
      sourceExact targetExact
    exact PLift.up (context.down.extend region
      (trace.survives_of_reachable payload region reachable.1))
  at_child := by
    intro sourceContext targetContext context parent regular sourceExact
      targetExact child reachable childParent
    exact trace.outerReachable_child_of_regular payload parent child reachable
      (Classical.not_not.mp regular) childParent
  at_extended := by
    intro sourceContext targetContext context region regular sourceExact
      targetExact reachable
    exact reachable
  at_focused_child := by
    intro sourceContext targetContext context parent focused sourceExact
      targetExact child reachable sourceParent targetParent
    have parentEq := trace.outerReachable_focused_eq payload parent reachable
      focused
    subst parent
    have childSurvives := trace.reachable_child_of_focus targetWellFormed
      wrap.val.anchor child reachable.1 targetParent
    refine ⟨childSurvives, ?_⟩
    by_cases childEq : child = wrap.val.anchor
    · exact Or.inl childEq
    · apply Or.inr
      intro selected
      have targetDirect : child ∉ wrap.val.childRoots := by
        rw [trace.regionMap_of_survives child childSurvives,
          trace.regionMap_of_survives wrap.val.anchor
            (wrap_anchor_survives payload)] at targetParent
        exact ((trace.targetRegion_parent_wrap_iff child childSurvives
          (wrap_anchor_survives payload)).1 targetParent).2
      obtain ⟨root, rootMember, encloses⟩ :=
        (wrap.mem_selectedRegions child).1 selected
      have rootEq : root = child := by
        have rootParent := wrap.property.childRoots_direct root rootMember
        rcases ConcreteElaboration.encloses_direct_child sourceParent encloses with
          equal | enclosesParent
        · exact equal
        · exact False.elim
            (ConcreteElaboration.checked_direct_child_not_encloses_parent
              input.property rootParent enclosesParent)
      exact targetDirect (rootEq ▸ rootMember)
  localTransport := by
    intro sourceRels targetRels direction fuelSource fuelTarget sourceContext
      targetContext context sourceBinders targetBinders binderWitness region
      reachable regular allowed sourceExact targetExact sourceBindersCover
      targetBindersCover sourceEnumeration targetEnumeration sourceItems
      targetItems sourceCompiled targetCompiled itemSemantics relationEnvironment
    letI : Nonempty model.Carrier :=
      ConcreteElaboration.lambdaModel_carrier_nonempty model
    apply ConcreteElaboration.directionalLocalTransport_of_agreement direction
      sourceContext targetContext region (trace.regionMap region)
      context.down.indexRelation
      (context.down.extend region
        (Classical.not_not.mp regular).1).indexRelation
      model named (sourceItems.renameRelations binderWitness.relationMap)
      targetItems
    · exact trace.regularEnvironmentSelection targetWellFormed direction
        sourceContext targetContext context.down region
          (Classical.not_not.mp regular) sourceExact
    · exact itemSemantics
  nodeSemantic := by
    intro sourceRels targetRels direction region sourceContext targetContext
      context reachable sourceNodup targetNodup sourceBinders targetBinders
      allowed binderWitness sourceNode targetNode regular mapped nodeRegion
      sourceItem targetItem sourceCompiled targetCompiled
    let regular' := Classical.not_not.mp regular
    have canonical := trace.occurrenceMap_node_of_region region regular'
      sourceNode nodeRegion
    rw [canonical] at mapped
    have targetNodeEq := ConcreteElaboration.LocalOccurrence.node.inj mapped
    subst targetNode
    exact trace.regularNode_itemSimulation model named direction sourceContext
      targetContext context.down sourceNodup sourceBinders targetBinders
      binderWitness
      region regular' sourceNode nodeRegion sourceItem targetItem sourceCompiled
      targetCompiled
  focusedRegionKernel := by
    intro sourceRels targetRels direction fuelSource fuelTarget region
      sourceContext targetContext context sourceBinders targetBinders reachable
      focused allowed binderWitness sourceExact targetExact sourceBindersCover
      targetBindersCover sourceEnumeration targetEnumeration recurse recurseAt
      sourceItems targetItems sourceCompiled targetCompiled
    have regionFocus : region = wrap.val.anchor :=
      trace.outerReachable_focused_eq payload region reachable focused
    subst region
    have directionEq := abstractionAllowed_focus_forward input.val
      wrap.val.anchor direction allowed
    subst direction
    let sourceRecurse : ∀ {rels : RelCtx},
        (region : Fin input.val.regionCount) →
        (context : ConcreteElaboration.WireContext input.val) →
        ConcreteElaboration.BinderContext input.val rels →
        Option (Region signature context.length rels) :=
      fun {rels} => ConcreteElaboration.compileRegion? signature input.val
        fuelSource
    let targetRecurse : ∀ {rels : RelCtx},
        (region : Fin trace.diagram.regionCount) →
        (context : ConcreteElaboration.WireContext trace.diagram) →
        ConcreteElaboration.BinderContext trace.diagram rels →
        Option (Region signature context.length rels) :=
      fun {rels} => ConcreteElaboration.compileRegion? signature trace.diagram
        fuelTarget
    let sourceExtended := sourceContext.extend wrap.val.anchor
    let targetExtended := targetContext.extend
      (trace.regionMap wrap.val.anchor)
    have sourcePartition := ModalSoundness.anchorOccurrences_perm_partition
      input.val wrap
    obtain ⟨sourcePartitionItems, sourcePartitionCompiled⟩ :=
      ConcreteElaboration.compileOccurrencesWith?_complete sourceRecurse
        sourceExtended sourceBinders
        (ModalSoundness.keptOccurrences input.val wrap ++
          ModalSoundness.selectedOccurrences input.val wrap) (by
            intro occurrence member
            exact ModalSoundness.compileOccurrence_success_of_mem input.val
              sourceRecurse sourceExtended sourceBinders sourceCompiled
              ((sourcePartition.mem_iff).1 member))
    obtain ⟨sourceKeptItems, sourceSelectedItems, sourceKeptCompiled,
        sourceSelectedCompiled, sourcePartitionEq⟩ :=
      ConcreteElaboration.compileOccurrencesWith?_append_split sourceRecurse
        sourceExtended sourceBinders
        (ModalSoundness.keptOccurrences input.val wrap)
        (ModalSoundness.selectedOccurrences input.val wrap)
        sourcePartitionItems sourcePartitionCompiled
    have targetPartition :
        (ConcreteElaboration.localOccurrences trace.diagram
            (trace.regionMap wrap.val.anchor)).Perm
          ((ModalSoundness.keptOccurrences input.val wrap).map
              trace.survivorOccurrence ++
            [(ConcreteElaboration.LocalOccurrence.child trace.bubble :
              ConcreteElaboration.LocalOccurrence trace.diagram.regionCount
                trace.diagram.nodeCount)]) := by
      rw [trace.regionMap_of_survives wrap.val.anchor
        (wrap_anchor_survives payload)]
      simpa [trace.kept_filterMap_eq_map payload] using
        trace.wrapAnchorLocalOccurrences payload
    obtain ⟨targetPartitionItems, targetPartitionCompiled⟩ :=
      ConcreteElaboration.compileOccurrencesWith?_complete targetRecurse
        targetExtended targetBinders
        ((ModalSoundness.keptOccurrences input.val wrap).map
            trace.survivorOccurrence ++
          [(ConcreteElaboration.LocalOccurrence.child trace.bubble :
            ConcreteElaboration.LocalOccurrence trace.diagram.regionCount
              trace.diagram.nodeCount)]) (by
            intro occurrence member
            exact ModalSoundness.compileOccurrence_success_of_mem trace.diagram
              targetRecurse targetExtended targetBinders targetCompiled
              ((targetPartition.mem_iff).2 member))
    obtain ⟨targetKeptItems, targetBubbleItems, targetKeptCompiled,
        targetBubbleCompiled, targetPartitionEq⟩ :=
      ConcreteElaboration.compileOccurrencesWith?_append_split targetRecurse
        targetExtended targetBinders
        ((ModalSoundness.keptOccurrences input.val wrap).map
          trace.survivorOccurrence)
        [ConcreteElaboration.LocalOccurrence.child trace.bubble]
        targetPartitionItems targetPartitionCompiled
    simp only [ConcreteElaboration.compileOccurrencesWith?]
      at targetBubbleCompiled
    dsimp only [targetRecurse] at targetBubbleCompiled
    simp only [ConcreteElaboration.compileOccurrenceWith?, trace.diagram_bubble]
      at targetBubbleCompiled
    let targetPushed := targetBinders.push trace.bubble
      comprehension.val.boundary.length
    cases bubbleResult : ConcreteElaboration.compileRegion? signature
        trace.diagram fuelTarget trace.bubble targetExtended targetPushed with
    | none => simp [targetPushed, bubbleResult] at targetBubbleCompiled
    | some bubbleBody =>
        simp [targetPushed, bubbleResult] at targetBubbleCompiled
        subst targetBubbleItems
        cases fuelTarget with
        | zero =>
            simp [ConcreteElaboration.compileRegion?] at bubbleResult
        | succ bubbleFuel =>
            simp only [ConcreteElaboration.compileRegion?] at bubbleResult
            obtain ⟨bubbleItems, bubbleItemsCompiled, bubbleBodyEq⟩ :=
              Option.bind_eq_some_iff.mp bubbleResult
            have bubbleBodyEq' :
                ConcreteElaboration.finishRegion trace.diagram targetExtended
                  trace.bubble bubbleItems = bubbleBody :=
              Option.some.inj bubbleBodyEq
            subst bubbleBody
            let focusedContext := context.down.extend wrap.val.anchor
              (wrap_anchor_survives payload)
            have keptPointwise : ∀ occurrence,
                occurrence ∈ ModalSoundness.keptOccurrences input.val wrap →
                ∀ sourceItem targetItem,
                ConcreteElaboration.compileOccurrenceWith? signature input.val
                    sourceRecurse sourceExtended sourceBinders occurrence =
                      some sourceItem →
                ConcreteElaboration.compileOccurrenceWith? signature
                    trace.diagram targetRecurse targetExtended targetBinders
                    (trace.survivorOccurrence occurrence) = some targetItem →
                ConcreteElaboration.ItemSimulation model named .forward
                  focusedContext.indexRelation
                  (sourceItem.renameRelations binderWitness.relationMap)
                  targetItem := by
              intro occurrence member sourceItem targetItem sourceOccurrence
                targetOccurrence
              exact trace.focusedKeptOccurrence_itemSimulation payload
                targetWellFormed model named .forward fuelSource
                (bubbleFuel + 1) sourceExtended targetExtended focusedContext
                sourceBinders targetBinders binderWitness sourceExact targetExact
                sourceBindersCover targetBindersCover sourceEnumeration
                targetEnumeration allowed
                (fun childFuelTarget childSourceContext childTargetContext
                    childContext => recurseAt childFuelTarget childSourceContext
                      childTargetContext (PLift.up childContext)) occurrence member
                sourceItem targetItem (by
                  simpa [sourceRecurse] using sourceOccurrence)
                (by simpa [targetRecurse] using targetOccurrence)
            have keptSimulation :=
              ConcreteElaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
                model named .forward sourceRecurse targetRecurse sourceExtended
                targetExtended sourceBinders targetBinders
                focusedContext.indexRelation binderWitness.relationMap
                trace.survivorOccurrence
                (ModalSoundness.keptOccurrences input.val wrap) keptPointwise
                sourceKeptItems targetKeptItems sourceKeptCompiled
                targetKeptCompiled
            let selectedSurvivors := trace.survivingSources
              (ModalSoundness.selectedOccurrences input.val wrap)
            let selectedAtWrap := selectedAt input occurrences wrap.val.anchor
            let targetSelectedSurvivors :=
              selectedSurvivors.map trace.survivorOccurrence
            let indices := anchorIndices occurrences wrap.val.anchor
            let targetAtoms : List (ConcreteElaboration.LocalOccurrence
                trace.diagram.regionCount trace.diagram.nodeCount) :=
              indices.map fun index =>
                ConcreteElaboration.LocalOccurrence.node (trace.targetAtom index)
            have sourceSelectedPartition :
                (selectedSurvivors ++ selectedAtWrap).Perm
                  (ModalSoundness.selectedOccurrences input.val wrap) := by
              simpa [selectedSurvivors, selectedAtWrap] using
                trace.selectedOccurrences_perm_focusedPartition payload
            have targetBubblePartition :
                (ConcreteElaboration.localOccurrences trace.diagram
                    trace.bubble).Perm
                  (targetSelectedSurvivors ++ targetAtoms) := by
              simpa [targetSelectedSurvivors, selectedSurvivors, targetAtoms,
                indices, atomsAt, anchorIndices,
                trace.survivingSources_map_survivor] using
                  trace.bubbleLocalOccurrences payload
            let bubbleContext := targetExtended.extend trace.bubble
            obtain ⟨sourceSelectedPartitionItems,
                sourceSelectedPartitionCompiled⟩ :=
              ConcreteElaboration.compileOccurrencesWith?_complete sourceRecurse
                sourceExtended sourceBinders
                (selectedSurvivors ++ selectedAtWrap) (by
                  intro occurrence member
                  exact ModalSoundness.compileOccurrence_success_of_mem input.val
                    sourceRecurse sourceExtended sourceBinders
                    sourceSelectedCompiled
                    ((sourceSelectedPartition.mem_iff).1 member))
            obtain ⟨sourceSurvivorItems, sourceFamilyAggregateItems,
                sourceSurvivorCompiled, sourceFamilyAggregateCompiled,
                sourceSelectedPartitionEq⟩ :=
              ConcreteElaboration.compileOccurrencesWith?_append_split
                sourceRecurse sourceExtended sourceBinders selectedSurvivors
                selectedAtWrap sourceSelectedPartitionItems
                sourceSelectedPartitionCompiled
            let bubbleRecurse : ∀ {rels : RelCtx},
                (region : Fin trace.diagram.regionCount) →
                (context : ConcreteElaboration.WireContext trace.diagram) →
                ConcreteElaboration.BinderContext trace.diagram rels →
                Option (Region signature context.length rels) :=
              fun {rels} => ConcreteElaboration.compileRegion? signature
                trace.diagram bubbleFuel
            obtain ⟨targetBubblePartitionItems,
                targetBubblePartitionCompiled⟩ :=
              ConcreteElaboration.compileOccurrencesWith?_complete bubbleRecurse
                bubbleContext targetPushed
                (targetSelectedSurvivors ++ targetAtoms) (by
                  intro occurrence member
                  exact ModalSoundness.compileOccurrence_success_of_mem
                    trace.diagram bubbleRecurse bubbleContext targetPushed
                    bubbleItemsCompiled
                    ((targetBubblePartition.mem_iff).2 member))
            obtain ⟨targetSurvivorItems, targetAtomItems,
                targetSurvivorCompiled, targetAtomCompiled,
                targetBubblePartitionEq⟩ :=
              ConcreteElaboration.compileOccurrencesWith?_append_split
                bubbleRecurse bubbleContext targetPushed
                targetSelectedSurvivors targetAtoms
                targetBubblePartitionItems targetBubblePartitionCompiled
            have sourceBlockExists : ∀ index, index ∈ indices →
                ∃ items : ItemSeq signature sourceExtended.length sourceRels,
                  ConcreteElaboration.compileOccurrencesWith? signature
                    input.val sourceRecurse sourceExtended sourceBinders
                    (ModalSoundness.selectedOccurrences input.val
                      (occurrences.get index).selection) = some items := by
              intro index indexMember
              apply ConcreteElaboration.compileOccurrencesWith?_complete
              intro occurrence occurrenceMember
              apply ModalSoundness.compileOccurrence_success_of_mem input.val
                sourceRecurse sourceExtended sourceBinders
                sourceFamilyAggregateCompiled
              exact (mem_selectedAt input occurrences wrap.val.anchor
                occurrence).2 ⟨index,
                  (mem_anchorIndices occurrences wrap.val.anchor index).1
                    indexMember,
                  occurrenceMember⟩
            let sourceFamilyItems : Fin occurrences.length →
                ItemSeq signature sourceExtended.length sourceRels :=
              fun index => if member : index ∈ indices then
                Classical.choose (sourceBlockExists index member)
              else .nil
            have sourceFamilyCompiled : ∀ index, index ∈ indices →
                ConcreteElaboration.compileOccurrencesWith? signature
                  input.val sourceRecurse sourceExtended sourceBinders
                  (ModalSoundness.selectedOccurrences input.val
                    (occurrences.get index).selection) =
                      some (sourceFamilyItems index) := by
              intro index member
              dsimp only [sourceFamilyItems]
              rw [dif_pos member]
              exact Classical.choose_spec (sourceBlockExists index member)
            have sourceFamilyCompiler := compileOccurrenceFamilyItems
              sourceRecurse sourceExtended sourceBinders indices
              (fun index => ModalSoundness.selectedOccurrences input.val
                (occurrences.get index).selection)
              sourceFamilyItems sourceFamilyCompiled
            have sourceFamilyEq :
                occurrenceFamilyItems sourceFamilyItems indices =
                  sourceFamilyAggregateItems := by
              apply Option.some.inj
              exact sourceFamilyCompiler.symm.trans (by
                simpa [selectedAtWrap, selectedAt, indices] using
                  sourceFamilyAggregateCompiled)
            have targetAtomExists : ∀ index, index ∈ indices →
                ∃ item : Item signature bubbleContext.length
                    (comprehension.val.boundary.length :: targetRels),
                  ConcreteElaboration.compileNode? signature trace.diagram
                    bubbleContext targetPushed (trace.targetAtom index) =
                      some item := by
              intro index indexMember
              obtain ⟨item, compiled⟩ :=
                ModalSoundness.compileOccurrence_success_of_mem trace.diagram
                  bubbleRecurse bubbleContext targetPushed targetAtomCompiled
                  (List.mem_map.mpr ⟨index, indexMember, rfl⟩)
              exact ⟨item, by
                simpa [ConcreteElaboration.compileOccurrenceWith?] using
                  compiled⟩
            let targetFamilyItems : Fin occurrences.length →
                Item signature bubbleContext.length
                  (comprehension.val.boundary.length :: targetRels) :=
              fun index => if member : index ∈ indices then
                Classical.choose (targetAtomExists index member)
              else .cut (.mk 0 .nil)
            have targetFamilyCompiled : ∀ index, index ∈ indices →
                ConcreteElaboration.compileNode? signature trace.diagram
                  bubbleContext targetPushed (trace.targetAtom index) =
                    some (targetFamilyItems index) := by
              intro index member
              dsimp only [targetFamilyItems]
              rw [dif_pos member]
              exact Classical.choose_spec (targetAtomExists index member)
            have targetFamilyCompiler := compileOccurrenceFamilyAtomItems
              bubbleRecurse bubbleContext targetPushed indices
              (fun index => ConcreteElaboration.LocalOccurrence.node
                (trace.targetAtom index)) targetFamilyItems (by
                  intro index member
                  simpa [ConcreteElaboration.compileOccurrenceWith?] using
                    targetFamilyCompiled index member)
            have targetFamilyEq :
                occurrenceFamilyAtomItems targetFamilyItems indices =
                  targetAtomItems := by
              apply Option.some.inj
              exact targetFamilyCompiler.symm.trans (by
                simpa [targetAtoms] using targetAtomCompiled)
            have sourceSelectedCanonicalCompiled :
                ConcreteElaboration.compileOccurrencesWith? signature input.val
                  sourceRecurse sourceExtended sourceBinders
                  (selectedSurvivors ++ selectedAtWrap) =
                    some (sourceSurvivorItems.append
                      sourceFamilyAggregateItems) := by
              rw [← sourceSelectedPartitionEq]
              exact sourceSelectedPartitionCompiled
            have targetBubbleCanonicalCompiled :
                ConcreteElaboration.compileOccurrencesWith? signature
                  trace.diagram bubbleRecurse bubbleContext targetPushed
                  (targetSelectedSurvivors ++ targetAtoms) =
                    some (targetSurvivorItems.append targetAtomItems) := by
              rw [← targetBubblePartitionEq]
              exact targetBubblePartitionCompiled
            have sourceSelectedCanonicalNodup :
                (selectedSurvivors ++ selectedAtWrap).Nodup :=
              (sourceSelectedPartition.nodup_iff).2
                (selectedOccurrences_nodup input wrap)
            have targetBubbleCanonicalNodup :
                (targetSelectedSurvivors ++ targetAtoms).Nodup :=
              (targetBubblePartition.nodup_iff).1
                (ConcreteElaboration.localOccurrences_nodup trace.diagram
                  trace.bubble)
            have selectedSurvivorMembers : ∀ occurrence,
                occurrence ∈ selectedSurvivors → occurrence ∈
                  ModalSoundness.selectedOccurrences input.val wrap := by
              intro occurrence member
              exact (mem_survivingSources trace
                (ModalSoundness.selectedOccurrences input.val wrap)
                occurrence).1 member |>.1
            have selectedSurvivorMaps : ∀ occurrence,
                occurrence ∈ selectedSurvivors →
                  ∃ target,
                    trace.survivingOccurrence? occurrence = some target := by
              intro occurrence member
              exact Option.isSome_iff_exists.mp
                ((mem_survivingSources trace
                  (ModalSoundness.selectedOccurrences input.val wrap)
                  occurrence).1 member |>.2)
            have fixedRecurseAt : ∀
                (childDirection : ConcreteElaboration.SimulationDirection)
                (child : Fin input.val.regionCount),
                child ∈ wrap.selectedRegions →
                trace.domains.regions.survives child = true →
                child ≠ wrap.val.anchor →
                AbstractionAllowed input.val wrap.val.anchor childDirection
                    child →
                  FixedRegionSimulation trace model named childDirection
                    fuelSource bubbleFuel child := by
              intro childDirection child childSelected childSurvives
                childNotWrap childAllowed
              exact trace.fixedRegionSimulation payload targetWellFormed model
                named childDirection fuelSource bubbleFuel child childSurvives
                childNotWrap childSelected childAllowed
            have bubbleContextEq : bubbleContext = targetExtended := by
              exact trace.extend_bubble_eq targetExtended
            subst bubbleContext
            have selectedContext : ContextWitness trace sourceExtended
                (targetExtended.extend trace.bubble) :=
              focusedContext.castTarget (trace.extend_bubble_eq targetExtended)
            have selectedTargetExact :
                (targetExtended.extend trace.bubble).Exact
                  (trace.regionMap wrap.val.anchor) := by
              rw [trace.extend_bubble_eq]
              exact targetExact
            have selectedSimulation :=
              trace.focusedSelectedSurvivingSources_semantic payload
                targetWellFormed model named fuelSource bubbleFuel
                sourceExtended (targetExtended.extend trace.bubble)
                selectedContext sourceBinders targetBinders binderWitness
                sourceExact selectedTargetExact
                sourceBindersCover targetBindersCover sourceEnumeration
                targetEnumeration allowed fixedRecurseAt selectedSurvivors
                selectedSurvivorMembers selectedSurvivorMaps
                sourceSurvivorItems targetSurvivorItems
                sourceSurvivorCompiled (by
                  simpa [targetPushed, targetSelectedSurvivors] using
                    targetSurvivorCompiled)
            have sourceCanonicalNodup :
                (ModalSoundness.keptOccurrences input.val wrap ++
                  ModalSoundness.selectedOccurrences input.val wrap).Nodup :=
              (sourcePartition.nodup_iff).2
                (ConcreteElaboration.localOccurrences_nodup input.val
                  wrap.val.anchor)
            have targetCanonicalNodup :
                ((ModalSoundness.keptOccurrences input.val wrap).map
                    trace.survivorOccurrence ++
                  [(ConcreteElaboration.LocalOccurrence.child trace.bubble :
                    ConcreteElaboration.LocalOccurrence trace.diagram.regionCount
                      trace.diagram.nodeCount)]).Nodup :=
              (targetPartition.nodup_iff).1
                (ConcreteElaboration.localOccurrences_nodup trace.diagram
                  (trace.regionMap wrap.val.anchor))
            letI : Nonempty model.Carrier :=
              ConcreteElaboration.lambdaModel_carrier_nonempty model
            intro sourceEnvironment targetEnvironment targetRelations
              environments
            rw [ConcreteElaboration.finishRegion_renameRelations]
            intro sourceDenotes
            obtain ⟨sourceLocal, sourceItemsDenote⟩ :=
              (DoubleCutElimTrace.finishRegion_denote_iff input.val
                sourceContext wrap.val.anchor
                (sourceItems.renameRelations binderWitness.relationMap)
                model named sourceEnvironment targetRelations).1 sourceDenotes
            obtain ⟨targetLocal, focusedAgreement⟩ :=
              trace.survivorEnvironmentSelection targetWellFormed .forward
                sourceContext targetContext context.down wrap.val.anchor
                (wrap_anchor_survives payload) sourceExact sourceEnvironment
                targetEnvironment environments sourceLocal
            let sourceLocalEnvironment :=
              ConcreteElaboration.extendedEnvironment sourceContext
                wrap.val.anchor sourceEnvironment sourceLocal
            let targetLocalEnvironment :=
              ConcreteElaboration.extendedEnvironment targetContext
                (trace.regionMap wrap.val.anchor) targetEnvironment targetLocal
            let sourceRelations := RelEnv.pullback
              binderWitness.relationMap targetRelations
            have baseRelationAgreement := RelEnv.pullback_agrees
              binderWitness.relationMap targetRelations
            have sourceRawDenote : denoteItemSeq model named
                sourceLocalEnvironment sourceRelations sourceItems :=
              (denoteItemSeq_renameRelations model named
                binderWitness.relationMap sourceRelations targetRelations
                baseRelationAgreement sourceLocalEnvironment sourceItems).1
                  sourceItemsDenote
            have sourcePermutation := compileOccurrences_perm_denote_iff
              input.val sourceRecurse sourceExtended sourceBinders
              sourcePartition sourceCanonicalNodup
              (ConcreteElaboration.localOccurrences_nodup input.val
                wrap.val.anchor)
              sourcePartitionCompiled sourceCompiled model named
              sourceLocalEnvironment sourceRelations
            have sourceCanonicalDenote := sourcePermutation.mpr sourceRawDenote
            rw [sourcePartitionEq] at sourceCanonicalDenote
            have sourceParts :=
              (denoteItemSeq_append model named sourceLocalEnvironment
                sourceRelations sourceKeptItems sourceSelectedItems).1
                sourceCanonicalDenote
            have sourceKeptRenamed : denoteItemSeq model named
                sourceLocalEnvironment targetRelations
                (sourceKeptItems.renameRelations binderWitness.relationMap) :=
              (denoteItemSeq_renameRelations model named
                binderWitness.relationMap sourceRelations targetRelations
                baseRelationAgreement sourceLocalEnvironment
                sourceKeptItems).2 sourceParts.1
            have targetKeptDenote := keptSimulation sourceLocalEnvironment
              targetLocalEnvironment targetRelations focusedAgreement
              sourceKeptRenamed
            have sourceSelectedPermutation :=
              compileOccurrences_perm_denote_iff input.val sourceRecurse
                sourceExtended sourceBinders sourceSelectedPartition
                sourceSelectedCanonicalNodup
                (selectedOccurrences_nodup input wrap)
                sourceSelectedCanonicalCompiled sourceSelectedCompiled model
                named sourceLocalEnvironment sourceRelations
            have sourceSelectedCanonicalDenote :=
              sourceSelectedPermutation.mpr sourceParts.2
            have sourceSelectedParts :=
              (denoteItemSeq_append model named sourceLocalEnvironment
                sourceRelations sourceSurvivorItems
                sourceFamilyAggregateItems).1 sourceSelectedCanonicalDenote
            let freshRelation := abstractionRelation
              (signature := signature) comprehension model named
            let freshRelations : RelEnv model.Carrier
                (comprehension.val.boundary.length :: targetRels) :=
              (freshRelation, targetRelations)
            let freshWitness := binderWitness.intoFreshBubble
              comprehension.val.boundary.length
            have freshRelationAgreement : RelEnv.Agrees
                freshWitness.relationMap sourceRelations freshRelations := by
              intro arity relation
              simpa [freshWitness, BinderWitness.intoFreshBubble,
                BinderWitness.weakenRelationMap, freshRelations,
                RelEnv.lookup, ConcreteElaboration.BinderContext.liftVar]
                using baseRelationAgreement arity relation
            have sourceSurvivorRenamed : denoteItemSeq model named
                sourceLocalEnvironment freshRelations
                (sourceSurvivorItems.renameRelations
                  freshWitness.relationMap) :=
              (denoteItemSeq_renameRelations model named
                freshWitness.relationMap sourceRelations freshRelations
                freshRelationAgreement sourceLocalEnvironment
                sourceSurvivorItems).2 sourceSelectedParts.1
            let bubbleLocal := trace.emptyBubbleEnvironment model.Carrier
            let targetBubbleEnvironment : Fin
                (targetExtended.extend trace.bubble).length → model.Carrier :=
              fun index => targetLocalEnvironment
                (Fin.cast (congrArg List.length
                  (trace.extend_bubble_eq targetExtended)) index)
            have selectedAgreement :
                selectedContext.indexRelation.EnvironmentsAgree
                  sourceLocalEnvironment targetBubbleEnvironment := by
              exact focusedContext.castTarget_agrees
                (trace.extend_bubble_eq targetExtended) sourceLocalEnvironment
                targetLocalEnvironment focusedAgreement
            have fixedFresh := FixedRelationWitness.fresh trace model named
              targetBinders targetRelations
            have targetSurvivorDenote := selectedSimulation
              sourceLocalEnvironment targetBubbleEnvironment freshRelations
              selectedAgreement fixedFresh sourceSurvivorRenamed
            have anchored : ∀ index, index ∈ indices →
                (occurrences.get index).selection.val.anchor =
                  wrap.val.anchor := by
              intro index member
              exact (mem_anchorIndices occurrences wrap.val.anchor index).1
                member
            have sourceFamilyDenote : denoteItemSeq model named
                sourceLocalEnvironment sourceRelations
                (occurrenceFamilyItems sourceFamilyItems indices) := by
              rw [sourceFamilyEq]
              exact sourceSelectedParts.2
            have targetFamilyDenote := trace.occurrenceFamily_forward payload
              model named fuelSource wrap.val.anchor indices anchored
              sourceExtended (targetExtended.extend trace.bubble)
              selectedContext sourceBinders targetPushed sourceBindersCover
              sourceEnumeration sourceExact sourceFamilyItems targetFamilyItems
              sourceFamilyCompiled targetFamilyCompiled sourceLocalEnvironment
              targetBubbleEnvironment sourceRelations freshRelations fixedFresh
              selectedAgreement sourceFamilyDenote
            have targetBubbleCanonicalDenote : denoteItemSeq model named
                targetBubbleEnvironment freshRelations
                (targetSurvivorItems.append targetAtomItems) := by
              apply (denoteItemSeq_append model named targetBubbleEnvironment
                freshRelations targetSurvivorItems targetAtomItems).2
              refine ⟨targetSurvivorDenote, ?_⟩
              rw [← targetFamilyEq]
              exact targetFamilyDenote
            have targetBubblePermutation :=
              compileOccurrences_perm_denote_iff trace.diagram bubbleRecurse
                (targetExtended.extend trace.bubble) targetPushed
                targetBubblePartition
                (ConcreteElaboration.localOccurrences_nodup trace.diagram
                  trace.bubble) targetBubbleCanonicalNodup bubbleItemsCompiled
                targetBubbleCanonicalCompiled model named
                targetBubbleEnvironment freshRelations
            have bubbleItemsDenote :=
              targetBubblePermutation.mpr targetBubbleCanonicalDenote
            have bubbleItemsDenoteActual : denoteItemSeq model named
                (ConcreteElaboration.extendedEnvironment targetExtended
                  trace.bubble targetLocalEnvironment bubbleLocal)
                freshRelations bubbleItems := by
              rw [trace.extendedEnvironment_bubble_empty]
              exact bubbleItemsDenote
            have bubbleBodyDenote : denoteRegion model named
                targetLocalEnvironment freshRelations
                (ConcreteElaboration.finishRegion trace.diagram targetExtended
                  trace.bubble bubbleItems) :=
              (DoubleCutElimTrace.finishRegion_denote_iff trace.diagram
                targetExtended trace.bubble bubbleItems model named
                targetLocalEnvironment freshRelations).2
                  ⟨bubbleLocal, bubbleItemsDenoteActual⟩
            have targetBubbleDenote : denoteItem model named
                targetLocalEnvironment targetRelations
                (.bubble comprehension.val.boundary.length
                  (ConcreteElaboration.finishRegion trace.diagram targetExtended
                    trace.bubble bubbleItems)) := by
              simp only [bubble_denotes_exists]
              exact ⟨freshRelation, bubbleBodyDenote⟩
            have targetCanonicalDenote : denoteItemSeq model named
                targetLocalEnvironment targetRelations
                (targetKeptItems.append (.cons
                  (.bubble comprehension.val.boundary.length
                    (ConcreteElaboration.finishRegion trace.diagram
                      targetExtended trace.bubble bubbleItems)) .nil)) := by
              apply (denoteItemSeq_append model named targetLocalEnvironment
                targetRelations targetKeptItems _).2
              exact ⟨targetKeptDenote, by simpa using targetBubbleDenote⟩
            have targetCanonicalCompiled :
                ConcreteElaboration.compileOccurrencesWith? signature
                  trace.diagram targetRecurse targetExtended targetBinders
                  ((ModalSoundness.keptOccurrences input.val wrap).map
                      trace.survivorOccurrence ++
                    [(ConcreteElaboration.LocalOccurrence.child trace.bubble :
                      ConcreteElaboration.LocalOccurrence
                        trace.diagram.regionCount trace.diagram.nodeCount)]) =
                    some (targetKeptItems.append (.cons
                      (.bubble comprehension.val.boundary.length
                        (ConcreteElaboration.finishRegion trace.diagram
                          targetExtended trace.bubble bubbleItems)) .nil)) := by
              rw [← targetPartitionEq]
              exact targetPartitionCompiled
            have targetPermutation := compileOccurrences_perm_denote_iff
              trace.diagram targetRecurse targetExtended targetBinders
              targetPartition
              (ConcreteElaboration.localOccurrences_nodup trace.diagram
                (trace.regionMap wrap.val.anchor)) targetCanonicalNodup
              targetCompiled targetCanonicalCompiled
              model named targetLocalEnvironment targetRelations
            have targetItemsDenote := targetPermutation.mpr
              targetCanonicalDenote
            apply (DoubleCutElimTrace.finishRegion_denote_iff trace.diagram
              targetContext (trace.regionMap wrap.val.anchor) targetItems
              model named targetEnvironment targetRelations).2
            exact ⟨targetLocal, targetItemsDenote⟩

end AbstractionRawTrace

end VisualProof.Rule
