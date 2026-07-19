import VisualProof.Rule.Soundness.Modal.VacuousEliminationFocusedCompiler

namespace VisualProof.Rule.VacuousElimTrace

open VisualProof
open VisualProof.Theory
open VisualProof.Diagram
open VisualProof.Rule.DoubleCutElimTrace

theorem regularTargetEnvironment_outer
    (trace : VacuousElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input)
    (context : PromotedContextWitness trace sourceContext targetContext)
    (region : Fin trace.sourceDiagram.regionCount)
    (regular : region ≠ trace.targetIndex wellFormed)
    (sourceExact : (sourceContext.extend region).Exact region)
    (sourceOuter : Fin sourceContext.length → D)
    (targetOuter : Fin targetContext.length → D)
    (outerAgreement :
      context.indexRelation.EnvironmentsAgree sourceOuter targetOuter)
    (sourceLocal :
      Fin (ConcreteElaboration.exactScopeWires trace.sourceDiagram
        region).length → D)
    (targetIndex : Fin targetContext.length) :
    let extended := context.extendRegular wellFormed region regular
    extended.targetEnvironment
        (ConcreteElaboration.extendedEnvironment sourceContext region
          sourceOuter sourceLocal)
        (extendedOuterIndex targetContext (trace.origin region) targetIndex) =
      targetOuter targetIndex := by
  dsimp only
  let extended := context.extendRegular wellFormed region regular
  let sourceIndex := context.sourceIndex targetIndex
  let sourceExtendedIndex := extendedOuterIndex sourceContext region sourceIndex
  let targetExtendedIndex := extendedOuterIndex targetContext
    (trace.origin region) targetIndex
  have corresponding :
      (sourceContext.extend region).get sourceExtendedIndex =
        (targetContext.extend (trace.origin region)).get
          targetExtendedIndex := by
    calc
      _ = sourceContext.get sourceIndex :=
        extendedOuterIndex_get sourceContext region sourceIndex
      _ = targetContext.get targetIndex := context.sourceIndex_get targetIndex
      _ = _ :=
        (extendedOuterIndex_get targetContext (trace.origin region)
          targetIndex).symm
  have sourceExtendedIndexEq :
      sourceExtendedIndex = extended.sourceIndex targetExtendedIndex :=
    ConcreteElaboration.WireContext.lookup?_unique sourceExact.nodup
      (extended.sourceIndex_lookup targetExtendedIndex) corresponding
  unfold PromotedContextWitness.targetEnvironment
  rw [← sourceExtendedIndexEq]
  rw [extendedEnvironment_outer]
  exact outerAgreement sourceIndex targetIndex (context.sourceIndex_get _)

theorem regularTargetEnvironment_local
    (trace : VacuousElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input)
    (context : PromotedContextWitness trace sourceContext targetContext)
    (region : Fin trace.sourceDiagram.regionCount)
    (regular : region ≠ trace.targetIndex wellFormed)
    (sourceExact : (sourceContext.extend region).Exact region)
    (sourceOuter : Fin sourceContext.length → D)
    (sourceLocal :
      Fin (ConcreteElaboration.exactScopeWires trace.sourceDiagram
        region).length → D)
    (targetIndex : Fin (ConcreteElaboration.exactScopeWires input
      (trace.origin region)).length) :
    let extended := context.extendRegular wellFormed region regular
    let scopeLengthEq :
        (ConcreteElaboration.exactScopeWires input
          (trace.origin region)).length =
          (ConcreteElaboration.exactScopeWires trace.sourceDiagram
            region).length :=
      congrArg List.length
        (trace.regular_exactScopeWires wellFormed region regular).symm
    extended.targetEnvironment
        (ConcreteElaboration.extendedEnvironment sourceContext region
          sourceOuter sourceLocal)
        (extendedLocalIndex targetContext (trace.origin region) targetIndex) =
      sourceLocal (Fin.cast scopeLengthEq targetIndex) := by
  dsimp only
  let extended := context.extendRegular wellFormed region regular
  let scopeEq := trace.regular_exactScopeWires wellFormed region regular
  let scopeLengthEq := congrArg List.length scopeEq.symm
  let sourceLocalIndex := Fin.cast scopeLengthEq targetIndex
  let sourceExtendedIndex := extendedLocalIndex sourceContext region
    sourceLocalIndex
  let targetExtendedIndex := extendedLocalIndex targetContext
    (trace.origin region) targetIndex
  have localWireEq :
      (ConcreteElaboration.exactScopeWires trace.sourceDiagram region).get
          sourceLocalIndex =
        (ConcreteElaboration.exactScopeWires input
          (trace.origin region)).get targetIndex := by
    simpa only [List.get_eq_getElem, Fin.val_cast] using
      (List.getElem_of_eq scopeEq sourceLocalIndex.isLt)
  have corresponding :
      (sourceContext.extend region).get sourceExtendedIndex =
        (targetContext.extend (trace.origin region)).get
          targetExtendedIndex := by
    calc
      _ = (ConcreteElaboration.exactScopeWires trace.sourceDiagram region).get
          sourceLocalIndex :=
        extendedLocalIndex_get sourceContext region sourceLocalIndex
      _ = (ConcreteElaboration.exactScopeWires input
          (trace.origin region)).get targetIndex := localWireEq
      _ = _ :=
        (extendedLocalIndex_get targetContext (trace.origin region)
          targetIndex).symm
  have sourceExtendedIndexEq :
      sourceExtendedIndex = extended.sourceIndex targetExtendedIndex :=
    ConcreteElaboration.WireContext.lookup?_unique sourceExact.nodup
      (extended.sourceIndex_lookup targetExtendedIndex) corresponding
  unfold PromotedContextWitness.targetEnvironment
  rw [← sourceExtendedIndexEq]
  exact extendedEnvironment_local sourceContext region sourceOuter sourceLocal
    sourceLocalIndex

noncomputable def semanticSimulation
    (trace : VacuousElimTrace input outer raw)
    (sourceWellFormed : trace.sourceDiagram.WellFormed signature)
    (targetWellFormed : input.WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (freshForward : ∀ {sourceRels : RelCtx}
      (sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram)
      (sourceBinders : ConcreteElaboration.BinderContext
        trace.sourceDiagram sourceRels),
      sourceContext.Exact (trace.targetIndex targetWellFormed) →
        sourceBinders.Covers (trace.targetIndex targetWellFormed) →
        ConcreteElaboration.BinderContext.Enumeration trace.sourceDiagram
          sourceBinders (trace.targetIndex targetWellFormed) →
      (Fin sourceContext.length → model.Carrier) →
        RelEnv model.Carrier sourceRels →
          Relation model.Carrier trace.arity) :
    ConcreteElaboration.ConcreteSemanticSimulation signature
      trace.sourceDiagram input model named where
  source_wellFormed := sourceWellFormed
  target_wellFormed := targetWellFormed
  regionMap := trace.origin
  binderMap := trace.origin
  Distinguished := fun region => region = trace.targetIndex targetWellFormed
  occurrenceMap := fun _ _ occurrence => trace.occurrenceMap occurrence
  occurrenceMap_node := by
    intro region regular node nodeRegion
    exact ⟨node, rfl⟩
  occurrenceMap_child := by
    intro region regular child
    rfl
  root_eq := trace.promotion.root_origin.symm
  region_shape := by
    intro parent regular child childParent
    have shaped := trace.regular_regionShape targetWellFormed parent regular
      child childParent
    cases childShape : trace.promotion.regions child with
    | sheet =>
        simp [sourceDiagram, PromoteDiagramTrace.diagram, childShape,
          CRegion.parent?] at childParent
    | cut childOwner =>
        have childOwnerEq : childOwner = parent := by
          simpa [sourceDiagram, PromoteDiagramTrace.diagram, childShape,
            CRegion.parent?] using childParent
        subst childOwner
        simpa [origin, sourceDiagram, PromoteDiagramTrace.diagram,
          childShape] using shaped
    | bubble childOwner arity =>
        have childOwnerEq : childOwner = parent := by
          simpa [sourceDiagram, PromoteDiagramTrace.diagram, childShape,
            CRegion.parent?] using childParent
        subst childOwner
        simpa [origin, sourceDiagram, PromoteDiagramTrace.diagram,
          childShape] using shaped
  localOccurrences_map := by
    intro region regular
    exact trace.regular_localOccurrences targetWellFormed region regular
  BinderWitness := fun {sourceRels targetRels} sourceBinders targetBinders =>
    MappedBinderWitness trace
      (sourceRels := sourceRels) (targetRels := targetRels)
      sourceBinders targetBinders
  relationMap := fun witness => witness.relationMap
  binders_empty := {
    relationMap := ConcreteElaboration.identityRelationRenaming []
    bindersMapped := by
      intro region binderArity sourceRelation sourceLookup
      exact Fin.elim0 sourceRelation.index
  }
  binders_push := by
    intro sourceRels targetRels sourceBinders targetBinders witness child parent
      arity childKind regular
    exact witness.push child arity
  relationMap_push := by
    intro sourceRels targetRels sourceBinders targetBinders witness child parent
      arity childKind regular
    exact witness.relationMap_push child arity
  Allowed := fun _ _ => True
  allowed_cut := by simp
  allowed_bubble := by simp
  ContextWitness := fun sourceContext targetContext =>
    PLift (PromotedContextWitness trace sourceContext targetContext)
  AtRegion := fun _ _ => True
  indexRelation := fun witness => witness.down.indexRelation
  extendContext := by
    intro sourceContext targetContext witness region regular sourceExact
      targetExact
    exact PLift.up (witness.down.extendRegular targetWellFormed region regular)
  extendFocusedContext := by
    intro sourceContext targetContext witness region focused sourceExact
      targetExact
    subst region
    have focusOrigin : trace.origin (trace.targetIndex targetWellFormed) =
        trace.parent := trace.targetIndex_origin targetWellFormed
    exact focusOrigin.symm ▸
      PLift.up (witness.down.extendFocused targetWellFormed)
  at_child := by simp
  at_extended := by simp
  at_focused_child := by simp
  localTransport := by
    intro sourceRels targetRels direction fuelSource fuelTarget sourceContext
      targetContext context sourceBinders targetBinders binderWitness region
      atRegion regular allowed sourceExact targetExact sourceBindersCover
      targetBindersCover sourceEnumeration targetEnumeration sourceItems
      targetItems sourceCompiled targetCompiled itemSemantics
    let promoted := context.down
    let extended := promoted.extendRegular targetWellFormed region regular
    apply ConcreteElaboration.directionalLocalTransport_of_agreement
      direction sourceContext targetContext region (trace.origin region)
      promoted.indexRelation extended.indexRelation model named
      (sourceItems.renameRelations binderWitness.relationMap) targetItems
    · intro sourceOuter targetOuter outerAgreement
      cases direction with
      | forward =>
          intro sourceLocal
          let sourceEnvironment :=
            ConcreteElaboration.extendedEnvironment sourceContext region
              sourceOuter sourceLocal
          let targetEnvironment :=
            extended.targetEnvironment sourceEnvironment
          let targetLocal := localEnvironmentPart targetContext
            (trace.origin region) targetEnvironment
          refine ⟨targetLocal, ?_⟩
          have targetOuterValues : ∀ index,
              targetEnvironment
                  (extendedOuterIndex targetContext (trace.origin region)
                    index) = targetOuter index := by
            intro index
            exact trace.regularTargetEnvironment_outer targetWellFormed
              sourceContext targetContext promoted region regular sourceExact
              sourceOuter targetOuter outerAgreement sourceLocal index
          have targetEnvironmentEq :=
            extendedEnvironment_of_parts targetContext (trace.origin region)
              targetOuter targetEnvironment targetOuterValues
          rw [targetEnvironmentEq]
          exact extended.targetEnvironment_agrees sourceExact.nodup
            sourceEnvironment
      | backward =>
          intro targetLocal
          let scopeLengthEq :
              (ConcreteElaboration.exactScopeWires input
                (trace.origin region)).length =
                (ConcreteElaboration.exactScopeWires trace.sourceDiagram
                  region).length :=
            congrArg List.length
              (trace.regular_exactScopeWires targetWellFormed region regular).symm
          let sourceLocal :
              Fin (ConcreteElaboration.exactScopeWires trace.sourceDiagram
                region).length → model.Carrier :=
            fun index => targetLocal (Fin.cast scopeLengthEq.symm index)
          let sourceEnvironment :=
            ConcreteElaboration.extendedEnvironment sourceContext region
              sourceOuter sourceLocal
          let targetEnvironment :=
            extended.targetEnvironment sourceEnvironment
          refine ⟨sourceLocal, ?_⟩
          have targetOuterValues : ∀ index,
              targetEnvironment
                  (extendedOuterIndex targetContext (trace.origin region)
                    index) = targetOuter index := by
            intro index
            exact trace.regularTargetEnvironment_outer targetWellFormed
              sourceContext targetContext promoted region regular sourceExact
              sourceOuter targetOuter outerAgreement sourceLocal index
          have targetLocalValues :
              localEnvironmentPart targetContext (trace.origin region)
                  targetEnvironment = targetLocal := by
            funext index
            change targetEnvironment
                (extendedLocalIndex targetContext (trace.origin region)
                  index) = targetLocal index
            have localValue :=
              trace.regularTargetEnvironment_local targetWellFormed
              sourceContext targetContext promoted region regular sourceExact
                sourceOuter sourceLocal index
            change targetEnvironment
                (extendedLocalIndex targetContext (trace.origin region)
                  index) = sourceLocal (Fin.cast scopeLengthEq index)
              at localValue
            rw [localValue]
            simp [sourceLocal, scopeLengthEq]
          have targetEnvironmentEq :=
            extendedEnvironment_of_parts targetContext (trace.origin region)
              targetOuter targetEnvironment targetOuterValues
          rw [targetLocalValues] at targetEnvironmentEq
          rw [targetEnvironmentEq]
          exact extended.targetEnvironment_agrees sourceExact.nodup
            sourceEnvironment
    · exact itemSemantics
  nodeSemantic := by
    intro sourceRels targetRels direction region sourceContext targetContext
      context atRegion sourceNodup targetNodup sourceBinders targetBinders
      allowed binderWitness sourceNode targetNode regular mapped nodeRegion
      sourceItem targetItem sourceCompiled targetCompiled
    have targetNodeEq : targetNode = sourceNode :=
      ConcreteElaboration.LocalOccurrence.node.inj mapped.symm
    subst targetNode
    have shape := trace.regular_nodeShape targetWellFormed region regular
      sourceNode nodeRegion
    cases promotedNode : trace.promotion.nodes sourceNode <;>
      simp [promotedNode] at shape ⊢
    all_goals
      have sourceShape : input.nodes sourceNode =
          match trace.sourceDiagram.nodes sourceNode with
          | .term owner freePorts term =>
              .term (trace.origin owner) freePorts term
          | .atom owner binder =>
              .atom (trace.origin owner) (trace.origin binder)
          | .named owner definition arity =>
              .named (trace.origin owner) definition arity := by
        simpa [PromoteDiagramTrace.diagram, promotedNode] using shape
      exact trace.compileNode_itemSimulation targetWellFormed model named
        direction sourceContext targetContext sourceBinders targetBinders
        binderWitness sourceNode trace.origin sourceShape sourceItem targetItem
        sourceCompiled targetCompiled
  focusedRegionKernel := by
    intro sourceRels targetRels direction fuelSource fuelTarget region
      sourceContext targetContext context sourceBinders targetBinders atRegion
      focused allowed binderWitness sourceExact targetExact sourceBindersCover
      targetBindersCover sourceEnumeration targetEnumeration recurse recurseAt
      sourceItems targetItems sourceCompiled targetCompiled
    subst region
    have focusOrigin : trace.origin (trace.targetIndex targetWellFormed) =
        trace.parent := trace.targetIndex_origin targetWellFormed
    let lawAtTarget :
        (targetExact : (targetContext.extend trace.parent).Exact trace.parent) →
        targetBinders.Covers trace.parent →
        ConcreteElaboration.BinderContext.Enumeration input targetBinders
          trace.parent →
        ∀ targetItems : ItemSeq signature
            (targetContext.extend trace.parent).length targetRels,
        ConcreteElaboration.compileOccurrencesWith? signature input
            (ConcreteElaboration.compileRegion? signature input fuelTarget)
            (targetContext.extend trace.parent) targetBinders
            (ConcreteElaboration.localOccurrences input trace.parent) =
          some targetItems →
        ConcreteElaboration.RegionSimulation model named direction
          context.down.indexRelation
          ((ConcreteElaboration.finishRegion trace.sourceDiagram sourceContext
            (trace.targetIndex targetWellFormed) sourceItems).renameRelations
              binderWitness.relationMap)
          (ConcreteElaboration.finishRegion input targetContext trace.parent
            targetItems) := by
      intro targetExact targetBindersCover targetEnumeration targetItems
        targetCompiled
      exact trace.focusedItems_regionSimulation sourceWellFormed targetWellFormed
        model named direction fuelSource fuelTarget sourceContext targetContext
        context.down sourceBinders targetBinders binderWitness sourceExact
        (freshForward (sourceContext.extend
          (trace.targetIndex targetWellFormed)) sourceBinders sourceExact
          sourceBindersCover sourceEnumeration)
        targetExact sourceBindersCover targetBindersCover sourceEnumeration
        targetEnumeration
        (fun childFuelTarget childSourceContext childTargetContext childContext =>
          recurseAt childFuelTarget childSourceContext childTargetContext
            (PLift.up childContext))
        sourceItems targetItems sourceCompiled targetCompiled
    have lawAtOrigin := focusOrigin.symm ▸ lawAtTarget
    exact lawAtOrigin targetExact targetBindersCover targetEnumeration
      targetItems targetCompiled

end VisualProof.Rule.VacuousElimTrace
