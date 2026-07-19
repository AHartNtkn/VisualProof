import VisualProof.Rule.Soundness.Comprehension.InstantiationFilteredRegionSimulation

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- Lift an authoritative cross-diagram simulation to the two executor
survivor compilers.  Removed nodes are reinserted only from explicit semantic
certificates; the forward projections merely forget them. -/
theorem survivor_simulation_of_authoritative
    {signature : List Nat}
    {sourceOrigin targetOrigin : CheckedDiagram signature}
    (sourceState : InstantiationState sourceOrigin sourceParameters sourceProxies)
    (targetState : InstantiationState targetOrigin targetParameters targetProxies)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceRemoved : ∀ {rels : RelCtx}
      (region : Fin sourceState.diagram.val.regionCount)
      (context : ConcreteElaboration.WireContext sourceState.diagram.val)
      (binders : ConcreteElaboration.BinderContext sourceState.diagram.val rels)
      (node : Fin sourceState.diagram.val.nodeCount)
      (item : Item signature context.length rels),
      ConcreteElaboration.LocalOccurrence.node node ∈
          ConcreteElaboration.localOccurrences sourceState.diagram.val region →
      dropOccurrenceSurvives sourceState (.node node) = false →
      ConcreteElaboration.compileNode? signature sourceState.diagram.val context
          binders node = some item →
      ∀ (env : Fin context.length → model.Carrier)
        (relEnv : RelEnv model.Carrier rels),
        denoteItem model named env relEnv item)
    (targetRemoved : ∀ {rels : RelCtx}
      (region : Fin targetState.diagram.val.regionCount)
      (context : ConcreteElaboration.WireContext targetState.diagram.val)
      (binders : ConcreteElaboration.BinderContext targetState.diagram.val rels)
      (node : Fin targetState.diagram.val.nodeCount)
      (item : Item signature context.length rels),
      ConcreteElaboration.LocalOccurrence.node node ∈
          ConcreteElaboration.localOccurrences targetState.diagram.val region →
      dropOccurrenceSurvives targetState (.node node) = false →
      ConcreteElaboration.compileNode? signature targetState.diagram.val context
          binders node = some item →
      ∀ (env : Fin context.length → model.Carrier)
        (relEnv : RelEnv model.Carrier rels),
        denoteItem model named env relEnv item)
    (direction : ConcreteElaboration.SimulationDirection)
    (sourceFuel targetFuel : Nat)
    (sourceRegion : Fin sourceState.diagram.val.regionCount)
    (targetRegion : Fin targetState.diagram.val.regionCount)
    (sourceContext : ConcreteElaboration.WireContext sourceState.diagram.val)
    (targetContext : ConcreteElaboration.WireContext targetState.diagram.val)
    (sourceExact : (sourceContext.extend sourceRegion).Exact sourceRegion)
    (targetExact : (targetContext.extend targetRegion).Exact targetRegion)
    (sourceBinders : ConcreteElaboration.BinderContext
      sourceState.diagram.val sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      targetState.diagram.val targetRels)
    (sourceCover : sourceBinders.Covers sourceRegion)
    (targetCover : targetBinders.Covers targetRegion)
    (outer : ConcreteElaboration.ContextIndexRelation sourceContext.length
      targetContext.length)
    (relationMap : RelationRenaming sourceRels targetRels)
    (sourceSurvivor : Region signature sourceContext.length sourceRels)
    (targetSurvivor : Region signature targetContext.length targetRels)
    (sourceSurvivorCompiled : compileSurvivorRegion? signature sourceState
      sourceFuel sourceRegion sourceContext sourceBinders = some sourceSurvivor)
    (targetSurvivorCompiled : compileSurvivorRegion? signature targetState
      targetFuel targetRegion targetContext targetBinders = some targetSurvivor)
    (authoritative : ∀ sourceFull targetFull,
      ConcreteElaboration.compileRegion? signature sourceState.diagram.val
          sourceFuel sourceRegion sourceContext sourceBinders = some sourceFull →
      ConcreteElaboration.compileRegion? signature targetState.diagram.val
          targetFuel targetRegion targetContext targetBinders = some targetFull →
      ConcreteElaboration.RegionSimulation model named direction outer
        (sourceFull.renameRelations relationMap) targetFull) :
    ConcreteElaboration.RegionSimulation model named direction outer
      (sourceSurvivor.renameRelations relationMap) targetSurvivor := by
  obtain ⟨sourceFull, sourceFullCompiled⟩ :=
    compileRegion?_exists_of_survivor sourceState sourceFuel sourceRegion
      sourceContext sourceBinders sourceExact sourceCover
      ⟨sourceSurvivor, sourceSurvivorCompiled⟩
  obtain ⟨targetFull, targetFullCompiled⟩ :=
    compileRegion?_exists_of_survivor targetState targetFuel targetRegion
      targetContext targetBinders targetExact targetCover
      ⟨targetSurvivor, targetSurvivorCompiled⟩
  have sourceForget := compileRegion_filter_simulation sourceState model named
    sourceRemoved .forward sourceFuel sourceRegion sourceContext sourceBinders
    sourceFull sourceSurvivor sourceFullCompiled sourceSurvivorCompiled
  have sourceReinsert := compileRegion_filter_simulation sourceState model named
    sourceRemoved .backward sourceFuel sourceRegion sourceContext sourceBinders
    sourceFull sourceSurvivor sourceFullCompiled sourceSurvivorCompiled
  have targetForget := compileRegion_filter_simulation targetState model named
    targetRemoved .forward targetFuel targetRegion targetContext targetBinders
    targetFull targetSurvivor targetFullCompiled targetSurvivorCompiled
  have targetReinsert := compileRegion_filter_simulation targetState model named
    targetRemoved .backward targetFuel targetRegion targetContext targetBinders
    targetFull targetSurvivor targetFullCompiled targetSurvivorCompiled
  have fullSimulation := authoritative sourceFull targetFull sourceFullCompiled
    targetFullCompiled
  intro sourceEnv targetEnv targetRelEnv environments
  let sourceRelEnv := RelEnv.pullback relationMap targetRelEnv
  have relationAgreement : RelEnv.Agrees relationMap sourceRelEnv targetRelEnv :=
    RelEnv.pullback_agrees relationMap targetRelEnv
  have sourceFullRename := denoteRegion_renameRelations model named relationMap
    sourceRelEnv targetRelEnv relationAgreement sourceEnv sourceFull
  have sourceSurvivorRename := denoteRegion_renameRelations model named
    relationMap sourceRelEnv targetRelEnv relationAgreement sourceEnv
    sourceSurvivor
  have sourceIdentity :
      (ConcreteElaboration.ContextIndexRelation.forwardMap id)
        |>.EnvironmentsAgree sourceEnv sourceEnv := by
    simp
  have targetIdentity :
      (ConcreteElaboration.ContextIndexRelation.forwardMap id)
        |>.EnvironmentsAgree targetEnv targetEnv := by
    simp
  cases direction with
  | forward =>
      intro sourceDenotes
      have sourceSurvivorNative := sourceSurvivorRename.mp sourceDenotes
      have sourceFullNative := sourceReinsert sourceEnv sourceEnv sourceRelEnv
        sourceIdentity sourceSurvivorNative
      have sourceFullPrepared := sourceFullRename.mpr sourceFullNative
      have targetFullDenotes := fullSimulation sourceEnv targetEnv targetRelEnv
        environments sourceFullPrepared
      exact targetForget targetEnv targetEnv targetRelEnv targetIdentity
        targetFullDenotes
  | backward =>
      intro targetDenotes
      have targetFullDenotes := targetReinsert targetEnv targetEnv targetRelEnv
        targetIdentity targetDenotes
      have sourceFullPrepared := fullSimulation sourceEnv targetEnv targetRelEnv
        environments targetFullDenotes
      have sourceFullNative := sourceFullRename.mp sourceFullPrepared
      have sourceSurvivorNative := sourceForget sourceEnv sourceEnv sourceRelEnv
        sourceIdentity sourceFullNative
      exact sourceSurvivorRename.mpr sourceSurvivorNative

end InstantiationSemantic

end VisualProof.Rule
