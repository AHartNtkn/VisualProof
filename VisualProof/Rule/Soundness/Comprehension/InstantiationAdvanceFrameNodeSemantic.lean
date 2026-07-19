import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvanceFrameSemantic

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- Direction-polymorphic form of frame-node transport.  A retained node is
compiled to the exact wire/relation renaming of its source item, so its
denotation is equivalent in both simulation directions. -/
theorem frameNode_simulation_of_mapped
    {signature : List Nat}
    (input : Splice.Input signature)
    (hadmissible : input.Admissible)
    (region : Fin input.coalesceFrameRaw.regionCount)
    (sourceContext : ConcreteElaboration.WireContext input.coalesceFrameRaw)
    (targetContext : ConcreteElaboration.WireContext input.plugLayout.plugRaw)
    (sourceExact : sourceContext.Exact region)
    (targetExact : targetContext.Exact
      (input.plugLayout.frameRegion region))
    (sourceBinders : ConcreteElaboration.BinderContext
      input.coalesceFrameRaw sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      input.plugLayout.plugRaw targetRels)
    (sourceCover : sourceBinders.Covers region)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      input.coalesceFrameRaw sourceBinders region)
    (wireMap : Fin sourceContext.length → Fin targetContext.length)
    (wireSpec : ∀ index, targetContext.get (wireMap index) =
      input.plugLayout.frameWire (sourceContext.get index))
    (relationMap : RelationRenaming sourceRels targetRels)
    (relationSpec : ∀ {arity} (relation : RelVar sourceRels arity),
      targetBinders
          (input.plugLayout.frameRegion
            (sourceEnumeration.binder relation.index)) =
        some ⟨arity, relationMap relation⟩)
    (node : Fin input.coalesceFrameRaw.nodeCount)
    (nodeRegion : (input.coalesceFrameRaw.nodes node).region = region)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (sourceItem : Item signature sourceContext.length sourceRels)
    (targetItem : Item signature targetContext.length targetRels)
    (sourceCompiled : ConcreteElaboration.compileNode? signature
      input.coalesceFrameRaw sourceContext sourceBinders node = some sourceItem)
    (targetCompiled : ConcreteElaboration.compileNode? signature
      input.plugLayout.plugRaw targetContext targetBinders
        (input.plugLayout.frameNode node) = some targetItem) :
    ConcreteElaboration.ItemSimulation model named direction
      (ConcreteElaboration.ContextIndexRelation.forwardMap wireMap)
      (sourceItem.renameRelations relationMap) targetItem := by
  have mapped := input.plugLayout.compileFrameNode_at_region_of_maps signature
    input hadmissible region sourceContext targetContext sourceExact targetExact
    sourceBinders targetBinders sourceCover sourceEnumeration wireMap wireSpec
    relationMap relationSpec node nodeRegion
  rw [sourceCompiled, targetCompiled] at mapped
  have itemEq :
      (sourceItem.renameWires wireMap).renameRelations relationMap =
        targetItem := by
    exact Option.some.inj (by simpa only [Option.map_some] using mapped.symm)
  subst targetItem
  intro sourceEnv targetEnv targetRelEnv environments
  have environmentEq : sourceEnv = targetEnv ∘ wireMap := by
    simpa using environments
  have sourceRelationDenotation := denoteItem_renameRelations model named
    relationMap (RelEnv.pullback relationMap targetRelEnv) targetRelEnv
    (RelEnv.pullback_agrees relationMap targetRelEnv) sourceEnv sourceItem
  have relationDenotation := denoteItem_renameRelations model named relationMap
    (RelEnv.pullback relationMap targetRelEnv) targetRelEnv
    (RelEnv.pullback_agrees relationMap targetRelEnv) targetEnv
    (sourceItem.renameWires wireMap)
  have wireDenotation := denoteItem_renameWires model named wireMap targetEnv
    (RelEnv.pullback relationMap targetRelEnv) sourceItem
  rw [sourceRelationDenotation, relationDenotation, wireDenotation,
    ← environmentEq]
  cases direction <;> exact id

/-- Backward semantic transport for one retained frame node.  This uses the
splice compiler's exact quotient/frame wire map and binder renaming directly,
so it remains valid at the distinguished site where the local wire carriers
need not be related by the off-site finite equivalence. -/
theorem frameNode_denotes_of_mapped
    {signature : List Nat}
    (input : Splice.Input signature)
    (hadmissible : input.Admissible)
    (region : Fin input.coalesceFrameRaw.regionCount)
    (sourceContext : ConcreteElaboration.WireContext input.coalesceFrameRaw)
    (targetContext : ConcreteElaboration.WireContext input.plugLayout.plugRaw)
    (sourceExact : sourceContext.Exact region)
    (targetExact : targetContext.Exact
      (input.plugLayout.frameRegion region))
    (sourceBinders : ConcreteElaboration.BinderContext
      input.coalesceFrameRaw sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      input.plugLayout.plugRaw targetRels)
    (sourceCover : sourceBinders.Covers region)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      input.coalesceFrameRaw sourceBinders region)
    (wireMap : Fin sourceContext.length → Fin targetContext.length)
    (wireSpec : ∀ index, targetContext.get (wireMap index) =
      input.plugLayout.frameWire (sourceContext.get index))
    (relationMap : RelationRenaming sourceRels targetRels)
    (relationSpec : ∀ {arity} (relation : RelVar sourceRels arity),
      targetBinders
          (input.plugLayout.frameRegion
            (sourceEnumeration.binder relation.index)) =
        some ⟨arity, relationMap relation⟩)
    (node : Fin input.coalesceFrameRaw.nodeCount)
    (nodeRegion : (input.coalesceFrameRaw.nodes node).region = region)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceEnv : Fin sourceContext.length → model.Carrier)
    (targetEnv : Fin targetContext.length → model.Carrier)
    (environmentEq : sourceEnv = targetEnv ∘ wireMap)
    (sourceRelEnv : RelEnv model.Carrier sourceRels)
    (targetRelEnv : RelEnv model.Carrier targetRels)
    (relationsAgree : RelEnv.Agrees relationMap sourceRelEnv targetRelEnv)
    (sourceItem : Item signature sourceContext.length sourceRels)
    (targetItem : Item signature targetContext.length targetRels)
    (sourceCompiled : ConcreteElaboration.compileNode? signature
      input.coalesceFrameRaw sourceContext sourceBinders node = some sourceItem)
    (targetCompiled : ConcreteElaboration.compileNode? signature
      input.plugLayout.plugRaw targetContext targetBinders
        (input.plugLayout.frameNode node) = some targetItem)
    (targetDenotes : denoteItem model named targetEnv targetRelEnv targetItem) :
    denoteItem model named sourceEnv sourceRelEnv sourceItem := by
  have mapped := input.plugLayout.compileFrameNode_at_region_of_maps signature
    input hadmissible region sourceContext targetContext sourceExact targetExact
    sourceBinders targetBinders sourceCover sourceEnumeration wireMap wireSpec
    relationMap relationSpec node nodeRegion
  rw [sourceCompiled, targetCompiled] at mapped
  have itemEq :
      (sourceItem.renameWires wireMap).renameRelations relationMap =
        targetItem := by
    exact Option.some.inj (by simpa only [Option.map_some] using mapped.symm)
  rw [← itemEq] at targetDenotes
  have wireRenamedDenotes : denoteItem model named targetEnv sourceRelEnv
      (sourceItem.renameWires wireMap) :=
    (denoteItem_renameRelations model named relationMap sourceRelEnv
      targetRelEnv relationsAgree targetEnv
      (sourceItem.renameWires wireMap)).mp targetDenotes
  have sourceDenotes :=
    (denoteItem_renameWires model named wireMap targetEnv sourceRelEnv
      sourceItem).mp wireRenamedDenotes
  simpa only [environmentEq] using sourceDenotes

end InstantiationSemantic

end VisualProof.Rule
