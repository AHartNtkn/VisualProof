import VisualProof.Rule.Soundness.Equational.FissionFocused

namespace VisualProof.Rule

open VisualProof
open Diagram
open Theory

namespace FissionSoundness

/-- Direct children of the focused fission site are unchanged. Cuts reverse
the recursive direction and bubbles preserve it, exactly as their denotations
require. -/
theorem focusedChild_itemSimulation
    (input : CheckedDiagram signature)
    (selected : Fin input.val.nodeCount)
    (site : Fin input.val.regionCount)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount)))
    (targetWellFormed :
      (fissionRaw input selected site producer residual).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (sourceContext : ConcreteElaboration.WireContext input.val)
    (targetContext : ConcreteElaboration.WireContext
      (fissionRaw input selected site producer residual))
    (embedding : ContextEmbedding input selected site producer residual
      sourceContext targetContext)
    (sourceBinders : ConcreteElaboration.BinderContext input.val rels)
    (targetBinders : ConcreteElaboration.BinderContext
      (fissionRaw input selected site producer residual) rels)
    (bindersEqual : HEq sourceBinders targetBinders)
    (sourceBindersCover : sourceBinders.Covers site)
    (targetBindersCover : targetBinders.Covers site)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      input.val sourceBinders site)
    (targetEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (fissionRaw input selected site producer residual) targetBinders site)
    (recurse : ∀ {childDirection : ConcreteElaboration.SimulationDirection}
      {child : Fin input.val.regionCount}
      {childSourceRels childTargetRels : RelCtx}
      {childSourceBinders : ConcreteElaboration.BinderContext
        input.val childSourceRels}
      {childTargetBinders : ConcreteElaboration.BinderContext
        (fissionRaw input selected site producer residual) childTargetRels}
      {sourceBody : Region signature sourceContext.length childSourceRels}
      {targetBody : Region signature targetContext.length childTargetRels},
      (input.val.regions child).parent? = some site →
      ((fissionRaw input selected site producer residual).regions child).parent? =
        some site →
      True →
      (childBinderWitness : ConcreteElaboration.IdentityBinderWitness input.val
        (fissionRaw input selected site producer residual)
        childSourceBinders childTargetBinders) →
      childSourceBinders.Covers child →
      childTargetBinders.Covers child →
      ConcreteElaboration.BinderContext.Enumeration input.val
        childSourceBinders child →
      ConcreteElaboration.BinderContext.Enumeration
        (fissionRaw input selected site producer residual)
        childTargetBinders child →
      ConcreteElaboration.compileRegion? signature input.val fuelSource child
          sourceContext childSourceBinders = some sourceBody →
      ConcreteElaboration.compileRegion? signature
          (fissionRaw input selected site producer residual) fuelTarget child
          targetContext childTargetBinders = some targetBody →
      ConcreteElaboration.RegionSimulation model named childDirection
        (ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index)
        (sourceBody.renameRelations
          (ConcreteElaboration.IdentityBinderWitness.relationMap
            childBinderWitness)) targetBody)
    (child : Fin input.val.regionCount)
    (parent : (input.val.regions child).parent? = some site)
    (sourceItem : Item signature sourceContext.length rels)
    (targetItem : Item signature targetContext.length rels)
    (sourceCompiled : ConcreteElaboration.compileOccurrenceWith? signature
      input.val (ConcreteElaboration.compileRegion? signature input.val
        fuelSource) sourceContext sourceBinders (.child child) = some sourceItem)
    (targetCompiled : ConcreteElaboration.compileOccurrenceWith? signature
      (fissionRaw input selected site producer residual)
      (ConcreteElaboration.compileRegion? signature
        (fissionRaw input selected site producer residual) fuelTarget)
      targetContext targetBinders (.child child) = some targetItem) :
    ConcreteElaboration.ItemSimulation model named direction
      (ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index)
      sourceItem targetItem := by
  cases bindersEqual
  have targetParent :
      ((fissionRaw input selected site producer residual).regions child).parent? =
        some site := by
    simpa [fissionRaw] using parent
  cases sourceKind : input.val.regions child with
  | sheet =>
      simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind]
        at sourceCompiled
  | cut actualParent =>
      have actualParentEq : actualParent = site := by
        rw [sourceKind] at parent
        exact Option.some.inj parent
      subst actualParent
      have targetKind :
          (fissionRaw input selected site producer residual).regions child =
            .cut site := by
        simpa [fissionRaw] using sourceKind
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
              (fissionRaw input selected site producer residual) fuelTarget child
              targetContext sourceBinders with
          | none =>
              simp [ConcreteElaboration.compileOccurrenceWith?, targetKind,
                targetResult] at targetCompiled
          | some targetBody =>
              simp [ConcreteElaboration.compileOccurrenceWith?, targetKind,
                targetResult] at targetCompiled
              subst targetItem
              let witness : ConcreteElaboration.IdentityBinderWitness input.val
                  (fissionRaw input selected site producer residual)
                  sourceBinders sourceBinders := ⟨rfl, HEq.rfl⟩
              have bodies := recurse (childDirection := direction.flip)
                parent targetParent True.intro witness
                (ConcreteElaboration.BinderContext.covers_cut_child
                  sourceBindersCover sourceKind)
                (ConcreteElaboration.BinderContext.covers_cut_child
                  targetBindersCover targetKind)
                (sourceEnumeration.cutChild input.property sourceKind)
                (targetEnumeration.cutChild targetWellFormed targetKind)
                sourceResult targetResult
              have relationMapEq :
                  (fun {arity} =>
                    ConcreteElaboration.IdentityBinderWitness.relationMap
                      witness : RelationRenaming rels rels) =
                    (fun {arity} relation => relation) := by rfl
              have bodies' : ConcreteElaboration.RegionSimulation model named
                  direction.flip
                  (ConcreteElaboration.ContextIndexRelation.forwardMap
                    embedding.index) sourceBody targetBody := by
                rw [relationMapEq, Region.renameRelations_id] at bodies
                exact bodies
              intro sourceEnv targetEnv relEnv environments
              have bodyEntailment := bodies' sourceEnv targetEnv relEnv
                environments
              simp only [cut_denotes_negation]
              cases direction with
              | forward =>
                  exact fun sourceNot targetDenotes =>
                    sourceNot (bodyEntailment targetDenotes)
              | backward =>
                  exact fun targetNot sourceDenotes =>
                    targetNot (bodyEntailment sourceDenotes)
  | bubble actualParent arity =>
      have actualParentEq : actualParent = site := by
        rw [sourceKind] at parent
        exact Option.some.inj parent
      subst actualParent
      have targetKind :
          (fissionRaw input selected site producer residual).regions child =
            .bubble site arity := by
        simpa [fissionRaw] using sourceKind
      let sourcePushed := sourceBinders.push child arity
      let targetPushed : ConcreteElaboration.BinderContext
          (fissionRaw input selected site producer residual) (arity :: rels) :=
        ConcreteElaboration.BinderContext.push
          (d := fissionRaw input selected site producer residual)
          sourceBinders child arity
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
              (fissionRaw input selected site producer residual) fuelTarget child
              targetContext targetPushed with
          | none =>
              simp [ConcreteElaboration.compileOccurrenceWith?, targetKind,
                targetPushed, targetResult] at targetCompiled
          | some targetBody =>
              simp [ConcreteElaboration.compileOccurrenceWith?, targetKind,
                targetPushed, targetResult] at targetCompiled
              subst targetItem
              let witness : ConcreteElaboration.IdentityBinderWitness input.val
                  (fissionRaw input selected site producer residual)
                  sourcePushed targetPushed := ⟨rfl, HEq.rfl⟩
              have bodies := recurse (childDirection := direction)
                parent targetParent True.intro witness
                (ConcreteElaboration.BinderContext.push_covers_bubble_child
                  sourceBindersCover sourceKind)
                (ConcreteElaboration.BinderContext.push_covers_bubble_child
                  targetBindersCover targetKind)
                (sourceEnumeration.bubbleChild input.property sourceKind)
                (targetEnumeration.bubbleChild targetWellFormed targetKind)
                sourceResult targetResult
              have relationMapEq :
                  (fun {relationArity} =>
                    ConcreteElaboration.IdentityBinderWitness.relationMap
                      witness : RelationRenaming (arity :: rels)
                        (arity :: rels)) =
                    (fun {relationArity} relation => relation) := by rfl
              have bodies' : ConcreteElaboration.RegionSimulation model named
                  direction
                  (ConcreteElaboration.ContextIndexRelation.forwardMap
                    embedding.index) sourceBody targetBody := by
                rw [relationMapEq, Region.renameRelations_id] at bodies
                exact bodies
              intro sourceEnv targetEnv relEnv environments
              simp only [bubble_denotes_exists]
              cases direction with
              | forward =>
                  rintro ⟨relationValue, sourceDenotes⟩
                  exact ⟨relationValue, bodies' sourceEnv targetEnv
                    (relationValue, relEnv) environments sourceDenotes⟩
              | backward =>
                  rintro ⟨relationValue, targetDenotes⟩
                  exact ⟨relationValue, bodies' sourceEnv targetEnv
                    (relationValue, relEnv) environments targetDenotes⟩

/-- Complete recursive semantic simulation for fission.  The focused site owns
the residual/producer factorization; every other region, node, wire, and child
is transported by the generic concrete compiler. -/
noncomputable def semanticSimulation
    (input : CheckedDiagram signature)
    (selected : Fin input.val.nodeCount)
    (site : Fin input.val.regionCount)
    (freePorts : Nat) (term : Lambda.Term 0 (Fin freePorts))
    (portWire : Fin freePorts → Fin input.val.wireCount)
    (depth : Nat) (selectedTerm : Lambda.Term depth
      (Fin input.val.wireCount))
    (path : List Lambda.PathSegment)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount)))
    (nodeShape : input.val.nodes selected = .term site freePorts term)
    (resolved : resolveNodeFreeWires? input selected freePorts = some portWire)
    (selectedResult : subtermAt? (term.mapFree portWire) path =
      some ⟨depth, selectedTerm⟩)
    (residualResult : replaceAtPort?
      ((term.mapFree portWire).mapFree some) path none = some residual)
    (producerResult : lowerToZero depth selectedTerm = some producer)
    (targetWellFormed :
      (fissionRaw input selected site producer residual).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature) :
    ConcreteElaboration.ConcreteSemanticSimulation signature input.val
      (fissionRaw input selected site producer residual) model named where
  source_wellFormed := input.property
  target_wellFormed := targetWellFormed
  regionMap := id
  binderMap := id
  Distinguished := fun region => region = site
  occurrenceMap := fun _ _ occurrence => mapOccurrence input occurrence
  occurrenceMap_node := by
    intro region regular node nodeRegion
    exact ⟨node.castSucc, rfl⟩
  occurrenceMap_child := by
    intro region regular child
    rfl
  root_eq := rfl
  region_shape := by
    intro parent regular child childParent
    simp only [id_eq]
    cases kind : input.val.regions child <;> simp [fissionRaw, kind]
  localOccurrences_map := by
    intro region regular
    exact fissionRaw_localOccurrences_regular input selected site region
      freePorts term nodeShape producer residual regular
  BinderWitness := fun {sourceRels targetRels} sourceBinders targetBinders =>
    ConcreteElaboration.IdentityBinderWitness input.val
      (fissionRaw input selected site producer residual)
      sourceBinders targetBinders
  relationMap := fun witness =>
    ConcreteElaboration.IdentityBinderWitness.relationMap witness
  binders_empty := ⟨rfl, HEq.rfl⟩
  binders_push := by
    intro sourceRels targetRels sourceBinders targetBinders witness child parent
      arity kind regular
    rcases witness with ⟨relationContextsEq, bindersEq⟩
    subst targetRels
    cases bindersEq
    exact ⟨rfl, HEq.rfl⟩
  relationMap_push := by
    intro sourceRels targetRels sourceBinders targetBinders witness child parent
      arity kind regular
    rcases witness with ⟨relationContextsEq, bindersEq⟩
    subst targetRels
    cases bindersEq
    simpa [ConcreteElaboration.IdentityBinderWitness.relationMap,
      ConcreteElaboration.identityRelationRenaming] using
        (RelationRenaming.lift_id_fun (source := sourceRels) arity).symm
  Allowed := fun _ _ => True
  allowed_cut := by simp
  allowed_bubble := by simp
  ContextWitness := ContextEmbedding input selected site producer residual
  AtRegion := fun _ _ => True
  indexRelation := fun embedding =>
    ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index
  extendContext := by
    intro source target embedding region regular sourceExact targetExact
    exact embedding.extend region
  extendFocusedContext := by
    intro source target embedding region atRegion focused sourceExact targetExact
    exact embedding.extend region
  at_child := by simp
  at_extended := by simp
  at_focused_child := by simp
  localTransport := by
    intro sourceRels targetRels direction fuelSource fuelTarget source target
      embedding sourceBinders targetBinders binderWitness region atRegion regular
      allowed sourceExact targetExact sourceBindersCover targetBindersCover
      sourceEnumeration targetEnumeration sourceItems targetItems sourceCompiled
      targetCompiled itemSemantics
    exact ConcreteElaboration.directionalLocalTransport_of_agreement direction
      source target region region
      (ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index)
      (ConcreteElaboration.ContextIndexRelation.forwardMap
        (embedding.extend region).index)
      model named
      (sourceItems.renameRelations
        (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness))
      targetItems
      (regularLocalSelection embedding direction region regular targetExact model)
      itemSemantics
  nodeSemantic := by
    intro sourceRels targetRels direction region source target embedding atRegion
      sourceNodup targetNodup sourceBinders targetBinders allowed binderWitness
      sourceNode targetNode regular mapped nodeRegion sourceItem targetItem
      sourceCompiled targetCompiled
    have relationContextsEq := binderWitness.relationContexts_eq
    subst targetRels
    have bindersEq := binderWitness.binders_eq
    cases bindersEq
    have different : sourceNode ≠ selected := by
      intro equality
      subst sourceNode
      rw [nodeShape] at nodeRegion
      exact regular nodeRegion.symm
    have targetNodeEq : targetNode = sourceNode.castSucc := by
      exact ConcreteElaboration.LocalOccurrence.node.inj mapped.symm
    subst targetNode
    have relationMapEq :
        (fun {arity} =>
          ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness :
          RelationRenaming sourceRels sourceRels) =
        (fun {arity} relation => relation) := by rfl
    rw [relationMapEq, Item.renameRelations_id]
    exact unchangedNode_itemSimulation input selected sourceNode different site
      producer residual source target embedding targetNodup sourceBinders
      sourceBinders HEq.rfl sourceItem targetItem sourceCompiled targetCompiled
      model named direction
  focusedRegionKernel := by
    intro sourceRels targetRels direction fuelSource fuelTarget region source
      target embedding sourceBinders targetBinders atRegion focused allowed
      binderWitness sourceExact targetExact sourceBindersCover
      targetBindersCover sourceEnumeration targetEnumeration recurse recurseAt
      sourceItems targetItems sourceCompiled targetCompiled
    subst region
    have relationContextsEq := binderWitness.relationContexts_eq
    subst targetRels
    have bindersEq := binderWitness.binders_eq
    cases bindersEq
    simp only [id_eq] at targetExact targetCompiled ⊢
    rw [ConcreteElaboration.finishRegion_renameRelations source site
      (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness)
      sourceItems]
    have relationMapEq :
        (fun {arity} =>
          ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness :
          RelationRenaming sourceRels sourceRels) =
        (fun {arity} relation => relation) := by rfl
    rw [relationMapEq, ItemSeq.renameRelations_id]
    apply ConcreteElaboration.finishRegion_denote direction source target site
      site (ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index)
      model named sourceItems targetItems
    exact focusedLocalTransport input selected site freePorts term portWire depth
      selectedTerm path producer residual nodeShape resolved selectedResult
      residualResult producerResult targetWellFormed model named direction
      fuelSource fuelTarget source target embedding sourceBinders sourceExact
      targetExact
      (fun child sourceItem targetItem parent sourceOccurrence targetOccurrence =>
        focusedChild_itemSimulation input selected site producer residual
          targetWellFormed model named direction fuelSource fuelTarget
          (source.extend site) (target.extend site) (embedding.extend site)
          sourceBinders sourceBinders HEq.rfl sourceBindersCover
          targetBindersCover sourceEnumeration targetEnumeration recurse child
          parent sourceItem targetItem sourceOccurrence targetOccurrence)
      sourceItems targetItems sourceCompiled targetCompiled

end FissionSoundness

end VisualProof.Rule
