import VisualProof.Rule.Soundness.Equational.HeadStripSemantic

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace HeadStripSoundness

theorem focusedLocalTransport
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (targetWellFormed : (headStripRaw input payload).WellFormed signature)
    (named : NamedEnv Lambda.Individual signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (sourceContext : ConcreteElaboration.WireContext input.val)
    (targetContext : ConcreteElaboration.WireContext
      (headStripRaw input payload))
    (embedding : ContextEmbedding input payload sourceContext targetContext)
    (sourceBinders : ConcreteElaboration.BinderContext input.val sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (headStripRaw input payload) targetRels)
    (binderWitness : ConcreteElaboration.IdentityBinderWitness input.val
      (headStripRaw input payload) sourceBinders targetBinders)
    (sourceExact : (sourceContext.extend payload.region).Exact payload.region)
    (targetExact : (targetContext.extend payload.region).Exact payload.region)
    (sourceBindersCover : sourceBinders.Covers payload.region)
    (targetBindersCover : targetBinders.Covers payload.region)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      input.val sourceBinders payload.region)
    (targetEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (headStripRaw input payload) targetBinders payload.region)
    (recurse : ∀ {childDirection : ConcreteElaboration.SimulationDirection}
      {child : Fin input.val.regionCount}
      {childSourceRels childTargetRels : RelCtx}
      {childSourceBinders : ConcreteElaboration.BinderContext
        input.val childSourceRels}
      {childTargetBinders : ConcreteElaboration.BinderContext
        (headStripRaw input payload) childTargetRels}
      {sourceBody : Region signature
        (sourceContext.extend payload.region).length childSourceRels}
      {targetBody : Region signature
        (targetContext.extend payload.region).length childTargetRels},
      (input.val.regions child).parent? = some payload.region →
      ((headStripRaw input payload).regions child).parent? =
        some payload.region →
      True →
      (childBinderWitness : ConcreteElaboration.IdentityBinderWitness input.val
        (headStripRaw input payload) childSourceBinders childTargetBinders) →
      childSourceBinders.Covers child →
      childTargetBinders.Covers child →
      ConcreteElaboration.BinderContext.Enumeration input.val
        childSourceBinders child →
      ConcreteElaboration.BinderContext.Enumeration
        (headStripRaw input payload) childTargetBinders child →
      ConcreteElaboration.compileRegion? signature input.val fuelSource child
          (sourceContext.extend payload.region) childSourceBinders =
        some sourceBody →
      ConcreteElaboration.compileRegion? signature (headStripRaw input payload)
          fuelTarget child (targetContext.extend payload.region)
          childTargetBinders = some targetBody →
      ConcreteElaboration.RegionSimulation Lambda.canonicalModel named
        childDirection
        (ConcreteElaboration.ContextIndexRelation.forwardMap
          (embedding.extend payload.region).index)
        (sourceBody.renameRelations
          (ConcreteElaboration.IdentityBinderWitness.relationMap
            childBinderWitness)) targetBody)
    (sourceItems : ItemSeq signature
      (sourceContext.extend payload.region).length sourceRels)
    (targetItems : ItemSeq signature
      (targetContext.extend payload.region).length targetRels)
    (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      input.val (ConcreteElaboration.compileRegion? signature input.val
        fuelSource) (sourceContext.extend payload.region) sourceBinders
      (ConcreteElaboration.localOccurrences input.val payload.region) =
        some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (headStripRaw input payload)
      (ConcreteElaboration.compileRegion? signature
        (headStripRaw input payload) fuelTarget)
      (targetContext.extend payload.region) targetBinders
      (ConcreteElaboration.localOccurrences (headStripRaw input payload)
        payload.region) = some targetItems) :
    ∀ relEnv, ConcreteElaboration.DirectionalLocalTransport direction
      sourceContext targetContext payload.region payload.region
      (ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index)
      Lambda.canonicalModel named relEnv
      (sourceItems.renameRelations
        (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness))
      targetItems := by
  have relationContextsEq := binderWitness.relationContexts_eq
  subst targetRels
  have binderMapId :=
    identityBinderWitness_relationMap_eq_identity binderWitness
  have bindersEq := binderWitness.binders_eq
  cases bindersEq
  rw [source_localOccurrences] at sourceCompiled
  obtain ⟨sourceNodeItems, sourceChildItems, sourceNodeCompiled,
      sourceChildCompiled, sourceItemsEq⟩ :=
    ConcreteElaboration.compileOccurrencesWith?_append_split
      (fun {rels} => ConcreteElaboration.compileRegion? signature input.val
        fuelSource)
      (sourceContext.extend payload.region) sourceBinders
      (sourceNodeOccurrences input payload.region)
      (sourceChildOccurrences input payload.region)
      sourceItems sourceCompiled
  rw [headStripRaw_focused_localOccurrences] at targetCompiled
  have targetCompiled' : ConcreteElaboration.compileOccurrencesWith? signature
      (headStripRaw input payload)
      (ConcreteElaboration.compileRegion? signature
        (headStripRaw input payload) fuelTarget)
      (targetContext.extend payload.region) sourceBinders
      ((sourceNodeOccurrences input payload.region).map
          (liftOccurrence payload) ++
        (firstAddedOccurrences payload ++ secondAddedOccurrences payload ++
          (sourceChildOccurrences input payload.region).map
            (liftOccurrence payload))) = some targetItems := by
    simpa only [List.append_assoc] using targetCompiled
  obtain ⟨targetNodeItems, targetRestItems, targetNodeCompiled,
      targetRestCompiled, targetItemsEq⟩ :=
    ConcreteElaboration.compileOccurrencesWith?_append_split
      (fun {rels} => ConcreteElaboration.compileRegion? signature
        (headStripRaw input payload) fuelTarget)
      (targetContext.extend payload.region) sourceBinders
      ((sourceNodeOccurrences input payload.region).map
        (liftOccurrence payload))
      (firstAddedOccurrences payload ++ secondAddedOccurrences payload ++
        (sourceChildOccurrences input payload.region).map
          (liftOccurrence payload))
      targetItems targetCompiled'
  have targetRestCompiled' :
      ConcreteElaboration.compileOccurrencesWith? signature
        (headStripRaw input payload)
        (ConcreteElaboration.compileRegion? signature
          (headStripRaw input payload) fuelTarget)
        (targetContext.extend payload.region) sourceBinders
        (firstAddedOccurrences payload ++
          (secondAddedOccurrences payload ++
            (sourceChildOccurrences input payload.region).map
              (liftOccurrence payload))) = some targetRestItems := by
    simpa only [List.append_assoc] using targetRestCompiled
  obtain ⟨firstItems, targetTailItems, firstCompiled, targetTailCompiled,
      targetRestItemsEq⟩ :=
    ConcreteElaboration.compileOccurrencesWith?_append_split
      (fun {rels} => ConcreteElaboration.compileRegion? signature
        (headStripRaw input payload) fuelTarget)
      (targetContext.extend payload.region) sourceBinders
      (firstAddedOccurrences payload)
      (secondAddedOccurrences payload ++
        (sourceChildOccurrences input payload.region).map
          (liftOccurrence payload))
      targetRestItems targetRestCompiled'
  obtain ⟨secondItems, targetChildItems, secondCompiled, targetChildCompiled,
      targetTailItemsEq⟩ :=
    ConcreteElaboration.compileOccurrencesWith?_append_split
      (fun {rels} => ConcreteElaboration.compileRegion? signature
        (headStripRaw input payload) fuelTarget)
      (targetContext.extend payload.region) sourceBinders
      (secondAddedOccurrences payload)
      ((sourceChildOccurrences input payload.region).map
        (liftOccurrence payload))
      targetTailItems targetTailCompiled
  have oldSimulation := oldNodeOccurrences_simulation input payload
    targetWellFormed Lambda.canonicalModel named direction
    (ConcreteElaboration.compileRegion? signature input.val fuelSource)
    (ConcreteElaboration.compileRegion? signature
      (headStripRaw input payload) fuelTarget)
    (sourceContext.extend payload.region)
    (targetContext.extend payload.region) (embedding.extend payload.region)
    sourceBinders sourceBinders
    ⟨rfl, HEq.rfl⟩ targetExact.nodup sourceNodeItems targetNodeItems
    sourceNodeCompiled targetNodeCompiled
  have childSimulation := childOccurrences_simulation input payload
    Lambda.canonicalModel named direction
    (ConcreteElaboration.compileRegion? signature input.val fuelSource)
    (ConcreteElaboration.compileRegion? signature
      (headStripRaw input payload) fuelTarget)
    (sourceContext.extend payload.region)
    (targetContext.extend payload.region) (embedding.extend payload.region)
    sourceBinders sourceBinders ⟨rfl, HEq.rfl⟩
    (fun child parent sourceItem targetItem sourceOccurrence
      targetOccurrence => childOccurrence_simulation input payload
        targetWellFormed Lambda.canonicalModel named direction fuelSource
        fuelTarget (sourceContext.extend payload.region)
        (targetContext.extend payload.region) (embedding.extend payload.region)
        sourceBinders sourceBinders ⟨rfl, HEq.rfl⟩ sourceBindersCover
        targetBindersCover sourceEnumeration targetEnumeration recurse child
        parent sourceItem targetItem sourceOccurrence targetOccurrence)
    sourceChildItems targetChildItems sourceChildCompiled targetChildCompiled
  have oldSimulation' : ConcreteElaboration.ItemSeqSimulation
      Lambda.canonicalModel named direction
      (ConcreteElaboration.ContextIndexRelation.forwardMap
        (embedding.extend payload.region).index)
      sourceNodeItems targetNodeItems := by
    rw [identityBinderWitness_relationMap_eq_identity,
      renameRelations_identityRelationRenaming] at oldSimulation
    exact oldSimulation
  have childSimulation' : ConcreteElaboration.ItemSeqSimulation
      Lambda.canonicalModel named direction
      (ConcreteElaboration.ContextIndexRelation.forwardMap
        (embedding.extend payload.region).index)
      sourceChildItems targetChildItems := by
    rw [identityBinderWitness_relationMap_eq_identity,
      renameRelations_identityRelationRenaming] at childSimulation
    exact childSimulation
  rw [sourceItemsEq, targetItemsEq, targetRestItemsEq, targetTailItemsEq]
  rw [binderMapId, renameRelations_identityRelationRenaming]
  intro relEnv sourceOuter targetOuter outerAgrees
  rw [ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
    at outerAgrees
  cases direction with
  | backward =>
      intro targetLocal targetDenotes
      let sourceLocal := focusedBackwardLocal input payload targetLocal
      have extendedAgrees := focusedBackwardExtendedEnvironment
        (embedding := embedding) sourceOuter targetOuter outerAgrees targetLocal
        targetExact.nodup
      refine ⟨sourceLocal, ?_⟩
      simp only [denoteItemSeq_append] at targetDenotes
      rcases targetDenotes with ⟨targetNodeDenotes, firstDenotes,
        secondDenotes, targetChildDenotes⟩
      rw [denoteItemSeq_append]
      refine ⟨oldSimulation' _ _ relEnv ?_ targetNodeDenotes,
        childSimulation' _ _ relEnv ?_ targetChildDenotes⟩
      · rw [ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
        exact extendedAgrees
      · rw [ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
        exact extendedAgrees
  | forward =>
      intro sourceLocal sourceDenotes
      let sourceEnv := ConcreteElaboration.extendedEnvironment sourceContext
        payload.region sourceOuter sourceLocal
      obtain ⟨common, evaluationsEqual, firstValues, secondValues⟩ :=
        source_common_environment input
        payload (sourceContext.extend payload.region) sourceBinders fuelSource
        (sourceNodeItems.append sourceChildItems) (by simpa [sourceItemsEq] using
          sourceCompiled) sourceExact named sourceEnv relEnv (by
            simpa [sourceEnv, denoteItemSeq_append] using sourceDenotes)
      let fresh : Fin payload.argumentIndices.length → Lambda.Individual :=
        fun position => Lambda.canonicalModel.eval
          ((payload.firstArgument
            (payload.argumentIndices.get position)).mapFree payload.firstPort)
          common
      let targetLocal := focusedForwardLocal input payload sourceLocal fresh
      let targetEnv := ConcreteElaboration.extendedEnvironment targetContext
        payload.region targetOuter targetLocal
      have extendedAgrees := focusedForwardExtendedEnvironment
        (embedding := embedding) sourceOuter targetOuter outerAgrees sourceLocal
        fresh targetExact.nodup
      refine ⟨targetLocal, ?_⟩
      rw [denoteItemSeq_append] at sourceDenotes
      rcases sourceDenotes with ⟨sourceNodeDenotes, sourceChildDenotes⟩
      have targetNodeDenotes := oldSimulation' sourceEnv targetEnv relEnv (by
        rw [ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
        exact extendedAgrees) sourceNodeDenotes
      have targetChildDenotes := childSimulation' sourceEnv targetEnv relEnv (by
        rw [ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
        exact extendedAgrees) sourceChildDenotes
      have firstDenotes := firstAddedOccurrences_denote input payload
        targetWellFormed
        (ConcreteElaboration.compileRegion? signature
          (headStripRaw input payload) fuelTarget)
        (targetContext.extend payload.region) sourceBinders
        (allFin payload.argumentIndices.length) firstItems (by
          simpa [firstAddedOccurrences] using firstCompiled)
        common targetEnv
        (fun position index getWire => focusedForward_fresh_value input payload
          targetContext targetOuter sourceLocal fresh targetExact.nodup position
          index getWire)
        (fun port index getWire => by
          obtain ⟨sourceIndex, sourceGet, valueEq⟩ := focusedForward_old_value
            (embedding := embedding) sourceOuter targetOuter outerAgrees
            sourceLocal fresh targetExact.nodup (payload.firstWire port) index
            getWire
          have transported : targetEnv index = sourceEnv sourceIndex := by
            simpa [targetEnv, targetLocal, sourceEnv] using valueEq
          exact transported.trans (firstValues port sourceIndex sourceGet))
        named relEnv
      have secondDenotes := secondAddedOccurrences_denote input payload
        targetWellFormed
        (ConcreteElaboration.compileRegion? signature
          (headStripRaw input payload) fuelTarget)
        (targetContext.extend payload.region) sourceBinders
        (allFin payload.argumentIndices.length) secondItems (by
          simpa [secondAddedOccurrences] using secondCompiled)
        common targetEnv
        (fun position index getWire => by
          have freshEq := focusedForward_fresh_value input payload
            targetContext targetOuter sourceLocal fresh targetExact.nodup
            position index getWire
          have transported : targetEnv index = fresh position := by
            simpa [targetEnv, targetLocal] using freshEq
          exact transported.trans
            (payload.originalArgumentEvaluationsEqual common evaluationsEqual
              (payload.argumentIndices.get position)))
        (fun port index getWire => by
          obtain ⟨sourceIndex, sourceGet, valueEq⟩ := focusedForward_old_value
            (embedding := embedding) sourceOuter targetOuter outerAgrees
            sourceLocal fresh targetExact.nodup (payload.secondWire port) index
            getWire
          have transported : targetEnv index = sourceEnv sourceIndex := by
            simpa [targetEnv, targetLocal, sourceEnv] using valueEq
          exact transported.trans (secondValues port sourceIndex sourceGet))
        named relEnv
      simp only [denoteItemSeq_append]
      exact ⟨targetNodeDenotes, firstDenotes, secondDenotes,
        targetChildDenotes⟩

end HeadStripSoundness

end VisualProof.Rule
