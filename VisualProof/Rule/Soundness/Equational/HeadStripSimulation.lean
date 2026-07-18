import VisualProof.Rule.Soundness.Equational.HeadStripSemantic

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace HeadStripSoundness

theorem regularExactScopeLength
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (region : Fin input.val.regionCount) (regular : region ≠ payload.region) :
    (ConcreteElaboration.exactScopeWires (headStripRaw input payload)
        region).length =
      (ConcreteElaboration.exactScopeWires input.val region).length := by
  rw [headStripRaw_exactScopeWires, if_neg regular, List.append_nil]
  exact List.length_map _

noncomputable def extendedWireMapRegular
    (embedding : ContextEmbedding input payload source target)
    (region : Fin input.val.regionCount) (regular : region ≠ payload.region) :
    Fin (source.extend region).length → Fin (target.extend region).length :=
  fun index =>
    Fin.cast
      ((congrArg (fun localCount => target.length + localCount)
          (regularExactScopeLength input payload region regular).symm).trans
        (ConcreteElaboration.WireContext.length_extend target region).symm)
      (extendWireRenaming embedding.index
        (ConcreteElaboration.exactScopeWires input.val region).length
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend source region) index))

theorem extendedWireMapRegular_spec
    (embedding : ContextEmbedding input payload source target)
    (region : Fin input.val.regionCount) (regular : region ≠ payload.region)
    (index : Fin (source.extend region).length) :
    (target.extend region).get
        (extendedWireMapRegular embedding region regular index) =
      Fin.castAdd payload.argumentIndices.length
        ((source.extend region).get index) := by
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend source region) index
  have recover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend source region).symm
      split = index := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun outer => ?_) (fun localIndex => ?_) split
  · have mapped : extendedWireMapRegular embedding region regular
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend source region).symm
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires input.val region).length
            outer)) =
        Fin.cast
          (ConcreteElaboration.WireContext.length_extend target region).symm
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires
              (headStripRaw input payload) region).length
            (embedding.index outer)) := by
      apply Fin.ext
      simp [extendedWireMapRegular, extendWireRenaming]
    rw [mapped]
    simpa [ConcreteElaboration.WireContext.extend] using embedding.get outer
  · let lengthEq := regularExactScopeLength input payload region regular
    have mapped : extendedWireMapRegular embedding region regular
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend source region).symm
          (Fin.natAdd source.length localIndex)) =
        Fin.cast
          (ConcreteElaboration.WireContext.length_extend target region).symm
          (Fin.natAdd target.length (Fin.cast lengthEq.symm localIndex)) := by
      apply Fin.ext
      simp [extendedWireMapRegular, extendWireRenaming]
    rw [mapped]
    have exactWires := headStripRaw_exactScopeWires input payload region
    rw [if_neg regular] at exactWires
    simp only [List.append_nil] at exactWires
    simp [ConcreteElaboration.WireContext.extend, exactWires]
    exact List.getElem_map _

theorem ContextEmbedding.extend_index_eq_map_regular
    (embedding : ContextEmbedding input payload source target)
    (region : Fin input.val.regionCount) (regular : region ≠ payload.region)
    (targetNodup : (target.extend region).Nodup)
    (index : Fin (source.extend region).length) :
    (embedding.extend region).index index =
      extendedWireMapRegular embedding region regular index := by
  symm
  apply Fin.ext
  exact (List.getElem_inj targetNodup).mp (by
    simpa only [List.get_eq_getElem] using
      (extendedWireMapRegular_spec embedding region regular index).trans
        ((embedding.extend region).get index).symm)

theorem regularExtendWireEnv
    (embedding : ContextEmbedding input payload source target)
    (region : Fin input.val.regionCount) (regular : region ≠ payload.region)
    (outer : Fin target.length → D)
    (localEnv : Fin (ConcreteElaboration.exactScopeWires
      (headStripRaw input payload) region).length → D) :
    (extendWireEnv outer localEnv ∘
        Fin.cast (ConcreteElaboration.WireContext.length_extend target region)) ∘
        extendedWireMapRegular embedding region regular =
      extendWireEnv (outer ∘ embedding.index)
          (localEnv ∘ Fin.cast
            (regularExactScopeLength input payload region regular).symm) ∘
        Fin.cast
          (ConcreteElaboration.WireContext.length_extend source region) := by
  funext wire
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend source region) wire
  have recover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend source region).symm
      split = wire := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun outerIndex => ?_) (fun localIndex => ?_) split
  · simp [extendedWireMapRegular, extendWireEnv, extendWireRenaming,
      Function.comp_def]
  · simp [extendedWireMapRegular, extendWireEnv, extendWireRenaming,
      Function.comp_def]
    rw [show Fin.cast _ (Fin.natAdd target.length localIndex) =
        Fin.natAdd target.length
          (Fin.cast
            (regularExactScopeLength input payload region regular).symm
            localIndex) by
      apply Fin.ext
      rfl]
    exact Fin.addCases_right _

theorem regularLocalSelection
    (direction : ConcreteElaboration.SimulationDirection)
    (embedding : ContextEmbedding input payload source target)
    (region : Fin input.val.regionCount) (regular : region ≠ payload.region)
    (targetExact : (target.extend region).Exact region)
    (model : Lambda.LambdaModel) :
    ∀ (sourceOuter : Fin source.length → model.Carrier)
      (targetOuter : Fin target.length → model.Carrier),
      ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
          (ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index)
          sourceOuter targetOuter →
        match direction with
        | .forward => ∀ sourceLocal,
            ∃ targetLocal,
              ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
                (ConcreteElaboration.ContextIndexRelation.forwardMap
                  (embedding.extend region).index)
                (ConcreteElaboration.extendedEnvironment source region
                  sourceOuter sourceLocal)
                (ConcreteElaboration.extendedEnvironment target region
                  targetOuter targetLocal)
        | .backward => ∀ targetLocal,
            ∃ sourceLocal,
              ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
                (ConcreteElaboration.ContextIndexRelation.forwardMap
                  (embedding.extend region).index)
                (ConcreteElaboration.extendedEnvironment source region
                  sourceOuter sourceLocal)
                (ConcreteElaboration.extendedEnvironment target region
                  targetOuter targetLocal) := by
  intro sourceOuter targetOuter outerAgrees
  have outerEq : sourceOuter = targetOuter ∘ embedding.index :=
    (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
      embedding.index sourceOuter targetOuter).mp outerAgrees
  let lengthEq := regularExactScopeLength input payload region regular
  cases direction with
  | forward =>
      intro sourceLocal
      let targetLocal := sourceLocal ∘ Fin.cast lengthEq
      refine ⟨targetLocal, ?_⟩
      apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
        (embedding.extend region).index _ _).mpr
      have localEq : targetLocal ∘ Fin.cast lengthEq.symm = sourceLocal := by
        funext localIndex
        simp [targetLocal]
      have environment := regularExtendWireEnv embedding region regular
        targetOuter targetLocal
      have indexEq : (embedding.extend region).index =
          extendedWireMapRegular embedding region regular := by
        funext index
        exact embedding.extend_index_eq_map_regular region regular
          targetExact.nodup index
      unfold ConcreteElaboration.extendedEnvironment
      rw [indexEq, environment, localEq, outerEq]
  | backward =>
      intro targetLocal
      let sourceLocal := targetLocal ∘ Fin.cast lengthEq.symm
      refine ⟨sourceLocal, ?_⟩
      apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
        (embedding.extend region).index _ _).mpr
      have environment := regularExtendWireEnv embedding region regular
        targetOuter targetLocal
      have indexEq : (embedding.extend region).index =
          extendedWireMapRegular embedding region regular := by
        funext index
        exact embedding.extend_index_eq_map_regular region regular
          targetExact.nodup index
      unfold ConcreteElaboration.extendedEnvironment
      rw [indexEq, environment, outerEq]

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

noncomputable def semanticSimulation
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (targetWellFormed : (headStripRaw input payload).WellFormed signature)
    (named : NamedEnv Lambda.Individual signature) :
    ConcreteElaboration.ConcreteSemanticSimulation signature input.val
      (headStripRaw input payload) Lambda.canonicalModel named where
  source_wellFormed := input.property
  target_wellFormed := targetWellFormed
  regionMap := id
  binderMap := id
  Distinguished := fun region => region = payload.region
  occurrenceMap := fun _ _ occurrence => liftOccurrence payload occurrence
  occurrenceMap_node := by
    intro region regular node nodeRegion
    exact ⟨Fin.castAdd
      (payload.argumentIndices.length + payload.argumentIndices.length) node,
      rfl⟩
  occurrenceMap_child := by
    intro region regular child
    rfl
  root_eq := rfl
  region_shape := by
    intro parent regular child childParent
    cases kind : input.val.regions child <;> simp [headStripRaw, kind]
  localOccurrences_map := by
    intro region regular
    exact headStripRaw_regular_localOccurrences input payload region regular
  BinderWitness := fun {sourceRels targetRels} sourceBinders targetBinders =>
    ConcreteElaboration.IdentityBinderWitness input.val
      (headStripRaw input payload) sourceBinders targetBinders
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
  ContextWitness := ContextEmbedding input payload
  AtRegion := fun _ _ => True
  indexRelation := fun embedding =>
    ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index
  extendContext := by
    intro source target embedding region regular sourceExact targetExact
    exact embedding.extend region
  extendFocusedContext := by
    intro source target embedding region focused sourceExact targetExact
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
      Lambda.canonicalModel named
      (sourceItems.renameRelations
        (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness))
      targetItems
      (regularLocalSelection direction embedding region regular targetExact
        Lambda.canonicalModel)
      itemSemantics
  nodeSemantic := by
    intro sourceRels targetRels direction region source target embedding atRegion
      sourceNodup targetNodup sourceBinders targetBinders allowed binderWitness
      sourceNode targetNode regular mapped nodeRegion sourceItem targetItem
      sourceCompiled targetCompiled
    have targetNodeEq : targetNode = Fin.castAdd
        (payload.argumentIndices.length + payload.argumentIndices.length)
        sourceNode :=
      ConcreteElaboration.LocalOccurrence.node.inj mapped.symm
    subst targetNode
    have mappedCompile := compileNode_old input payload targetWellFormed source
      target embedding sourceBinders targetBinders binderWitness targetNodup
      sourceNode
    rw [sourceCompiled] at mappedCompile
    simp only [Option.map_some] at mappedCompile
    rw [targetCompiled] at mappedCompile
    have itemEq : targetItem =
        (sourceItem.renameWires embedding.index).renameRelations
          (ConcreteElaboration.IdentityBinderWitness.relationMap
            binderWitness) :=
      Option.some.inj mappedCompile
    subst targetItem
    intro sourceEnv targetEnv relEnv environments
    have environmentEq : sourceEnv = targetEnv ∘ embedding.index :=
      (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
        embedding.index sourceEnv targetEnv).mp environments
    rw [environmentEq]
    have wireSemantic := denoteItem_renameWires Lambda.canonicalModel named
      embedding.index targetEnv relEnv
      (sourceItem.renameRelations
        (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness))
    cases direction with
    | forward =>
        simpa only [Item.renameWires_renameRelations] using wireSemantic.mpr
    | backward =>
        simpa only [Item.renameWires_renameRelations] using wireSemantic.mp
  focusedRegionKernel := by
    intro sourceRels targetRels direction fuelSource fuelTarget region source
      target embedding sourceBinders targetBinders atRegion focused allowed
      binderWitness sourceExact targetExact sourceBindersCover
      targetBindersCover sourceEnumeration targetEnumeration recurse recurseAt
      sourceItems targetItems sourceCompiled targetCompiled
    subst region
    rw [ConcreteElaboration.finishRegion_renameRelations source payload.region
      (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness)
      sourceItems]
    apply ConcreteElaboration.finishRegion_denote direction source target
      payload.region payload.region
      (ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index)
      Lambda.canonicalModel named
      (sourceItems.renameRelations
        (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness))
      targetItems
    exact focusedLocalTransport input payload targetWellFormed named direction
      fuelSource fuelTarget source target embedding sourceBinders targetBinders
      binderWitness sourceExact targetExact sourceBindersCover
      targetBindersCover sourceEnumeration targetEnumeration recurse sourceItems
      targetItems sourceCompiled targetCompiled

private theorem eraseDups_map_injective
    [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (injective : Function.Injective f) :
    ∀ values : List α, (values.map f).eraseDups = values.eraseDups.map f
  | [] => rfl
  | head :: tail => by
      rw [List.map_cons, List.eraseDups_cons, List.eraseDups_cons,
        List.map_cons]
      congr 1
      rw [← eraseDups_map_injective f injective
        (tail.filter fun value => !value == head)]
      apply congrArg List.eraseDups
      rw [List.filter_map]
      apply congrArg (List.map f)
      apply congrArg (fun predicate => List.filter predicate tail)
      funext value
      simp only [Function.comp_apply]
      apply Bool.eq_iff_iff.mpr
      simp [injective.eq_iff]
termination_by values => values.length
decreasing_by
  simpa using Nat.lt_succ_of_le (List.length_filter_le _ tail)

theorem targetOpen_exposedWires
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (boundary : List (Fin input.val.wireCount)) :
    (targetOpen input payload boundary).exposedWires =
      (sourceOpen input boundary).exposedWires.map
        (Fin.castAdd payload.argumentIndices.length :
          Fin input.val.wireCount →
            Fin (input.val.wireCount + payload.argumentIndices.length)) := by
  unfold targetOpen sourceOpen OpenConcreteDiagram.exposedWires
  apply eraseDups_map_injective
  intro left right equality
  apply Fin.ext
  exact congrArg
    (fun value : Fin (input.val.wireCount +
      payload.argumentIndices.length) => value.val) equality

theorem targetOpen_hiddenWires
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (boundary : List (Fin input.val.wireCount)) :
    (targetOpen input payload boundary).hiddenWires =
      (sourceOpen input boundary).hiddenWires.map
          (Fin.castAdd payload.argumentIndices.length :
            Fin input.val.wireCount →
              Fin (input.val.wireCount + payload.argumentIndices.length)) ++
        if input.val.root = payload.region then
          (allFin payload.argumentIndices.length).map
            (Fin.natAdd input.val.wireCount)
        else [] := by
  unfold OpenConcreteDiagram.hiddenWires
  change List.filter
      (fun wire => decide
        (wire ∉ (targetOpen input payload boundary).exposedWires))
      (ConcreteElaboration.exactScopeWires (headStripRaw input payload)
        input.val.root) = _
  rw [headStripRaw_exactScopeWires, targetOpen_exposedWires]
  have oldPart :
      List.filter
          (fun wire => decide
            (wire ∉ (sourceOpen input boundary).exposedWires.map
              (Fin.castAdd payload.argumentIndices.length)))
          (List.map (Fin.castAdd payload.argumentIndices.length)
            (ConcreteElaboration.exactScopeWires input.val input.val.root)) =
        List.map (Fin.castAdd payload.argumentIndices.length)
          (List.filter
            (fun wire => decide
              (wire ∉ (sourceOpen input boundary).exposedWires))
            (ConcreteElaboration.exactScopeWires input.val input.val.root)) := by
    rw [List.filter_map]
    apply congrArg (List.map (Fin.castAdd payload.argumentIndices.length))
    apply congrArg (fun predicate => List.filter predicate
      (ConcreteElaboration.exactScopeWires input.val input.val.root))
    funext wire
    simp only [Function.comp_apply]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro notMapped sourceMember
      exact notMapped (List.mem_map.mpr ⟨wire, sourceMember, rfl⟩)
    · intro notSource mappedMember
      rcases List.mem_map.mp mappedMember with ⟨old, oldMember, equality⟩
      have oldEq : old = wire := by
        apply Fin.ext
        exact congrArg
          (fun value : Fin (input.val.wireCount +
            payload.argumentIndices.length) => value.val) equality
      exact notSource (by simpa [oldEq] using oldMember)
  by_cases rootSite : input.val.root = payload.region
  · rw [if_pos rootSite]
    have split := List.filter_append
      (p := fun wire => decide
        (wire ∉ (sourceOpen input boundary).exposedWires.map
          (Fin.castAdd payload.argumentIndices.length)))
      (List.map (Fin.castAdd payload.argumentIndices.length)
        (ConcreteElaboration.exactScopeWires input.val input.val.root))
      ((allFin payload.argumentIndices.length).map
        (Fin.natAdd input.val.wireCount))
    apply Eq.trans split
    rw [oldPart]
    congr 1
    apply List.filter_eq_self.mpr
    intro fresh freshMember
    rcases List.mem_map.mp freshMember with ⟨position, _, rfl⟩
    apply decide_eq_true
    intro exposed
    unfold sourceOpen at exposed
    rcases List.mem_map.mp exposed with ⟨old, _, equality⟩
    change Fin.castAdd payload.argumentIndices.length old =
      Fin.natAdd input.val.wireCount position at equality
    have values := congrArg
      (fun value : Fin (input.val.wireCount +
        payload.argumentIndices.length) => value.val) equality
    simp only [Fin.val_castAdd, Fin.val_natAdd] at values
    omega
  · rw [if_neg rootSite, List.append_nil]
    simpa [sourceOpen] using oldPart

def rootFresh
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second) :
    List (Fin (input.val.wireCount + payload.argumentIndices.length)) :=
  if input.val.root = payload.region then
    (allFin payload.argumentIndices.length).map
      (Fin.natAdd input.val.wireCount)
  else []

theorem targetOpen_rootWires
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (boundary : List (Fin input.val.wireCount)) :
    (targetOpen input payload boundary).rootWires =
      (sourceOpen input boundary).rootWires.map
          (Fin.castAdd payload.argumentIndices.length :
            Fin input.val.wireCount →
              Fin (input.val.wireCount + payload.argumentIndices.length)) ++
        rootFresh input payload := by
  unfold OpenConcreteDiagram.rootWires rootFresh
  rw [targetOpen_exposedWires, targetOpen_hiddenWires]
  let exposed : List (Fin
      (input.val.wireCount + payload.argumentIndices.length)) :=
    (sourceOpen input boundary).exposedWires.map
      (Fin.castAdd payload.argumentIndices.length)
  let hidden : List (Fin
      (input.val.wireCount + payload.argumentIndices.length)) :=
    (sourceOpen input boundary).hiddenWires.map
      (Fin.castAdd payload.argumentIndices.length)
  let fresh : List (Fin
      (input.val.wireCount + payload.argumentIndices.length)) :=
    if input.val.root = payload.region then
    (allFin payload.argumentIndices.length).map
      (Fin.natAdd input.val.wireCount)
    else []
  change exposed ++ (hidden ++ fresh) =
    List.map (Fin.castAdd payload.argumentIndices.length :
      Fin input.val.wireCount →
        Fin (input.val.wireCount + payload.argumentIndices.length))
      ((sourceOpen input boundary).exposedWires ++
        (sourceOpen input boundary).hiddenWires) ++ fresh
  calc
    exposed ++ (hidden ++ fresh) = (exposed ++ hidden) ++ fresh :=
      (List.append_assoc _ _ _).symm
    _ = List.map (Fin.castAdd payload.argumentIndices.length :
          Fin input.val.wireCount →
            Fin (input.val.wireCount + payload.argumentIndices.length))
          ((sourceOpen input boundary).exposedWires ++
            (sourceOpen input boundary).hiddenWires) ++ fresh := by
      exact congrArg (fun values => values ++ fresh)
        (List.map_append
          (f := Fin.castAdd payload.argumentIndices.length)
          (l₁ := (sourceOpen input boundary).exposedWires)
          (l₂ := (sourceOpen input boundary).hiddenWires)).symm

noncomputable def rootIndex
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (boundary : List (Fin input.val.wireCount)) :
    Fin (sourceOpen input boundary).rootWires.length →
      Fin (targetOpen input payload boundary).rootWires.length :=
  fun index =>
    let mapped : List (Fin
        (input.val.wireCount + payload.argumentIndices.length)) :=
      (sourceOpen input boundary).rootWires.map
          (Fin.castAdd payload.argumentIndices.length :
            Fin input.val.wireCount →
              Fin (input.val.wireCount + payload.argumentIndices.length)) ++
        rootFresh input payload
    let mappedIndex : Fin mapped.length := ⟨index.val, by
        dsimp only [mapped]
        rw [List.length_append, List.length_map]
        exact Nat.lt_of_lt_of_le index.isLt (Nat.le_add_right _ _)⟩
    Fin.cast (congrArg List.length
      (targetOpen_rootWires input payload boundary)).symm mappedIndex

theorem rootIndex_get
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (boundary : List (Fin input.val.wireCount))
    (index : Fin (sourceOpen input boundary).rootWires.length) :
    (targetOpen input payload boundary).rootWires.get
        (rootIndex input payload boundary index) =
      Fin.castAdd payload.argumentIndices.length
        ((sourceOpen input boundary).rootWires.get index) := by
  let mapped := (sourceOpen input boundary).rootWires.map
      (Fin.castAdd payload.argumentIndices.length :
        Fin input.val.wireCount →
          Fin (input.val.wireCount + payload.argumentIndices.length)) ++
        rootFresh input payload
  let mappedIndex : Fin mapped.length := ⟨index.val, by
    simp [mapped]
    exact Nat.lt_of_lt_of_le index.isLt (Nat.le_add_right _ _)⟩
  have transported := List.get_of_eq
    (targetOpen_rootWires input payload boundary)
      (rootIndex input payload boundary index)
  rw [transported]
  let transportedIndex : Fin mapped.length :=
    Fin.cast (congrArg List.length
      (targetOpen_rootWires input payload boundary))
      (rootIndex input payload boundary index)
  change mapped.get transportedIndex = _
  have transportedIndexEq : transportedIndex = mappedIndex := by
    apply Fin.ext
    rfl
  rw [transportedIndexEq]
  have valid : index.val <
      ((sourceOpen input boundary).rootWires.map
          (Fin.castAdd payload.argumentIndices.length :
            Fin input.val.wireCount →
              Fin (input.val.wireCount + payload.argumentIndices.length)) ++
        rootFresh input payload).length := by
    rw [List.length_append, List.length_map]
    exact Nat.lt_of_lt_of_le index.isLt (Nat.le_add_right _ _)
  change (((sourceOpen input boundary).rootWires.map
      (Fin.castAdd payload.argumentIndices.length :
        Fin input.val.wireCount →
          Fin (input.val.wireCount + payload.argumentIndices.length)) ++
        rootFresh input payload)[index.val]'valid) =
      Fin.castAdd payload.argumentIndices.length
        (sourceOpen input boundary).rootWires[index.val]
  rw [List.getElem_append_left (by
    rw [List.length_map]
    exact index.isLt)]
  exact List.getElem_map _

def sourceCheckedOpen
    (input : CheckedDiagram signature)
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root) :
    CheckedOpenDiagram signature :=
  ⟨sourceOpen input boundary, input.property, sourceRoot⟩

noncomputable def rootEmbedding
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (targetWellFormed : (headStripRaw input payload).WellFormed signature) :
    ContextEmbedding input payload
      (sourceOpen input boundary).rootWires
      (targetOpen input payload boundary).rootWires where
  index := rootIndex input payload boundary
  get := rootIndex_get input payload boundary
  mem_old := by
    intro wire
    constructor
    · intro member
      have scope := (OpenConcreteDiagram.mem_rootWires_iff
        (targetCheckedOpen input payload boundary sourceRoot
          targetWellFormed).val
        (targetCheckedOpen input payload boundary sourceRoot
          targetWellFormed).property _).mp member
      change ((headStripRaw input payload).wires
        (Fin.castAdd payload.argumentIndices.length wire)).scope =
          input.val.root at scope
      rw [headStripRaw_oldWire_scope] at scope
      exact (OpenConcreteDiagram.mem_rootWires_iff
        (sourceCheckedOpen input boundary sourceRoot).val
        (sourceCheckedOpen input boundary sourceRoot).property _).mpr scope
    · intro member
      have scope := (OpenConcreteDiagram.mem_rootWires_iff
        (sourceCheckedOpen input boundary sourceRoot).val
        (sourceCheckedOpen input boundary sourceRoot).property _).mp member
      apply (OpenConcreteDiagram.mem_rootWires_iff
        (targetCheckedOpen input payload boundary sourceRoot
          targetWellFormed).val
        (targetCheckedOpen input payload boundary sourceRoot
          targetWellFormed).property _).mpr
      change ((headStripRaw input payload).wires
        (Fin.castAdd payload.argumentIndices.length wire)).scope =
          input.val.root
      rw [headStripRaw_oldWire_scope]
      exact scope

end HeadStripSoundness

end VisualProof.Rule
