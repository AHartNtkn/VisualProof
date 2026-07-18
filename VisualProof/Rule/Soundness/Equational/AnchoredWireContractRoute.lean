import VisualProof.Rule.Soundness.Equational.AnchoredWireContract

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace AnchoredWireContractSoundness

/-- Moving one selected endpoint leaves ownership of every other endpoint
definitionally observable through the executor's authoritative owner lookup. -/
theorem moveEndpointRaw_endpointOwner_eq_of_ne
    (input : ConcreteDiagram)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoint current : CEndpoint input.nodeCount)
    (different : current ≠ endpoint) :
    ConcreteElaboration.endpointOwner?
        (moveEndpointRaw input sourceWire targetWire endpoint) current =
      ConcreteElaboration.endpointOwner? input current := by
  unfold ConcreteElaboration.endpointOwner? filterFin
  congr 2
  funext wire
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact moveEndpointRaw_other_occurs_iff input sourceWire targetWire endpoint
    current different wire

/-- Port resolution is unchanged away from the single moved endpoint. -/
theorem moveEndpointRaw_resolvePort_eq_of_ne
    (input : ConcreteDiagram)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount)
    (context : ConcreteElaboration.WireContext input)
    (node : Fin input.nodeCount) (port : CPort)
    (different : ({ node := node, port := port } : CEndpoint input.nodeCount) ≠
      endpoint) :
    ConcreteElaboration.resolvePort?
        (moveEndpointRaw input sourceWire targetWire endpoint) context node port =
      ConcreteElaboration.resolvePort? input context node port := by
  unfold ConcreteElaboration.resolvePort?
  have ownerEq := moveEndpointRaw_endpointOwner_eq_of_ne input sourceWire
    targetWire endpoint { node := node, port := port } different
  change (ConcreteElaboration.endpointOwner?
      (moveEndpointRaw input sourceWire targetWire endpoint)
      { node := node, port := port }).bind context.lookup? =
    (ConcreteElaboration.endpointOwner? input
      { node := node, port := port }).bind context.lookup?
  exact congrArg (fun owner => owner.bind context.lookup?) ownerEq

/-- Every node other than the endpoint's owner compiles identically across a
single endpoint move. -/
theorem compileNode_moveEndpoint_eq_of_node_ne
    (input : ConcreteDiagram)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount)
    (context : ConcreteElaboration.WireContext input)
    (binders : ConcreteElaboration.BinderContext input rels)
    (node : Fin input.nodeCount)
    (different : node ≠ endpoint.node) :
    ConcreteElaboration.compileNode? signature
        (moveEndpointRaw input sourceWire targetWire endpoint) context binders node =
      ConcreteElaboration.compileNode? signature input context binders node := by
  have portDifferent : ∀ port : CPort,
      ({ node := node, port := port } : CEndpoint input.nodeCount) ≠ endpoint := by
    intro port equality
    exact different (congrArg CEndpoint.node equality)
  have resolveEq : ∀ port : CPort,
      ConcreteElaboration.resolvePort?
          (moveEndpointRaw input sourceWire targetWire endpoint) context node port =
        ConcreteElaboration.resolvePort? input context node port := by
    intro port
    exact moveEndpointRaw_resolvePort_eq_of_ne input sourceWire targetWire
      endpoint context node port (portDifferent port)
  have mapped := ConcreteElaboration.compileNode?_map
    (signature := signature)
    (source := input)
    (target := moveEndpointRaw input sourceWire targetWire endpoint)
    context context binders binders node node id id id
    (ConcreteElaboration.identityRelationRenaming rels)
    (by
      rw [moveEndpointRaw_nodes]
      cases input.nodes node <;> rfl)
    (by
      intro port
      rw [resolveEq port]
      exact (congrFun Option.map_id _).symm)
    (by
      intro region binder nodeShape
      change binders binder = Option.map _ (binders binder)
      cases binderValue : binders binder with
      | none => rfl
      | some relation =>
          rcases relation with ⟨arity, relation⟩
          rfl)
  have identityRelationRenamingEq :
      (ConcreteElaboration.identityRelationRenaming rels :
        RelationRenaming rels rels) =
        (fun {arity} (relation : RelVar rels arity) => relation) := rfl
  rw [identityRelationRenamingEq] at mapped
  have itemMapId :
      (fun item : Item signature context.length rels =>
        (item.renameWires id).renameRelations
          (fun {arity} (relation : RelVar rels arity) => relation)) = id := by
    funext item
    rw [Item.renameWires_id, Item.renameRelations_id]
    rfl
  calc
    _ = Option.map
        (fun item : Item signature context.length rels =>
          (item.renameWires id).renameRelations
            (fun {arity} (relation : RelVar rels arity) => relation))
        (ConcreteElaboration.compileNode? signature input context binders node) :=
      mapped
    _ = Option.map id
        (ConcreteElaboration.compileNode? signature input context binders node) :=
      congrArg (fun function => Option.map function
        (ConcreteElaboration.compileNode? signature input context binders node))
        itemMapId
    _ = _ := congrFun Option.map_id _

private theorem directParent_encloses
    {input : ConcreteDiagram} {parent child : Fin input.regionCount}
    (parentEq : (input.regions child).parent? = some parent) :
    input.Encloses parent child := by
  refine ⟨⟨1, by have := child.isLt; omega⟩, ?_⟩
  simp [ConcreteDiagram.climb, parentEq]

@[simp] theorem moveEndpointRaw_context_extend
    (input : ConcreteDiagram)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount)
    (context : ConcreteElaboration.WireContext input)
    (region : Fin input.regionCount) :
    @ConcreteElaboration.WireContext.extend
        (moveEndpointRaw input sourceWire targetWire endpoint) context region =
      @ConcreteElaboration.WireContext.extend input context region := by
  unfold ConcreteElaboration.WireContext.extend
  rw [moveEndpointRaw_exactScopeWires]
  rfl

private theorem extendWireEnv_transport
    {D : Sort u} {outer sourceLocalCount targetLocalCount : Nat}
    (countEq : targetLocalCount = sourceLocalCount)
    (sourceLocal : Fin sourceLocalCount → D)
    (targetLocal : Fin targetLocalCount → D)
    (localValues : ∀ index,
      targetLocal index = sourceLocal (Fin.cast countEq index))
    (sourceIndex : Fin (outer + sourceLocalCount))
    (targetIndex : Fin (outer + targetLocalCount))
    (indexValue : sourceIndex.val = targetIndex.val) :
    ∀ outerEnv,
      extendWireEnv outerEnv sourceLocal sourceIndex =
        extendWireEnv outerEnv targetLocal targetIndex := by
  subst targetLocalCount
  have targetLocalEq : targetLocal = sourceLocal := by
    funext index
    simpa using localValues index
  subst targetLocal
  have indexEq : sourceIndex = targetIndex := by
    apply Fin.ext
    exact indexValue
  subst targetIndex
  exact fun _ => rfl

structure EndpointMoveAwayContext
    (input : ConcreteDiagram)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount)
    (sourceContext : ConcreteElaboration.WireContext input)
    (targetContext : ConcreteElaboration.WireContext
      (moveEndpointRaw input sourceWire targetWire endpoint)) : Type where
  contexts_eq : sourceContext = targetContext

namespace EndpointMoveAwayContext

def indexRelation
    (context : EndpointMoveAwayContext input sourceWire targetWire endpoint
      sourceContext targetContext) :
    ConcreteElaboration.ContextIndexRelation sourceContext.length
      targetContext.length :=
  ConcreteElaboration.ContextIndexRelation.forwardMap
    (Fin.cast (congrArg List.length context.contexts_eq))

def extend
    (context : EndpointMoveAwayContext input sourceWire targetWire endpoint
      sourceContext targetContext)
    (region : Fin input.regionCount) :
    EndpointMoveAwayContext input sourceWire targetWire endpoint
      (sourceContext.extend region) (targetContext.extend region) := by
  rcases context with ⟨rfl⟩
  exact ⟨(moveEndpointRaw_context_extend input sourceWire targetWire endpoint
    sourceContext region).symm⟩

theorem extended_agreement
    (context : EndpointMoveAwayContext input sourceWire targetWire endpoint
      sourceContext targetContext)
    (region : Fin input.regionCount)
    (sourceOuter : Fin sourceContext.length → D)
    (targetOuter : Fin targetContext.length → D)
    (outerAgrees : context.indexRelation.EnvironmentsAgree sourceOuter targetOuter)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires input region).length → D) :
    ∃ targetLocal : Fin (ConcreteElaboration.exactScopeWires
        (moveEndpointRaw input sourceWire targetWire endpoint) region).length → D,
      (context.extend region).indexRelation.EnvironmentsAgree
        (ConcreteElaboration.extendedEnvironment sourceContext region
          sourceOuter sourceLocal)
        (ConcreteElaboration.extendedEnvironment targetContext region
          targetOuter targetLocal) := by
  rcases context with ⟨contextsEq⟩
  cases contextsEq
  have outerEq : sourceOuter = targetOuter := by
    simpa only [indexRelation,
      ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap,
      Function.comp_id] using outerAgrees
  let countEq := congrArg List.length
    (moveEndpointRaw_exactScopeWires input sourceWire targetWire endpoint region)
  let targetLocal := fun index => sourceLocal (Fin.cast countEq index)
  refine ⟨targetLocal, ?_⟩
  unfold indexRelation ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
    ConcreteElaboration.ContextIndexRelation.forwardMap
  intro sourceIndex targetIndex related
  subst targetIndex
  subst targetOuter
  simp only [ConcreteElaboration.extendedEnvironment, targetLocal,
    Function.comp_apply]
  apply extendWireEnv_transport countEq sourceLocal targetLocal
  · intro localIndex
    rfl
  · rfl

theorem extended_agreement_backward
    (context : EndpointMoveAwayContext input sourceWire targetWire endpoint
      sourceContext targetContext)
    (region : Fin input.regionCount)
    (sourceOuter : Fin sourceContext.length → D)
    (targetOuter : Fin targetContext.length → D)
    (outerAgrees : context.indexRelation.EnvironmentsAgree sourceOuter targetOuter)
    (targetLocal : Fin (ConcreteElaboration.exactScopeWires
      (moveEndpointRaw input sourceWire targetWire endpoint) region).length → D) :
    ∃ sourceLocal : Fin (ConcreteElaboration.exactScopeWires input region).length → D,
      (context.extend region).indexRelation.EnvironmentsAgree
        (ConcreteElaboration.extendedEnvironment sourceContext region
          sourceOuter sourceLocal)
        (ConcreteElaboration.extendedEnvironment targetContext region
          targetOuter targetLocal) := by
  rcases context with ⟨contextsEq⟩
  cases contextsEq
  have outerEq : sourceOuter = targetOuter := by
    simpa only [indexRelation,
      ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap,
      Function.comp_id] using outerAgrees
  let countEq := congrArg List.length
    (moveEndpointRaw_exactScopeWires input sourceWire targetWire endpoint region)
  let sourceLocal := fun index => targetLocal (Fin.cast countEq.symm index)
  refine ⟨sourceLocal, ?_⟩
  unfold indexRelation ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
    ConcreteElaboration.ContextIndexRelation.forwardMap
  intro sourceIndex targetIndex related
  subst targetIndex
  subst targetOuter
  simp only [ConcreteElaboration.extendedEnvironment, sourceLocal,
    Function.comp_apply]
  apply extendWireEnv_transport countEq sourceLocal targetLocal
  · intro localIndex
    apply congrArg targetLocal
    apply Fin.ext
    rfl
  · rfl

theorem endpoint_relation_of_coalesced
    (context : EndpointMoveAwayContext input sourceWire targetWire endpoint
      sourceContext targetContext)
    (sourceExact : sourceContext.Exact region)
    (sourceEnv : Fin sourceContext.length → D)
    (targetEnv : Fin targetContext.length → D)
    (identityAgrees : context.indexRelation.EnvironmentsAgree
      sourceEnv targetEnv)
    (coalesced : ∀ sourceIndex targetIndex,
      sourceContext.get sourceIndex = sourceWire →
      sourceContext.get targetIndex = targetWire →
      sourceEnv sourceIndex = sourceEnv targetIndex) :
    (endpointMoveRelation input sourceWire targetWire sourceContext targetContext
      ).EnvironmentsAgree sourceEnv targetEnv := by
  rcases context with ⟨contextsEq⟩
  cases contextsEq
  have envEq : sourceEnv = targetEnv := by
    simpa only [indexRelation,
      ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap,
      Function.comp_id] using identityAgrees
  subst targetEnv
  apply endpointMoveRelation_environmentsAgree input sourceWire targetWire
  · intro sourceIndex targetIndex sameWire
    have indexEq : sourceIndex = targetIndex := by
      apply Fin.ext
      exact (List.getElem_inj sourceExact.nodup).mp (by
        simpa only [List.get_eq_getElem] using sameWire)
    subst targetIndex
    rfl
  · exact coalesced

end EndpointMoveAwayContext

/-- Outside the subtree containing the moved endpoint, the authoritative
compiler is simulated with the identity lexical relation. -/
noncomputable def endpointMoveAwaySimulation
    (input : ConcreteDiagram)
    (wellFormed : input.WellFormed signature)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount)
    (targetWellFormed :
      (moveEndpointRaw input sourceWire targetWire endpoint).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature) :
    ConcreteElaboration.ConcreteSemanticSimulation signature input
      (moveEndpointRaw input sourceWire targetWire endpoint) model named where
  source_wellFormed := wellFormed
  target_wellFormed := targetWellFormed
  regionMap := id
  binderMap := id
  Distinguished := fun _ => False
  occurrenceMap := fun _ _ occurrence => occurrence
  occurrenceMap_node := by
    intro region regular node nodeRegion
    exact ⟨node, rfl⟩
  occurrenceMap_child := by
    intro region regular child
    rfl
  root_eq := rfl
  region_shape := by
    intro parent regular child childParent
    rw [moveEndpointRaw_regions]
    cases kind : input.regions child <;> simp [kind] <;> rfl
  localOccurrences_map := by
    intro region regular
    rw [moveEndpointRaw_localOccurrences]
    have mapIdentity :
        (fun occurrence : ConcreteElaboration.LocalOccurrence input.regionCount
          input.nodeCount => occurrence) = id := rfl
    rw [mapIdentity]
    exact (List.map_id _).symm
  BinderWitness := fun {sourceRels targetRels} sourceBinders targetBinders =>
    ConcreteElaboration.IdentityBinderWitness input
      (moveEndpointRaw input sourceWire targetWire endpoint)
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
  ContextWitness := EndpointMoveAwayContext input sourceWire targetWire endpoint
  AtRegion := fun _ region =>
    ¬ input.Encloses region (input.nodes endpoint.node).region
  indexRelation := fun context => context.indexRelation
  extendContext := by
    intro sourceContext targetContext context region regular sourceExact
      targetExact
    exact context.extend region
  extendFocusedContext := by
    intro sourceContext targetContext context region focused sourceExact
      targetExact
    exact False.elim focused
  at_child := by
    intro sourceContext targetContext context parent regular sourceExact
      targetExact child parentAway childParent
    intro childEncloses
    exact parentAway (ConcreteElaboration.checked_encloses_trans wellFormed
      (directParent_encloses childParent) childEncloses)
  at_extended := by
    intro sourceContext targetContext context region regular sourceExact
      targetExact away
    exact away
  at_focused_child := by
    intro sourceContext targetContext context parent focused sourceExact
      targetExact child atParent sourceParent targetParent
    exact False.elim focused
  localTransport := by
    intro sourceRels targetRels direction fuelSource fuelTarget sourceContext
      targetContext context sourceBinders targetBinders binderWitness region
      atRegion regular allowed sourceExact targetExact sourceCover targetCover
      sourceEnumeration targetEnumeration sourceItems targetItems sourceCompiled
      targetCompiled itemSimulation
    rcases context with ⟨contextsEq⟩
    cases contextsEq
    let extendedContext :=
      EndpointMoveAwayContext.extend
        (⟨rfl⟩ : EndpointMoveAwayContext input sourceWire targetWire endpoint
          sourceContext sourceContext) region
    cases binderWitness.relationContexts_eq
    have identityRelationRenamingEq :
        (ConcreteElaboration.identityRelationRenaming sourceRels :
          RelationRenaming sourceRels sourceRels) =
            (fun {arity} (relation : RelVar sourceRels arity) => relation) := rfl
    change ∀ relEnv,
      ConcreteElaboration.DirectionalLocalTransport direction
        (source := input)
        (target := moveEndpointRaw input sourceWire targetWire endpoint)
        sourceContext sourceContext region region
        (ConcreteElaboration.ContextIndexRelation.forwardMap id)
        model named relEnv
        (sourceItems.renameRelations
          (ConcreteElaboration.identityRelationRenaming sourceRels)) targetItems
    rw [identityRelationRenamingEq, ItemSeq.renameRelations_id]
    change ConcreteElaboration.ItemSeqSimulation model named direction
      extendedContext.indexRelation
      (sourceItems.renameRelations
        (ConcreteElaboration.identityRelationRenaming sourceRels)) targetItems
        at itemSimulation
    rw [identityRelationRenamingEq, ItemSeq.renameRelations_id] at itemSimulation
    apply ConcreteElaboration.directionalLocalTransport_of_agreement
      (source := input)
      (target := moveEndpointRaw input sourceWire targetWire endpoint)
      direction sourceContext sourceContext region region
      (ConcreteElaboration.ContextIndexRelation.forwardMap id)
      extendedContext.indexRelation model named sourceItems targetItems
    · intro sourceOuter targetOuter outerAgrees
      have outerEq : sourceOuter = targetOuter := by
        simpa only [
          ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap,
          Function.comp_id] using outerAgrees
      let localCountEq :
          (ConcreteElaboration.exactScopeWires
            (moveEndpointRaw input sourceWire targetWire endpoint) region).length =
            (ConcreteElaboration.exactScopeWires input region).length :=
        congrArg List.length (moveEndpointRaw_exactScopeWires input sourceWire
          targetWire endpoint region)
      cases direction with
      | forward =>
          intro sourceLocal
          let targetLocal := fun index => sourceLocal (Fin.cast localCountEq index)
          refine ⟨targetLocal, ?_⟩
          unfold EndpointMoveAwayContext.indexRelation
            ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
            ConcreteElaboration.ContextIndexRelation.forwardMap
          intro sourceIndex targetIndex related
          subst targetIndex
          subst targetOuter
          simp only [ConcreteElaboration.extendedEnvironment, targetLocal,
            Function.comp_apply]
          apply extendWireEnv_transport localCountEq sourceLocal targetLocal
          · intro localIndex
            rfl
          · rfl
      | backward =>
          intro targetLocal
          let sourceLocal := fun index => targetLocal
            (Fin.cast localCountEq.symm index)
          refine ⟨sourceLocal, ?_⟩
          unfold EndpointMoveAwayContext.indexRelation
            ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
            ConcreteElaboration.ContextIndexRelation.forwardMap
          intro sourceIndex targetIndex related
          subst targetIndex
          subst targetOuter
          simp only [ConcreteElaboration.extendedEnvironment, sourceLocal,
            Function.comp_apply]
          apply extendWireEnv_transport localCountEq sourceLocal targetLocal
          · intro localIndex
            apply congrArg targetLocal
            apply Fin.ext
            rfl
          · rfl
    · exact itemSimulation
  nodeSemantic := by
    intro sourceRels targetRels direction region sourceContext targetContext
      context atRegion sourceNodup targetNodup sourceBinders targetBinders
      allowed binderWitness sourceNode targetNode regular mapped nodeRegion
      sourceItem targetItem sourceCompiled targetCompiled
    rcases context with ⟨contextsEq⟩
    cases contextsEq
    have targetNodeEq : targetNode = sourceNode :=
      ConcreteElaboration.LocalOccurrence.node.inj mapped.symm
    subst targetNode
    have nodeNe : sourceNode ≠ endpoint.node := by
      intro equality
      subst sourceNode
      exact atRegion (by rw [nodeRegion]; exact
        ConcreteDiagram.Encloses.refl input region)
    apply ConcreteElaboration.compileNode?_itemSimulation_of_related_ports
      (source := input)
      (target := moveEndpointRaw input sourceWire targetWire endpoint)
      model named direction sourceContext sourceContext
      (ConcreteElaboration.ContextIndexRelation.forwardMap id)
      sourceBinders targetBinders
      (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness)
      sourceNode sourceNode id id
    · rw [moveEndpointRaw_nodes]
      cases input.nodes sourceNode <;> rfl
    · intro port sourceIndex targetIndex sourceResolved targetResolved
      have resolved := moveEndpointRaw_resolvePort_eq_of_ne input sourceWire
        targetWire endpoint sourceContext sourceNode port (by
          intro equality
          exact nodeNe (congrArg CEndpoint.node equality))
      rw [sourceResolved, targetResolved] at resolved
      change sourceIndex = targetIndex
      apply Fin.ext
      exact congrArg Fin.val (Option.some.inj resolved).symm
    · intro nodeOwner binder arity sourceRelation sourceAtom sourceLookup
      rcases binderWitness with ⟨relationContextsEq, bindersEq⟩
      subst targetRels
      cases bindersEq
      simpa [ConcreteElaboration.IdentityBinderWitness.relationMap,
        ConcreteElaboration.identityRelationRenaming] using sourceLookup
    · exact sourceCompiled
    · exact targetCompiled
  focusedRegionKernel := by
    intro sourceRels targetRels direction fuelSource fuelTarget region
      sourceContext targetContext context sourceBinders targetBinders atRegion
      focused
    exact False.elim focused

theorem compileNode_moveEndpoint_itemSimulation_of_node_ne
    (input : ConcreteDiagram)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount)
    (sourceContext : ConcreteElaboration.WireContext input)
    (targetContext : ConcreteElaboration.WireContext
      (moveEndpointRaw input sourceWire targetWire endpoint))
    (context : EndpointMoveAwayContext input sourceWire targetWire endpoint
      sourceContext targetContext)
    (sourceBinders : ConcreteElaboration.BinderContext input sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (moveEndpointRaw input sourceWire targetWire endpoint) targetRels)
    (binderWitness : ConcreteElaboration.IdentityBinderWitness input
      (moveEndpointRaw input sourceWire targetWire endpoint)
      sourceBinders targetBinders)
    (node : Fin input.nodeCount)
    (nodeNe : node ≠ endpoint.node)
    (sourceItem : Item signature sourceContext.length sourceRels)
    (targetItem : Item signature targetContext.length targetRels)
    (sourceCompiled : ConcreteElaboration.compileNode? signature input
      sourceContext sourceBinders node = some sourceItem)
    (targetCompiled : ConcreteElaboration.compileNode? signature
      (moveEndpointRaw input sourceWire targetWire endpoint)
      targetContext targetBinders node = some targetItem)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection) :
    ConcreteElaboration.ItemSimulation model named direction
      context.indexRelation
      (sourceItem.renameRelations
        (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness))
      targetItem := by
  rcases context with ⟨contextsEq⟩
  cases contextsEq
  apply ConcreteElaboration.compileNode?_itemSimulation_of_related_ports
    (source := input)
    (target := moveEndpointRaw input sourceWire targetWire endpoint)
    model named direction sourceContext sourceContext
    (ConcreteElaboration.ContextIndexRelation.forwardMap id)
    sourceBinders targetBinders
    (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness)
    node node id id
  · rw [moveEndpointRaw_nodes]
    cases input.nodes node <;> rfl
  · intro port sourceIndex targetIndex sourceResolved targetResolved
    have resolved := moveEndpointRaw_resolvePort_eq_of_ne input sourceWire
      targetWire endpoint sourceContext node port (by
        intro equality
        exact nodeNe (congrArg CEndpoint.node equality))
    rw [sourceResolved, targetResolved] at resolved
    change sourceIndex = targetIndex
    apply Fin.ext
    exact congrArg Fin.val (Option.some.inj resolved).symm
  · intro nodeOwner binder arity sourceRelation sourceAtom sourceLookup
    rcases binderWitness with ⟨relationContextsEq, bindersEq⟩
    subst targetRels
    cases bindersEq
    simpa [ConcreteElaboration.IdentityBinderWitness.relationMap,
      ConcreteElaboration.identityRelationRenaming] using sourceLookup
  · exact sourceCompiled
  · exact targetCompiled

theorem compileRegion_moveEndpoint_away_regionSimulation
    (input : ConcreteDiagram)
    (wellFormed : input.WellFormed signature)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount)
    (targetWellFormed :
      (moveEndpointRaw input sourceWire targetWire endpoint).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    {sourceRels targetRels : RelCtx}
    (fuelSource fuelTarget : Nat)
    (region : Fin input.regionCount)
    (sourceContext : ConcreteElaboration.WireContext input)
    (targetContext : ConcreteElaboration.WireContext
      (moveEndpointRaw input sourceWire targetWire endpoint))
    (context : EndpointMoveAwayContext input sourceWire targetWire endpoint
      sourceContext targetContext)
    (away : ¬ input.Encloses region (input.nodes endpoint.node).region)
    (sourceBinders : ConcreteElaboration.BinderContext input sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (moveEndpointRaw input sourceWire targetWire endpoint) targetRels)
    (binderWitness : ConcreteElaboration.IdentityBinderWitness input
      (moveEndpointRaw input sourceWire targetWire endpoint)
      sourceBinders targetBinders)
    (sourceCover : sourceBinders.Covers region)
    (targetCover : targetBinders.Covers region)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration input
      sourceBinders region)
    (targetEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (moveEndpointRaw input sourceWire targetWire endpoint)
      targetBinders region)
    (sourceExact : (sourceContext.extend region).Exact region)
    (targetExact : (targetContext.extend region).Exact region)
    (sourceBody : Region signature sourceContext.length sourceRels)
    (targetBody : Region signature targetContext.length targetRels)
    (sourceCompiled : ConcreteElaboration.compileRegion? signature input
      fuelSource region sourceContext sourceBinders = some sourceBody)
    (targetCompiled : ConcreteElaboration.compileRegion? signature
      (moveEndpointRaw input sourceWire targetWire endpoint)
      fuelTarget region targetContext targetBinders = some targetBody) :
    ConcreteElaboration.RegionSimulation model named direction
      context.indexRelation
      (sourceBody.renameRelations
        (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness))
      targetBody := by
  let simulation := endpointMoveAwaySimulation input wellFormed sourceWire
    targetWire endpoint targetWellFormed model named
  exact simulation.compileRegion_denote direction fuelSource fuelTarget region
    sourceContext targetContext context away sourceBinders targetBinders
    (by trivial) binderWitness sourceCover targetCover sourceEnumeration
    targetEnumeration sourceExact targetExact sourceBody targetBody sourceCompiled
    targetCompiled

/-- A selected occurrence frame that excludes the moved endpoint's subtree
is simulated pointwise under the identity lexical relation. -/
theorem compileOccurrences_moveEndpoint_away_itemSeqSimulation
    (input : ConcreteDiagram)
    (wellFormed : input.WellFormed signature)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount)
    (targetWellFormed :
      (moveEndpointRaw input sourceWire targetWire endpoint).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    {sourceRels targetRels : RelCtx}
    (fuelSource fuelTarget : Nat)
    (region : Fin input.regionCount)
    (sourceContext : ConcreteElaboration.WireContext input)
    (targetContext : ConcreteElaboration.WireContext
      (moveEndpointRaw input sourceWire targetWire endpoint))
    (context : EndpointMoveAwayContext input sourceWire targetWire endpoint
      sourceContext targetContext)
    (sourceExact : sourceContext.Exact region)
    (targetExact : targetContext.Exact region)
    (sourceBinders : ConcreteElaboration.BinderContext input sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (moveEndpointRaw input sourceWire targetWire endpoint) targetRels)
    (binderWitness : ConcreteElaboration.IdentityBinderWitness input
      (moveEndpointRaw input sourceWire targetWire endpoint)
      sourceBinders targetBinders)
    (sourceCover : sourceBinders.Covers region)
    (targetCover : targetBinders.Covers region)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration input
      sourceBinders region)
    (targetEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (moveEndpointRaw input sourceWire targetWire endpoint)
      targetBinders region)
    (occurrences : List
      (ConcreteElaboration.LocalOccurrence input.regionCount input.nodeCount))
    (members : ∀ occurrence, occurrence ∈ occurrences →
      occurrence ∈ ConcreteElaboration.localOccurrences input region)
    (away : ∀ occurrence, occurrence ∈ occurrences →
      match occurrence with
      | .node node => node ≠ endpoint.node
      | .child child =>
          ¬ input.Encloses child (input.nodes endpoint.node).region)
    (sourceItems : ItemSeq signature sourceContext.length sourceRels)
    (targetItems : ItemSeq signature targetContext.length targetRels)
    (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature input
      (ConcreteElaboration.compileRegion? signature input fuelSource)
      sourceContext sourceBinders occurrences = some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (moveEndpointRaw input sourceWire targetWire endpoint)
      (ConcreteElaboration.compileRegion? signature
        (moveEndpointRaw input sourceWire targetWire endpoint) fuelTarget)
      targetContext targetBinders (occurrences.map id) = some targetItems) :
    ConcreteElaboration.ItemSeqSimulation model named direction
      context.indexRelation
      (sourceItems.renameRelations
        (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness))
      targetItems := by
  apply ConcreteElaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
    model named direction
    (ConcreteElaboration.compileRegion? signature input fuelSource)
    (ConcreteElaboration.compileRegion? signature
      (moveEndpointRaw input sourceWire targetWire endpoint) fuelTarget)
    sourceContext targetContext sourceBinders targetBinders
    context.indexRelation
    (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness)
    id occurrences
  · intro occurrence member sourceItem targetItem sourceOccurrenceCompiled
      targetOccurrenceCompiled
    have occurrenceAway := away occurrence member
    cases occurrence with
    | node node =>
        exact compileNode_moveEndpoint_itemSimulation_of_node_ne input sourceWire
          targetWire endpoint sourceContext targetContext context sourceBinders
          targetBinders binderWitness node occurrenceAway sourceItem targetItem
          sourceOccurrenceCompiled targetOccurrenceCompiled model named direction
    | child child =>
        have childParent :=
          (ConcreteElaboration.mem_localOccurrences_child input region child).mp
            (members (.child child) member)
        cases childKind : input.regions child with
        | sheet =>
            simp [ConcreteElaboration.compileOccurrenceWith?, childKind]
              at sourceOccurrenceCompiled
        | cut actualParent =>
            have parentEq : actualParent = region := by
              rw [childKind] at childParent
              exact Option.some.inj childParent
            subst actualParent
            have targetKind :
                (moveEndpointRaw input sourceWire targetWire endpoint).regions
                    child = .cut region := by
              simpa only [moveEndpointRaw_regions] using childKind
            cases sourceResult : ConcreteElaboration.compileRegion? signature
                input fuelSource child sourceContext sourceBinders with
            | none =>
                simp [ConcreteElaboration.compileOccurrenceWith?, childKind,
                  sourceResult] at sourceOccurrenceCompiled
            | some sourceBody =>
                simp [ConcreteElaboration.compileOccurrenceWith?, childKind,
                  sourceResult] at sourceOccurrenceCompiled
                subst sourceItem
                cases targetResult : ConcreteElaboration.compileRegion? signature
                    (moveEndpointRaw input sourceWire targetWire endpoint)
                    fuelTarget child targetContext targetBinders with
                | none =>
                    simp [ConcreteElaboration.compileOccurrenceWith?, targetKind,
                      targetResult] at targetOccurrenceCompiled
                | some targetBody =>
                    simp [ConcreteElaboration.compileOccurrenceWith?, targetKind,
                      targetResult] at targetOccurrenceCompiled
                    subst targetItem
                    have bodies :=
                      compileRegion_moveEndpoint_away_regionSimulation input
                        wellFormed sourceWire targetWire endpoint targetWellFormed
                        model named direction.flip fuelSource fuelTarget child
                        sourceContext targetContext context occurrenceAway
                        sourceBinders targetBinders binderWitness
                        (ConcreteElaboration.BinderContext.covers_cut_child
                          sourceCover childKind)
                        (ConcreteElaboration.BinderContext.covers_cut_child
                          targetCover targetKind)
                        (sourceEnumeration.cutChild wellFormed childKind)
                        (targetEnumeration.cutChild targetWellFormed targetKind)
                        (sourceExact.extend_child wellFormed childParent)
                        (targetExact.extend_child targetWellFormed (by
                          simpa only [moveEndpointRaw_regions] using childParent))
                        sourceBody targetBody sourceResult targetResult
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
        | bubble actualParent arity =>
            have parentEq : actualParent = region := by
              rw [childKind] at childParent
              exact Option.some.inj childParent
            subst actualParent
            have targetKind :
                (moveEndpointRaw input sourceWire targetWire endpoint).regions
                    child = .bubble region arity := by
              simpa only [moveEndpointRaw_regions] using childKind
            let sourcePushed := sourceBinders.push child arity
            let targetPushed := targetBinders.push child arity
            cases sourceResult : ConcreteElaboration.compileRegion? signature
                input fuelSource child sourceContext sourcePushed with
            | none =>
                simp [ConcreteElaboration.compileOccurrenceWith?, childKind,
                  sourcePushed, sourceResult] at sourceOccurrenceCompiled
            | some sourceBody =>
                simp [ConcreteElaboration.compileOccurrenceWith?, childKind,
                  sourcePushed, sourceResult] at sourceOccurrenceCompiled
                subst sourceItem
                cases targetResult : ConcreteElaboration.compileRegion? signature
                    (moveEndpointRaw input sourceWire targetWire endpoint)
                    fuelTarget child targetContext targetPushed with
                | none =>
                    simp [ConcreteElaboration.compileOccurrenceWith?, targetKind,
                      targetPushed, targetResult] at targetOccurrenceCompiled
                | some targetBody =>
                    simp [ConcreteElaboration.compileOccurrenceWith?, targetKind,
                      targetPushed, targetResult] at targetOccurrenceCompiled
                    subst targetItem
                    let pushedWitness : ConcreteElaboration.IdentityBinderWitness
                        input (moveEndpointRaw input sourceWire targetWire endpoint)
                        sourcePushed targetPushed := by
                      rcases binderWitness with
                        ⟨relationContextsEq, bindersEq⟩
                      subst targetRels
                      cases bindersEq
                      exact ⟨rfl, HEq.rfl⟩
                    have bodies :=
                      compileRegion_moveEndpoint_away_regionSimulation input
                        wellFormed sourceWire targetWire endpoint targetWellFormed
                        model named direction fuelSource fuelTarget child
                        sourceContext targetContext context occurrenceAway
                        sourcePushed targetPushed pushedWitness
                        (ConcreteElaboration.BinderContext.push_covers_bubble_child
                          sourceCover childKind)
                        (ConcreteElaboration.BinderContext.push_covers_bubble_child
                          targetCover targetKind)
                        (sourceEnumeration.bubbleChild wellFormed childKind)
                        (targetEnumeration.bubbleChild targetWellFormed targetKind)
                        (sourceExact.extend_child wellFormed childParent)
                        (targetExact.extend_child targetWellFormed (by
                          simpa only [moveEndpointRaw_regions] using childParent))
                        sourceBody targetBody sourceResult targetResult
                    have pushedMap :
                        (ConcreteElaboration.IdentityBinderWitness.relationMap
                          pushedWitness : RelationRenaming
                            (arity :: sourceRels) (arity :: targetRels)) =
                          (RelationRenaming.lift
                            (ConcreteElaboration.IdentityBinderWitness.relationMap
                              binderWitness) arity : RelationRenaming
                                (arity :: sourceRels) (arity :: targetRels)) := by
                      rcases binderWitness with
                        ⟨relationContextsEq, bindersEq⟩
                      subst targetRels
                      cases bindersEq
                      simpa [pushedWitness,
                        ConcreteElaboration.IdentityBinderWitness.relationMap,
                        ConcreteElaboration.identityRelationRenaming] using
                          (RelationRenaming.lift_id_fun
                            (source := sourceRels) arity).symm
                    rw [pushedMap] at bodies
                    intro sourceEnv targetEnv relEnv environments
                    simp only [Item.renameRelations, bubble_denotes_exists]
                    cases direction with
                    | forward =>
                        rintro ⟨relationValue, sourceDenotes⟩
                        exact ⟨relationValue,
                          bodies sourceEnv targetEnv (relationValue, relEnv)
                            environments sourceDenotes⟩
                    | backward =>
                        rintro ⟨relationValue, targetDenotes⟩
                        exact ⟨relationValue,
                          bodies sourceEnv targetEnv (relationValue, relEnv)
                            environments targetDenotes⟩
  · exact sourceCompiled
  · exact targetCompiled

/-- At a site where both wire identities are visible and the surrounding
denotation coalesces their values, moving the selected endpoint preserves the
finished region in both directions. -/
theorem finishRegion_moveEndpoint_equiv_of_coalesced
    (input : ConcreteDiagram)
    (wellFormed : input.WellFormed signature)
    (sourceWire targetWire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount)
    (distinct : sourceWire ≠ targetWire)
    (sourceOccurs : input.EndpointOccurs sourceWire endpoint)
    (targetWellFormed :
      (moveEndpointRaw input sourceWire targetWire endpoint).WellFormed signature)
    (region : Fin input.regionCount)
    (sourceWireVisible : input.Encloses (input.wires sourceWire).scope region)
    (targetWireVisible : input.Encloses (input.wires targetWire).scope region)
    {rels : RelCtx}
    (fuelSource fuelTarget : Nat)
    (sourceContext : ConcreteElaboration.WireContext input)
    (targetContext : ConcreteElaboration.WireContext
      (moveEndpointRaw input sourceWire targetWire endpoint))
    (context : EndpointMoveAwayContext input sourceWire targetWire endpoint
      sourceContext targetContext)
    (sourceBinders : ConcreteElaboration.BinderContext input rels)
    (targetBinders : ConcreteElaboration.BinderContext
      (moveEndpointRaw input sourceWire targetWire endpoint) rels)
    (binderWitness : ConcreteElaboration.IdentityBinderWitness input
      (moveEndpointRaw input sourceWire targetWire endpoint)
      sourceBinders targetBinders)
    (sourceCover : sourceBinders.Covers region)
    (targetCover : targetBinders.Covers region)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration input
      sourceBinders region)
    (targetEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (moveEndpointRaw input sourceWire targetWire endpoint)
      targetBinders region)
    (sourceExact : (sourceContext.extend region).Exact region)
    (targetExact : (targetContext.extend region).Exact region)
    (sourceItems : ItemSeq signature (sourceContext.extend region).length rels)
    (targetItems : ItemSeq signature (targetContext.extend region).length rels)
    (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature input
      (ConcreteElaboration.compileRegion? signature input fuelSource)
      (sourceContext.extend region) sourceBinders
      (ConcreteElaboration.localOccurrences input region) = some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (moveEndpointRaw input sourceWire targetWire endpoint)
      (ConcreteElaboration.compileRegion? signature
        (moveEndpointRaw input sourceWire targetWire endpoint) fuelTarget)
      (targetContext.extend region) targetBinders
      (ConcreteElaboration.localOccurrences
        (moveEndpointRaw input sourceWire targetWire endpoint) region) =
        some targetItems)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceCoalesced : ∀ sourceOuter sourceLocal relEnv,
      denoteItemSeq model named
          (ConcreteElaboration.extendedEnvironment sourceContext region
            sourceOuter sourceLocal) relEnv sourceItems →
      ∀ sourceIndex targetIndex,
        (sourceContext.extend region).get sourceIndex = sourceWire →
        (sourceContext.extend region).get targetIndex = targetWire →
        ConcreteElaboration.extendedEnvironment sourceContext region
            sourceOuter sourceLocal sourceIndex =
          ConcreteElaboration.extendedEnvironment sourceContext region
            sourceOuter sourceLocal targetIndex)
    (targetCoalesced : ∀ targetOuter targetLocal relEnv,
      denoteItemSeq model named
          (ConcreteElaboration.extendedEnvironment targetContext region
            targetOuter targetLocal) relEnv targetItems →
      ∀ sourceIndex targetIndex,
        (targetContext.extend region).get sourceIndex = sourceWire →
        (targetContext.extend region).get targetIndex = targetWire →
        ConcreteElaboration.extendedEnvironment targetContext region
            targetOuter targetLocal sourceIndex =
          ConcreteElaboration.extendedEnvironment targetContext region
            targetOuter targetLocal targetIndex) :
    ∀ sourceOuter targetOuter relEnv,
      context.indexRelation.EnvironmentsAgree sourceOuter targetOuter →
      (denoteRegion model named sourceOuter relEnv
          (ConcreteElaboration.finishRegion input sourceContext region sourceItems) ↔
        denoteRegion model named targetOuter relEnv
          (ConcreteElaboration.finishRegion
            (moveEndpointRaw input sourceWire targetWire endpoint)
            targetContext region targetItems)) := by
  intro sourceOuter targetOuter relEnv outerAgrees
  let extendedContext := context.extend region
  let moveContext : EndpointMoveContext input sourceWire targetWire endpoint
      (sourceContext.extend region) (targetContext.extend region) := {
    contexts_eq := extendedContext.contexts_eq
    source_mem := (sourceExact.mem_iff sourceWire).2 sourceWireVisible
    target_mem := (sourceExact.mem_iff targetWire).2 targetWireVisible
  }
  have identityRelationRenamingEq :
      (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness :
        RelationRenaming rels rels) =
          (fun {arity} (relation : RelVar rels arity) => relation) := by
    rcases binderWitness with ⟨relationContextsEq, bindersEq⟩
    rfl
  have semantic : ∀ direction,
      ConcreteElaboration.ItemSeqSimulation model named direction
        (endpointMoveRelation input sourceWire targetWire
          (sourceContext.extend region) (targetContext.extend region))
        (sourceItems.renameRelations
          (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness))
        targetItems := by
    intro direction
    simpa only [identityRelationRenamingEq, ItemSeq.renameRelations_id] using
      (compileOccurrences_moveEndpoint_itemSeqSimulation input wellFormed
        sourceWire targetWire endpoint distinct sourceOccurs targetWellFormed model
        named direction fuelSource fuelTarget region (sourceContext.extend region)
        (targetContext.extend region) moveContext sourceExact.nodup
        targetExact.nodup sourceBinders targetBinders binderWitness sourceCover
        targetCover sourceEnumeration targetEnumeration sourceExact targetExact
        sourceItems targetItems sourceCompiled targetCompiled)
  have transport : ∀ direction relEnv,
      ConcreteElaboration.DirectionalLocalTransport direction sourceContext
        targetContext region region context.indexRelation model named relEnv
        (sourceItems.renameRelations
          (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness))
        targetItems := by
    intro direction currentRelEnv currentSourceOuter currentTargetOuter
      currentOuterAgrees
    cases direction with
    | forward =>
        intro sourceLocal sourceDenotes
        obtain ⟨targetLocal, identityAgrees⟩ :=
          context.extended_agreement region currentSourceOuter
            currentTargetOuter currentOuterAgrees sourceLocal
        have sourceDenotesRaw : denoteItemSeq model named
            (ConcreteElaboration.extendedEnvironment sourceContext region
              currentSourceOuter sourceLocal) currentRelEnv sourceItems := by
          simpa only [identityRelationRenamingEq, ItemSeq.renameRelations_id] using
            sourceDenotes
        have endpointAgrees := extendedContext.endpoint_relation_of_coalesced
          sourceExact
          (ConcreteElaboration.extendedEnvironment sourceContext region
            currentSourceOuter sourceLocal)
          (ConcreteElaboration.extendedEnvironment targetContext region
            currentTargetOuter targetLocal)
          identityAgrees
          (sourceCoalesced currentSourceOuter sourceLocal currentRelEnv
            sourceDenotesRaw)
        exact ⟨targetLocal,
          semantic .forward _ _ currentRelEnv endpointAgrees sourceDenotes⟩
    | backward =>
        intro targetLocal targetDenotes
        obtain ⟨sourceLocal, identityAgrees⟩ :=
          context.extended_agreement_backward region currentSourceOuter
            currentTargetOuter currentOuterAgrees targetLocal
        have targetCoal := targetCoalesced currentTargetOuter targetLocal
          currentRelEnv targetDenotes
        have sourceCoal : ∀ sourceIndex targetIndex,
            (sourceContext.extend region).get sourceIndex = sourceWire →
            (sourceContext.extend region).get targetIndex = targetWire →
            ConcreteElaboration.extendedEnvironment sourceContext region
                currentSourceOuter sourceLocal sourceIndex =
              ConcreteElaboration.extendedEnvironment sourceContext region
                currentSourceOuter sourceLocal targetIndex := by
          intro sourceIndex targetIndex sourceGet targetGet
          let sourceAtTarget : Fin (targetContext.extend region).length :=
            Fin.cast (congrArg List.length extendedContext.contexts_eq) sourceIndex
          let targetAtTarget : Fin (targetContext.extend region).length :=
            Fin.cast (congrArg List.length extendedContext.contexts_eq) targetIndex
          have sourceTransported :
              (sourceContext.extend region).get sourceIndex =
                (targetContext.extend region).get sourceAtTarget := by
            have transported := List.get_of_eq extendedContext.contexts_eq sourceIndex
            simpa only [sourceAtTarget, List.get_eq_getElem, Fin.val_cast] using
              transported
          have targetTransported :
              (sourceContext.extend region).get targetIndex =
                (targetContext.extend region).get targetAtTarget := by
            have transported := List.get_of_eq extendedContext.contexts_eq targetIndex
            simpa only [targetAtTarget, List.get_eq_getElem, Fin.val_cast] using
              transported
          have sourceToTarget := identityAgrees sourceIndex sourceAtTarget (by rfl)
          have targetToTarget := identityAgrees targetIndex targetAtTarget (by rfl)
          exact sourceToTarget.trans ((targetCoal sourceAtTarget targetAtTarget
            (sourceTransported.symm.trans sourceGet)
            (targetTransported.symm.trans targetGet)).trans targetToTarget.symm)
        have endpointAgrees := extendedContext.endpoint_relation_of_coalesced
          sourceExact
          (ConcreteElaboration.extendedEnvironment sourceContext region
            currentSourceOuter sourceLocal)
          (ConcreteElaboration.extendedEnvironment targetContext region
            currentTargetOuter targetLocal)
          identityAgrees sourceCoal
        exact ⟨sourceLocal,
          semantic .backward _ _ currentRelEnv endpointAgrees targetDenotes⟩
  have forward := ConcreteElaboration.finishRegion_denote .forward sourceContext
    targetContext region region context.indexRelation model named
    (sourceItems.renameRelations
      (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness))
    targetItems (transport .forward) sourceOuter targetOuter relEnv outerAgrees
  have backward := ConcreteElaboration.finishRegion_denote .backward sourceContext
    targetContext region region context.indexRelation model named
    (sourceItems.renameRelations
      (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness))
    targetItems (transport .backward) sourceOuter targetOuter relEnv outerAgrees
  rw [identityRelationRenamingEq, ItemSeq.renameRelations_id] at forward backward
  exact ⟨forward, backward⟩

end AnchoredWireContractSoundness

end VisualProof.Rule
