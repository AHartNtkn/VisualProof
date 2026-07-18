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

end EndpointMoveAwayContext

private theorem extendWireEnv_transport
    {D : Type} {outer sourceLocalCount targetLocalCount : Nat}
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

end AnchoredWireContractSoundness

end VisualProof.Rule
