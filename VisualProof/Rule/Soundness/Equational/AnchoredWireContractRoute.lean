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

end AnchoredWireContractSoundness

end VisualProof.Rule
