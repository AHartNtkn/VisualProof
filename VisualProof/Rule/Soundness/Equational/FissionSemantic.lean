import VisualProof.Rule.Soundness.Equational.FissionContext

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram

namespace FissionSoundness

theorem fissionRaw_otherEndpointOccurs_iff
    (input : CheckedDiagram signature)
    (selected old : Fin input.val.nodeCount)
    (different : old ≠ selected)
    (site : Fin input.val.regionCount)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount)))
    (wire : Fin input.val.wireCount) (port : CPort) :
    (fissionRaw input selected site producer residual).EndpointOccurs
        wire.castSucc { node := old.castSucc, port := port } ↔
      input.val.EndpointOccurs wire { node := old, port := port } := by
  unfold ConcreteDiagram.EndpointOccurs
  simp only [fissionRaw, Fin.lastCases_castSucc]
  constructor
  · intro member
    rcases List.mem_append.mp member with prefixPart | residualMember
    · rcases List.mem_append.mp prefixPart with retained | producerMember
      · rcases List.mem_map.mp retained with ⟨endpoint, filtered, equality⟩
        have nodeEquality := congrArg CEndpoint.node equality
        have endpointNode : endpoint.node = old := by
          apply Fin.ext
          simpa only [anchoredSplitLiftEndpoint_node, Fin.val_castSucc] using
            congrArg Fin.val nodeEquality
        have endpointPort : endpoint.port = port := by
          simpa only [anchoredSplitLiftEndpoint_port] using
            congrArg CEndpoint.port equality
        have endpointEquality : endpoint = { node := old, port := port } := by
          cases endpoint
          simp_all
        subst endpoint
        exact (List.mem_filter.mp filtered).1
      · rcases List.mem_filterMap.mp producerMember with
          ⟨producerPort, _, producerResult⟩
        split at producerResult <;> try contradiction
        have endpointEquality := Option.some.inj producerResult
        have nodeEquality := congrArg CEndpoint.node endpointEquality
        have values := congrArg Fin.val nodeEquality
        simp only [Fin.val_last, Fin.val_castSucc] at values
        omega
    · rcases List.mem_filterMap.mp residualMember with
        ⟨residualPort, _, residualResult⟩
      split at residualResult <;> try contradiction
      have endpointEquality := Option.some.inj residualResult
      have nodeEquality := congrArg CEndpoint.node endpointEquality
      have selectedEquality : selected = old := by
        apply Fin.ext
        simpa only [Fin.val_castSucc] using congrArg Fin.val nodeEquality
      exact False.elim (different selectedEquality.symm)
  · intro member
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨{ node := old, port := port }, ?_, rfl⟩
    exact List.mem_filter.mpr ⟨member,
      fissionKeepEndpoint_of_node_ne selected _ different⟩

theorem fissionRaw_otherEndpointOccurs_backward
    (input : CheckedDiagram signature)
    (selected old : Fin input.val.nodeCount)
    (different : old ≠ selected)
    (site : Fin input.val.regionCount)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount)))
    (targetWire : Fin (fissionRaw input selected site producer residual).wireCount)
    (port : CPort)
    (occurs : (fissionRaw input selected site producer residual).EndpointOccurs
      targetWire { node := old.castSucc, port := port }) :
    ∃ sourceWire : Fin input.val.wireCount,
      sourceWire.castSucc = targetWire ∧
        input.val.EndpointOccurs sourceWire { node := old, port := port } := by
  change Fin (input.val.wireCount + 1) at targetWire
  refine Fin.lastCases ?_ (fun sourceWire occurrence =>
    ⟨sourceWire, rfl,
      (fissionRaw_otherEndpointOccurs_iff input selected old different site
        producer residual sourceWire port).mp occurrence⟩) targetWire occurs
  intro freshOccurs
  unfold ConcreteDiagram.EndpointOccurs at freshOccurs
  simp only [fissionRaw, Fin.lastCases_last] at freshOccurs
  have alternatives := List.mem_cons.mp freshOccurs
  rcases alternatives with producerEndpoint | residualEndpoint
  · have nodeEquality := congrArg CEndpoint.node producerEndpoint
    have values := congrArg Fin.val nodeEquality
    simp only [Fin.val_castSucc, Fin.val_last] at values
    omega
  · rcases List.mem_filterMap.mp residualEndpoint with
      ⟨residualPort, _, present⟩
    split at present <;> try contradiction
    have endpointEquality := Option.some.inj present
    have nodeEquality := congrArg CEndpoint.node endpointEquality
    have selectedEquality : selected = old := by
      apply Fin.ext
      simpa only [Fin.val_castSucc] using congrArg Fin.val nodeEquality
    exact False.elim (different selectedEquality.symm)

theorem unchangedNode_itemSimulation
    (input : CheckedDiagram signature)
    (selected old : Fin input.val.nodeCount)
    (different : old ≠ selected)
    (site : Fin input.val.regionCount)
    (producer : Lambda.Term 0 (Fin input.val.wireCount))
    (residual : Lambda.Term 0 (Option (Fin input.val.wireCount)))
    (sourceContext : ConcreteElaboration.WireContext input.val)
    (targetContext : ConcreteElaboration.WireContext
      (fissionRaw input selected site producer residual))
    (context : ContextEmbedding input selected site producer residual
      sourceContext targetContext)
    (targetNodup : targetContext.Nodup)
    (sourceBinders : ConcreteElaboration.BinderContext input.val rels)
    (targetBinders : ConcreteElaboration.BinderContext
      (fissionRaw input selected site producer residual) rels)
    (bindersEqual : HEq sourceBinders targetBinders)
    (sourceItem : Item signature sourceContext.length rels)
    (targetItem : Item signature targetContext.length rels)
    (sourceCompiled : ConcreteElaboration.compileNode? signature input.val
      sourceContext sourceBinders old = some sourceItem)
    (targetCompiled : ConcreteElaboration.compileNode? signature
      (fissionRaw input selected site producer residual) targetContext
      targetBinders old.castSucc = some targetItem)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection) :
    ConcreteElaboration.ItemSimulation model named direction
      (ConcreteElaboration.ContextIndexRelation.forwardMap context.index)
      sourceItem targetItem := by
  cases bindersEqual
  have simulation :=
    ConcreteElaboration.compileNode?_itemSimulation_of_related_ports
      (source := input.val)
      (target := fissionRaw input selected site producer residual)
      model named direction sourceContext targetContext
      (ConcreteElaboration.ContextIndexRelation.forwardMap context.index)
      sourceBinders sourceBinders
      (ConcreteElaboration.identityRelationRenaming rels)
      (sourceNode := old)
      (targetNode := old.castSucc)
      (regionMap := id)
      (binderMap := id)
      (nodeShape := by
        cases shape : input.val.nodes old <;>
          simp [fissionRaw, different, shape])
      (portsRelated := by
        intro port sourceIndex targetIndex sourceResolved targetResolved
        obtain ⟨sourceOwner, sourceOccurs, sourceGet⟩ :=
          ConcreteElaboration.resolvePort?_sound sourceResolved
        obtain ⟨targetOwner, targetOccurs, targetGet⟩ :=
          ConcreteElaboration.resolvePort?_sound targetResolved
        obtain ⟨origin, originEquality, originOccurs⟩ :=
          fissionRaw_otherEndpointOccurs_backward input selected old different
            site producer residual targetOwner port targetOccurs
        have ownerEquality : origin = sourceOwner :=
          ConcreteElaboration.endpoint_wire_unique
            input.property.wire_endpoints_are_disjoint originOccurs sourceOccurs
        have sourceGet' : sourceContext.get sourceIndex = sourceOwner := by
          simpa only [List.get_eq_getElem] using sourceGet
        have targetGet' : targetContext.get targetIndex = targetOwner := by
          simpa only [List.get_eq_getElem] using targetGet
        change context.index sourceIndex = targetIndex
        exact (context.index_eq_of_get targetNodup sourceIndex targetIndex (by
          calc
            targetContext.get targetIndex = targetOwner := targetGet'
            _ = origin.castSucc := originEquality.symm
            _ = sourceOwner.castSucc := congrArg Fin.castSucc ownerEquality
            _ = (sourceContext.get sourceIndex).castSucc :=
              congrArg Fin.castSucc sourceGet'.symm)).symm)
      (bindersRelated := by
        intro region binder arity sourceRelation nodeShape binderLookup
        simpa [ConcreteElaboration.identityRelationRenaming] using binderLookup)
      (sourceItem := sourceItem) (targetItem := targetItem)
      sourceCompiled targetCompiled
  have relationMapEq :
      (ConcreteElaboration.identityRelationRenaming rels :
        RelationRenaming rels rels) =
      (fun {arity} (relation : Theory.RelVar rels arity) => relation) := rfl
  rw [relationMapEq, Item.renameRelations_id] at simulation
  exact simulation

end FissionSoundness

end VisualProof.Rule
