import VisualProof.Diagram.Concrete.Elaboration.Simulation
import VisualProof.Rule.Soundness.Comprehension.AbstractionBinder

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

namespace AbstractionRawTrace

/-- The endpoints contributed by a surviving frame wire are exactly the
surviving original endpoints, embedded before the fresh occurrence atoms. -/
theorem targetNode_endpoint_origin_occurs
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (sourceNode : Fin input.val.nodeCount)
    (nodeSurvives : trace.domains.nodes.survives sourceNode = true)
    (targetWire : Fin trace.diagram.wireCount)
    (port : CPort)
    (occurs : trace.diagram.EndpointOccurs targetWire
      { node := trace.targetNode sourceNode nodeSurvives, port }) :
    input.val.EndpointOccurs (trace.domains.wires.origin targetWire)
      { node := sourceNode, port } := by
  let originalWire := trace.domains.wires.origin targetWire
  have wireSurvives : trace.domains.wires.survives originalWire = true :=
    trace.domains.wires.origin_survives targetWire
  have wireResult := trace.abstractWire?_targetWire originalWire wireSurvives
  rw [trace.domains.regions.index?_index _
    (trace.wireScope_survives originalWire wireSurvives)] at wireResult
  have wireEq := Option.some.inj wireResult
  have endpointsEq := congrArg CWire.endpoints wireEq
  rw [trace.targetWire_origin_index targetWire] at endpointsEq
  unfold ConcreteDiagram.EndpointOccurs at occurs ⊢
  rw [← endpointsEq] at occurs
  rcases List.mem_append.mp occurs with frameOccurs | atomOccurs
  · rw [abstractFrameEndpoints, trace.domains.wires.origin_index]
      at frameOccurs
    obtain ⟨original, originalOccurs, mappedResult⟩ :=
      List.mem_filterMap.mp frameOccurs
    cases reindexed : trace.domains.nodes.reindexEndpoint? original with
    | none => simp [reindexed] at mappedResult
    | some mapped =>
      simp only [reindexed, Option.map_some] at mappedResult
      have mappedEq := Option.some.inj mappedResult
      obtain ⟨compact, indexed, mappedShape⟩ :=
        (trace.domains.nodes.reindexEndpoint?_eq_some_iff original mapped).1
          reindexed
      have mappedNodeEq : mapped.node =
          trace.domains.nodes.index sourceNode nodeSurvives := by
        apply Fin.ext
        simpa [targetNode] using congrArg (fun endpoint => endpoint.node.val)
          mappedEq
      have compactEq : compact =
          trace.domains.nodes.index sourceNode nodeSurvives := by
        rw [← mappedNodeEq]
        exact congrArg CEndpoint.node mappedShape |>.symm
      have originalNodeEq : original.node = sourceNode := by
        have originEq :=
          (trace.domains.nodes.index?_eq_some_iff original.node compact).1
            indexed
        calc
          original.node = trace.domains.nodes.origin compact := originEq.symm
          _ = trace.domains.nodes.origin
              (trace.domains.nodes.index sourceNode nodeSurvives) :=
            congrArg trace.domains.nodes.origin compactEq
          _ = sourceNode := trace.domains.nodes.origin_index _ _
      have originalPortEq : original.port = port := by
        have mappedPortEq := congrArg CEndpoint.port mappedEq
        have sourcePortEq := congrArg CEndpoint.port mappedShape
        exact sourcePortEq.symm.trans mappedPortEq
      have originalEq : original =
          ({ node := sourceNode, port } : CEndpoint input.val.nodeCount) := by
        cases original
        simp_all
      simpa [originalWire, originalEq] using originalOccurs
  · rw [abstractAtomEndpoints, trace.domains.wires.origin_index]
      at atomOccurs
    obtain ⟨occurrenceIndex, _, atomOccurs⟩ :=
      List.mem_flatMap.mp atomOccurs
    obtain ⟨argumentIndex, _, atomResult⟩ :=
      List.mem_filterMap.mp atomOccurs
    split at atomResult <;> try contradiction
    have nodeEq := congrArg CEndpoint.node (Option.some.inj atomResult)
    change Fin.natAdd trace.domains.nodes.count occurrenceIndex =
      Fin.castAdd occurrences.length
        (trace.domains.nodes.index sourceNode nodeSurvives) at nodeEq
    have valueEq := congrArg (fun value : Fin
        (trace.domains.nodes.count + occurrences.length) => value.val) nodeEq
    simp only [Fin.val_natAdd, Fin.val_castAdd] at valueEq
    omega

/-- Every node directly owned by a regular frame region compiles through the
exact survivor context and binder maps. -/
theorem regularNode_itemSimulation
    (trace : AbstractionRawTrace input wrap comprehension occurrences raw)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (sourceContext : ConcreteElaboration.WireContext input.val)
    (targetContext : ConcreteElaboration.WireContext trace.diagram)
    (context : ContextWitness trace sourceContext targetContext)
    (sourceNodup : sourceContext.Nodup)
    (sourceBinders : ConcreteElaboration.BinderContext input.val sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext trace.diagram targetRels)
    (binderWitness : BinderWitness trace sourceBinders targetBinders)
    (parent : Fin input.val.regionCount)
    (regular : trace.FrameRegular parent)
    (sourceNode : Fin input.val.nodeCount)
    (nodeRegion : (input.val.nodes sourceNode).region = parent)
    (sourceItem : Item signature sourceContext.length sourceRels)
    (targetItem : Item signature targetContext.length targetRels)
    (sourceCompiled : ConcreteElaboration.compileNode? signature input.val
      sourceContext sourceBinders sourceNode = some sourceItem)
    (targetCompiled : ConcreteElaboration.compileNode? signature trace.diagram
      targetContext targetBinders
      (trace.targetNode sourceNode
        (trace.node_survives_of_regular parent regular sourceNode nodeRegion)) =
        some targetItem) :
    ConcreteElaboration.ItemSimulation model named direction
      context.indexRelation
      (sourceItem.renameRelations binderWitness.relationMap) targetItem := by
  let nodeSurvives :=
    trace.node_survives_of_regular parent regular sourceNode nodeRegion
  apply ConcreteElaboration.compileNode?_itemSimulation_of_related_ports
    model named direction sourceContext targetContext context.indexRelation
    sourceBinders targetBinders binderWitness.relationMap sourceNode
    (trace.targetNode sourceNode nodeSurvives) trace.regionMap trace.regionMap
  · have shape :=
      trace.node_shape_of_regular parent regular sourceNode nodeRegion
        nodeSurvives
    cases sourceShape : input.val.nodes sourceNode <;>
      simp only [sourceShape] at shape ⊢ <;> exact shape
  · intro port sourceIndex targetIndex sourceResolved targetResolved
    obtain ⟨sourceWire, sourceOccurs, sourceGet⟩ :=
      ConcreteElaboration.resolvePort?_sound sourceResolved
    obtain ⟨targetWire, targetOccurs, targetGet⟩ :=
      ConcreteElaboration.resolvePort?_sound targetResolved
    have originOccurs := trace.targetNode_endpoint_origin_occurs sourceNode
      nodeSurvives targetWire port targetOccurs
    have wireEq : trace.domains.wires.origin targetWire = sourceWire :=
      ConcreteElaboration.endpoint_wire_unique
        input.property.wire_endpoints_are_disjoint originOccurs sourceOccurs
    have targetGet' : targetContext.get targetIndex = targetWire := by
      simpa only [List.get_eq_getElem] using targetGet
    have sourceGet' : sourceContext.get sourceIndex = sourceWire := by
      simpa only [List.get_eq_getElem] using sourceGet
    have mappedGet : sourceContext.get (context.sourceIndex targetIndex) =
        sourceWire := by
      rw [context.sourceIndex_get, targetGet', wireEq]
    change context.sourceIndex targetIndex = sourceIndex
    apply Fin.ext
    exact (List.getElem_inj sourceNodup).mp (by
      simpa only [List.get_eq_getElem] using mappedGet.trans sourceGet'.symm)
  · intro owner binder arity sourceRelation sourceShape sourceLookup
    have binderSurvives := trace.atomBinder_survives sourceNode nodeSurvives
      owner binder sourceShape
    rw [trace.regionMap_of_survives binder binderSurvives]
    exact binderWitness.bindersMapped binder binderSurvives arity
      sourceRelation sourceLookup
  · exact sourceCompiled
  · exact targetCompiled

end AbstractionRawTrace

end VisualProof.Rule
