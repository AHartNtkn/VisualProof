import VisualProof.Rule.Soundness.Equational.HeadStripSimulation

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace FusionSoundness

def mappedConsumer
    (input : CheckedDiagram signature)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer) :
    Fin (fusionNodeDomain input.val producer).count :=
  (fusionNodeDomain input.val producer).index consumer (by
    simp [fusionNodeDomain, hdistinct.symm])

def mappedNode
    (input : CheckedDiagram signature)
    (producer node : Fin input.val.nodeCount)
    (survives : node ≠ producer) :
    Fin (fusionNodeDomain input.val producer).count :=
  (fusionNodeDomain input.val producer).index node (by
    simp [fusionNodeDomain, survives])

@[simp] theorem fusionNodeDomain_origin_mappedNode
    (input : CheckedDiagram signature)
    (producer node : Fin input.val.nodeCount)
    (survives : node ≠ producer) :
    (fusionNodeDomain input.val producer).origin
        (mappedNode input producer node survives) = node := by
  exact (fusionNodeDomain input.val producer).origin_index node (by
    simp [fusionNodeDomain, survives])

@[simp] theorem fusionNodeDomain_origin_mappedConsumer
    (input : CheckedDiagram signature)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer) :
    (fusionNodeDomain input.val producer).origin
        (mappedConsumer input producer consumer hdistinct) = consumer := by
  exact (fusionNodeDomain input.val producer).origin_index consumer (by
    simp [fusionNodeDomain, hdistinct.symm])

/-- Evaluation of the serialized fusion term is simultaneous substitution at
the consumed consumer port.  This is the logical kernel used at the routed
consumer site; it deliberately states the result over the executor's global
wire maps, before compact support reindexing. -/
theorem eval_fusionTerm
    (model : Lambda.LambdaModel)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin wires)
    (consumerWire : Fin consumerPorts → Fin wires)
    (consumedPort : Fin consumerPorts)
    (environment : Fin wires → model.Carrier) :
    model.eval
        (fusionTerm producerTerm consumerTerm producerWire consumerWire
          consumedPort) environment =
      model.eval consumerTerm (fun port ↦
        if port = consumedPort then
          model.eval producerTerm (environment ∘ producerWire)
        else environment (consumerWire port)) := by
  rw [fusionTerm, model.eval_bindFree]
  apply congrArg (model.eval consumerTerm)
  funext port
  split
  · rw [model.eval_mapFree]
  · exact model.eval_port _ _

/-- Resolving all free ports records the authoritative owner of every port. -/
theorem resolveNodeFreeWires?_sound
    (input : CheckedDiagram signature)
    (node : Fin input.val.nodeCount) (ports : Nat)
    (wires : Fin ports → Fin input.val.wireCount)
    (resolved : resolveNodeFreeWires? input node ports = some wires)
    (port : Fin ports) :
    ConcreteElaboration.endpointOwner? input.val
        { node := node, port := .free port } = some (wires port) := by
  exact sequenceFin_sound resolved port

/-- Every resolved free-port owner contains the corresponding endpoint. -/
theorem resolvedFreePort_occurs
    (input : CheckedDiagram signature)
    (node : Fin input.val.nodeCount) (ports : Nat)
    (wires : Fin ports → Fin input.val.wireCount)
    (resolved : resolveNodeFreeWires? input node ports = some wires)
    (port : Fin ports) :
    input.val.EndpointOccurs (wires port)
      { node := node, port := .free port } := by
  exact ConcreteElaboration.endpointOwner?_sound
    (resolveNodeFreeWires?_sound input node ports wires resolved port)

theorem fusionEndpoints_consumer_occurs
    (input : CheckedDiagram signature)
    (wire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (consumed : Nat)
    (endpoints :
      (input.val.wires wire).endpoints = [
          { node := producer, port := CPort.output },
          { node := consumer, port := CPort.free consumed }] ∨
        (input.val.wires wire).endpoints = [
          { node := consumer, port := CPort.free consumed },
          { node := producer, port := CPort.output }]) :
    input.val.EndpointOccurs wire
      { node := consumer, port := .free consumed } := by
  rcases endpoints with forward | backward
  · simp [ConcreteDiagram.EndpointOccurs, forward]
  · simp [ConcreteDiagram.EndpointOccurs, backward]

theorem fusionEndpoints_producer_occurs
    (input : CheckedDiagram signature)
    (wire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (consumed : Nat)
    (endpoints :
      (input.val.wires wire).endpoints = [
          { node := producer, port := CPort.output },
          { node := consumer, port := CPort.free consumed }] ∨
        (input.val.wires wire).endpoints = [
          { node := consumer, port := CPort.free consumed },
          { node := producer, port := CPort.output }]) :
    input.val.EndpointOccurs wire
      { node := producer, port := .output } := by
  rcases endpoints with forward | backward
  · simp [ConcreteDiagram.EndpointOccurs, forward]
  · simp [ConcreteDiagram.EndpointOccurs, backward]

theorem consumedWire_encloses_consumer
    (input : CheckedDiagram signature)
    (wire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (consumed : Nat)
    (consumerRegion : Fin input.val.regionCount)
    (consumerPorts : Nat)
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (consumerShape : input.val.nodes consumer =
      .term consumerRegion consumerPorts consumerTerm)
    (endpoints :
      (input.val.wires wire).endpoints = [
          { node := producer, port := CPort.output },
          { node := consumer, port := CPort.free consumed }] ∨
        (input.val.wires wire).endpoints = [
          { node := consumer, port := CPort.free consumed },
          { node := producer, port := CPort.output }]) :
    input.val.Encloses (input.val.wires wire).scope consumerRegion := by
  have encloses := input.property.wire_scopes_enclose wire
    { node := consumer, port := .free consumed }
    (fusionEndpoints_consumer_occurs input wire producer consumer consumed
      endpoints)
  simpa [consumerShape] using encloses

theorem producerWire_encloses_consumer
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (consumed : Nat)
    (producerRegion consumerRegion : Fin input.val.regionCount)
    (producerPorts consumerPorts : Nat)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (producerShape : input.val.nodes producer =
      .term producerRegion producerPorts producerTerm)
    (consumerShape : input.val.nodes consumer =
      .term consumerRegion consumerPorts consumerTerm)
    (scope : producerRegion = (input.val.wires consumedWire).scope)
    (producerResolved : resolveNodeFreeWires? input producer producerPorts =
      some producerWire)
    (endpoints :
      (input.val.wires consumedWire).endpoints = [
          { node := producer, port := CPort.output },
          { node := consumer, port := CPort.free consumed }] ∨
        (input.val.wires consumedWire).endpoints = [
          { node := consumer, port := CPort.free consumed },
          { node := producer, port := CPort.output }])
    (port : Fin producerPorts) :
    input.val.Encloses (input.val.wires (producerWire port)).scope
      consumerRegion := by
  have producerEncloses := input.property.wire_scopes_enclose
    (producerWire port) { node := producer, port := .free port }
    (resolvedFreePort_occurs input producer producerPorts producerWire
      producerResolved port)
  have producerEnclosesRegion : input.val.Encloses
      (input.val.wires (producerWire port)).scope producerRegion := by
    simpa [producerShape] using producerEncloses
  have consumedEncloses := consumedWire_encloses_consumer input consumedWire
    producer consumer consumed consumerRegion consumerPorts consumerTerm
    consumerShape endpoints
  rw [scope] at producerEnclosesRegion
  exact ConcreteElaboration.checked_encloses_trans input.property
    producerEnclosesRegion consumedEncloses

theorem consumerWire_encloses_consumer
    (input : CheckedDiagram signature)
    (consumer : Fin input.val.nodeCount)
    (consumerRegion : Fin input.val.regionCount)
    (consumerPorts : Nat)
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumerShape : input.val.nodes consumer =
      .term consumerRegion consumerPorts consumerTerm)
    (consumerResolved : resolveNodeFreeWires? input consumer consumerPorts =
      some consumerWire)
    (port : Fin consumerPorts) :
    input.val.Encloses (input.val.wires (consumerWire port)).scope
      consumerRegion := by
  have encloses := input.property.wire_scopes_enclose (consumerWire port)
    { node := consumer, port := .free port }
    (resolvedFreePort_occurs input consumer consumerPorts consumerWire
      consumerResolved port)
  simpa [consumerShape] using encloses

@[simp] theorem fusionRaw_regions
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (consumerRegion : Fin input.val.regionCount)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts) :
    (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
      producerTerm consumerTerm producerWire consumerWire consumedPort).regions =
        input.val.regions := rfl

@[simp] theorem fusionRaw_root
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (consumerRegion : Fin input.val.regionCount)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts) :
    (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
      producerTerm consumerTerm producerWire consumerWire consumedPort).root =
        input.val.root := rfl

@[simp] theorem fusionRaw_wire_scope
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (consumerRegion : Fin input.val.regionCount)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts)
    (wire : Fin (fusionWireDomain input.val consumedWire).count) :
    ((fusionRaw input consumedWire producer consumer hdistinct consumerRegion
      producerTerm consumerTerm producerWire consumerWire consumedPort).wires
        wire).scope =
      (input.val.wires
        ((fusionWireDomain input.val consumedWire).origin wire)).scope :=
  rfl

@[simp] theorem fusionRaw_consumer_node
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (consumerRegion : Fin input.val.regionCount)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts) :
    (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
      producerTerm consumerTerm producerWire consumerWire consumedPort).nodes
        (mappedConsumer input producer consumer hdistinct) =
      .term consumerRegion
        (fusionTerm producerTerm consumerTerm producerWire consumerWire
          consumedPort).freeSupport.length
        (fusionTerm producerTerm consumerTerm producerWire consumerWire
          consumedPort).compact := by
  change (if (fusionNodeDomain input.val producer).origin
        (mappedConsumer input producer consumer hdistinct) = consumer then
      CNode.term consumerRegion
        (fusionTerm producerTerm consumerTerm producerWire consumerWire
          consumedPort).freeSupport.length
        (fusionTerm producerTerm consumerTerm producerWire consumerWire
          consumedPort).compact
    else input.val.nodes ((fusionNodeDomain input.val producer).origin
      (mappedConsumer input producer consumer hdistinct))) = _
  rw [fusionNodeDomain_origin_mappedConsumer]
  rw [if_pos rfl]
  rfl

theorem fusionRaw_old_node_of_ne_consumer
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer node : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (survives : node ≠ producer)
    (notConsumer : node ≠ consumer)
    (consumerRegion : Fin input.val.regionCount)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts) :
    (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
      producerTerm consumerTerm producerWire consumerWire consumedPort).nodes
        (mappedNode input producer node survives) = input.val.nodes node := by
  change (if (fusionNodeDomain input.val producer).origin
        (mappedNode input producer node survives) = consumer then
      CNode.term consumerRegion
        (fusionTerm producerTerm consumerTerm producerWire consumerWire
          consumedPort).freeSupport.length
        (fusionTerm producerTerm consumerTerm producerWire consumerWire
          consumedPort).compact
    else input.val.nodes ((fusionNodeDomain input.val producer).origin
      (mappedNode input producer node survives))) = _
  rw [fusionNodeDomain_origin_mappedNode]
  rw [if_neg notConsumer]

theorem fusionRaw_node_region
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (consumerRegion : Fin input.val.regionCount)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (consumerPorts : Nat)
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts)
    (consumerShape : input.val.nodes consumer =
      .term consumerRegion consumerPorts consumerTerm)
    (node : Fin (fusionNodeDomain input.val producer).count) :
    ((fusionRaw input consumedWire producer consumer hdistinct consumerRegion
      producerTerm consumerTerm producerWire consumerWire consumedPort).nodes
        node).region =
      (input.val.nodes
        ((fusionNodeDomain input.val producer).origin node)).region := by
  simp only [fusionRaw]
  split
  · rename_i equality
    rw [equality, consumerShape]
    rfl
  · rfl

/-- A free endpoint of the rewritten consumer can only come from the compact
support reconstruction appended by `fusionRaw`; the filtered old endpoint
prefix deliberately removes every old consumer free endpoint. -/
theorem fusionRaw_consumer_free_origin
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (consumerRegion : Fin input.val.regionCount)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts)
    (wire : Fin (fusionWireDomain input.val consumedWire).count)
    (port : Fin (fusionTerm producerTerm consumerTerm producerWire consumerWire
      consumedPort).freeSupport.length)
    (occurs :
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort
      ).EndpointOccurs wire
        { node := mappedConsumer input producer consumer hdistinct,
          port := .free port }) :
    (fusionWireDomain input.val consumedWire).origin wire =
      (fusionTerm producerTerm consumerTerm producerWire consumerWire
        consumedPort).freeSupport.get port := by
  let nodes := fusionNodeDomain input.val producer
  let wires := fusionWireDomain input.val consumedWire
  let mergedGlobal := fusionTerm producerTerm consumerTerm producerWire
    consumerWire consumedPort
  simp only [fusionRaw] at occurs
  change CEndpoint.mk (mappedConsumer input producer consumer hdistinct)
    (CPort.free port) ∈ (_ ++ _) at occurs
  rw [List.mem_append] at occurs
  rcases occurs with oldOccurs | rebuiltOccurs
  · obtain ⟨endpoint, _, endpointMapped⟩ := List.mem_filterMap.mp oldOccurs
    split at endpointMapped
    · rename_i kept
      unfold anchoredContractEndpoint? at endpointMapped
      obtain ⟨mappedNode, indexed, endpointEq⟩ :=
        Option.map_eq_some_iff.mp endpointMapped
      have mappedEq : mappedNode =
          mappedConsumer input producer consumer hdistinct :=
        congrArg CEndpoint.node endpointEq
      have originEq : nodes.origin mappedNode = endpoint.node :=
        (nodes.index?_eq_some_iff endpoint.node mappedNode).mp (by
          simpa [nodes] using indexed)
      have endpointNode : endpoint.node = consumer := by
        rw [mappedEq, fusionNodeDomain_origin_mappedConsumer] at originEq
        exact originEq.symm
      have endpointPort : endpoint.port = CPort.free port :=
        congrArg CEndpoint.port endpointEq
      rcases endpoint with ⟨endpointNodeValue, endpointPortValue⟩
      simp only at endpointNode endpointPort
      subst endpointNodeValue
      subst endpointPortValue
      rw [fusionKeepEndpoint_consumer_free] at kept
      contradiction
    · contradiction
  · obtain ⟨candidate, _, candidateMapped⟩ :=
      List.mem_filterMap.mp rebuiltOccurs
    split at candidateMapped
    · rename_i supportEq
      have endpointEq := Option.some.inj candidateMapped
      have candidateEq : candidate = port :=
        Fin.ext (CPort.free.inj (congrArg CEndpoint.port endpointEq))
      subst candidate
      simpa [wires, mergedGlobal] using supportEq.symm
    · contradiction

/-- The rewritten consumer retains its output endpoint on the survivor of the
same source wire. -/
theorem fusionRaw_consumer_output_origin_occurs
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (consumerRegion : Fin input.val.regionCount)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts)
    (wire : Fin (fusionWireDomain input.val consumedWire).count)
    (occurs :
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort
      ).EndpointOccurs wire
        { node := mappedConsumer input producer consumer hdistinct,
          port := .output }) :
    input.val.EndpointOccurs
      ((fusionWireDomain input.val consumedWire).origin wire)
      { node := consumer, port := .output } := by
  let nodes := fusionNodeDomain input.val producer
  simp only [fusionRaw] at occurs
  change CEndpoint.mk (mappedConsumer input producer consumer hdistinct)
    CPort.output ∈ (_ ++ _) at occurs
  rw [List.mem_append] at occurs
  rcases occurs with oldOccurs | rebuiltOccurs
  · obtain ⟨endpoint, endpointOccurs, endpointMapped⟩ :=
      List.mem_filterMap.mp oldOccurs
    split at endpointMapped
    · unfold anchoredContractEndpoint? at endpointMapped
      obtain ⟨mappedNode, indexed, endpointEq⟩ :=
        Option.map_eq_some_iff.mp endpointMapped
      have mappedEq : mappedNode =
          mappedConsumer input producer consumer hdistinct :=
        congrArg CEndpoint.node endpointEq
      have originEq : nodes.origin mappedNode = endpoint.node :=
        (nodes.index?_eq_some_iff endpoint.node mappedNode).mp (by
          simpa [nodes] using indexed)
      have endpointNode : endpoint.node = consumer := by
        rw [mappedEq, fusionNodeDomain_origin_mappedConsumer] at originEq
        exact originEq.symm
      have endpointPort : endpoint.port = CPort.output :=
        congrArg CEndpoint.port endpointEq
      rcases endpoint with ⟨endpointNodeValue, endpointPortValue⟩
      simp only at endpointNode endpointPort
      subst endpointNodeValue
      subst endpointPortValue
      exact endpointOccurs
    · contradiction
  · obtain ⟨port, _, portMapped⟩ := List.mem_filterMap.mp rebuiltOccurs
    split at portMapped
    · have endpointEq := Option.some.inj portMapped
      have impossible : CPort.free port = CPort.output :=
        congrArg CEndpoint.port endpointEq
      contradiction
    · contradiction

/-- Every endpoint of an unchanged survivor node comes from the same source
endpoint on the source identity represented by the compacted target wire. -/
theorem fusionRaw_mappedNode_endpoint_origin_occurs
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer node : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (survives : node ≠ producer)
    (notConsumer : node ≠ consumer)
    (consumerRegion : Fin input.val.regionCount)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts)
    (wire : Fin (fusionWireDomain input.val consumedWire).count)
    (port : CPort)
    (occurs :
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort
      ).EndpointOccurs wire
        { node := mappedNode input producer node survives, port := port }) :
    input.val.EndpointOccurs
      ((fusionWireDomain input.val consumedWire).origin wire)
      { node := node, port := port } := by
  let nodes := fusionNodeDomain input.val producer
  simp only [fusionRaw] at occurs
  change CEndpoint.mk (mappedNode input producer node survives) port ∈
    (_ ++ _) at occurs
  rw [List.mem_append] at occurs
  rcases occurs with oldOccurs | rebuiltOccurs
  · obtain ⟨endpoint, endpointOccurs, endpointMapped⟩ :=
      List.mem_filterMap.mp oldOccurs
    split at endpointMapped
    · unfold anchoredContractEndpoint? at endpointMapped
      obtain ⟨mapped, indexed, endpointEq⟩ :=
        Option.map_eq_some_iff.mp endpointMapped
      have mappedEq : mapped = mappedNode input producer node survives :=
        congrArg CEndpoint.node endpointEq
      have originEq : nodes.origin mapped = endpoint.node :=
        (nodes.index?_eq_some_iff endpoint.node mapped).mp (by
          simpa [nodes] using indexed)
      have endpointNode : endpoint.node = node := by
        rw [mappedEq, fusionNodeDomain_origin_mappedNode] at originEq
        exact originEq.symm
      have endpointPort : endpoint.port = port :=
        congrArg CEndpoint.port endpointEq
      rcases endpoint with ⟨endpointNodeValue, endpointPortValue⟩
      simp only at endpointNode endpointPort
      subst endpointNodeValue
      subst endpointPortValue
      exact endpointOccurs
    · contradiction
  · obtain ⟨candidate, _, candidateMapped⟩ :=
      List.mem_filterMap.mp rebuiltOccurs
    split at candidateMapped
    · have endpointEq := Option.some.inj candidateMapped
      have mappedEq : mappedConsumer input producer consumer hdistinct =
          mappedNode input producer node survives :=
        congrArg CEndpoint.node endpointEq
      have originEq := congrArg
        (fusionNodeDomain input.val producer).origin mappedEq
      rw [fusionNodeDomain_origin_mappedConsumer,
        fusionNodeDomain_origin_mappedNode] at originEq
      exact False.elim (notConsumer originEq.symm)
    · contradiction

theorem fusionRaw_climb
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (consumerRegion : Fin input.val.regionCount)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts)
    (steps : Nat) (region : Fin input.val.regionCount) :
    (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
      producerTerm consumerTerm producerWire consumerWire consumedPort).climb
        steps region = input.val.climb steps region := by
  induction steps generalizing region with
  | zero => rfl
  | succ steps ih =>
      simp only [ConcreteDiagram.climb]
      rw [fusionRaw_regions]
      cases kind : input.val.regions region with
      | sheet => rfl
      | cut parent => exact ih parent
      | bubble parent arity => exact ih parent

theorem fusionRaw_encloses_iff
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (consumerRegion : Fin input.val.regionCount)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts)
    (outer inner : Fin input.val.regionCount) :
    (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
      producerTerm consumerTerm producerWire consumerWire consumedPort).Encloses
        outer inner ↔ input.val.Encloses outer inner := by
  constructor <;> rintro ⟨steps, climbed⟩ <;> refine ⟨steps, ?_⟩
  · rwa [fusionRaw_climb] at climbed
  · rwa [fusionRaw_climb]

/-- The unique lexical index of a wire visible at an exact compiler context. -/
noncomputable def visibleIndex
    (diagram : ConcreteDiagram)
    (context : ConcreteElaboration.WireContext diagram)
    (region : Fin diagram.regionCount)
    (exact : context.Exact region)
    (wire : Fin diagram.wireCount)
    (visible : diagram.Encloses (diagram.wires wire).scope region) :
    Fin context.length :=
  Classical.choose (ConcreteElaboration.WireContext.lookup?_complete
    ((exact.mem_iff wire).2 visible))

@[simp] theorem visibleIndex_get
    (diagram : ConcreteDiagram)
    (context : ConcreteElaboration.WireContext diagram)
    (region : Fin diagram.regionCount)
    (exact : context.Exact region)
    (wire : Fin diagram.wireCount)
    (visible : diagram.Encloses (diagram.wires wire).scope region) :
    context.get (visibleIndex diagram context region exact wire visible) = wire :=
  ConcreteElaboration.WireContext.lookup?_sound
    (Classical.choose_spec (ConcreteElaboration.WireContext.lookup?_complete
      ((exact.mem_iff wire).2 visible)))

theorem index_eq_visibleIndex_of_get
    (diagram : ConcreteDiagram)
    (context : ConcreteElaboration.WireContext diagram)
    (region : Fin diagram.regionCount)
    (exact : context.Exact region)
    (wire : Fin diagram.wireCount)
    (visible : diagram.Encloses (diagram.wires wire).scope region)
    (index : Fin context.length)
    (indexGet : context.get index = wire) :
    index = visibleIndex diagram context region exact wire visible := by
  apply Fin.ext
  exact (List.getElem_inj exact.nodup).mp (by
    simpa only [List.get_eq_getElem] using
      indexGet.trans (visibleIndex_get diagram context region exact wire
        visible).symm)

/-- Exact fusion contexts identify every compacted target wire with its
surviving source identity.  The consumed identity intentionally has no target
index; its source value is supplied separately by the producer equation. -/
structure Context
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (consumerRegion : Fin input.val.regionCount)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts)
    (source : ConcreteElaboration.WireContext input.val)
    (target : ConcreteElaboration.WireContext
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort)) where
  sourceIndex : Fin target.length → Fin source.length
  get : ∀ index,
    source.get (sourceIndex index) =
      (fusionWireDomain input.val consumedWire).origin (target.get index)

namespace Context

noncomputable def ofExact
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (consumerRegion : Fin input.val.regionCount)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts)
    (region : Fin input.val.regionCount)
    (source : ConcreteElaboration.WireContext input.val)
    (target : ConcreteElaboration.WireContext
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort))
    (sourceExact : source.Exact region)
    (targetExact : target.Exact region) :
    Context input consumedWire producer consumer hdistinct consumerRegion
      producerTerm consumerTerm producerWire consumerWire consumedPort source
      target := by
  let domain := fusionWireDomain input.val consumedWire
  let sourceIndex : Fin target.length → Fin source.length := fun index ↦
    Classical.choose (ConcreteElaboration.WireContext.lookup?_complete
      ((sourceExact.mem_iff (domain.origin (target.get index))).2 (by
        have targetVisible := (targetExact.mem_iff (target.get index)).1
          (List.get_mem target index)
        have sourceVisible : input.val.Encloses
            (input.val.wires (domain.origin (target.get index))).scope region :=
          (fusionRaw_encloses_iff input consumedWire producer consumer hdistinct
            consumerRegion producerTerm consumerTerm producerWire consumerWire
            consumedPort _ _).mp (by
              simpa only [fusionRaw_wire_scope] using targetVisible)
        exact sourceVisible)))
  exact {
    sourceIndex := sourceIndex
    get := by
      intro index
      exact ConcreteElaboration.WireContext.lookup?_sound
        (Classical.choose_spec
          (ConcreteElaboration.WireContext.lookup?_complete
            ((sourceExact.mem_iff (domain.origin (target.get index))).2 (by
              have targetVisible := (targetExact.mem_iff (target.get index)).1
                (List.get_mem target index)
              have sourceVisible : input.val.Encloses
                  (input.val.wires (domain.origin (target.get index))).scope
                    region :=
                (fusionRaw_encloses_iff input consumedWire producer consumer
                  hdistinct consumerRegion producerTerm consumerTerm producerWire
                  consumerWire consumedPort _ _).mp (by
                    simpa only [fusionRaw_wire_scope] using targetVisible)
              exact sourceVisible))))
  }

def indexRelation
    (context : Context input consumedWire producer consumer hdistinct
      consumerRegion producerTerm consumerTerm producerWire consumerWire
      consumedPort source target) :
    ConcreteElaboration.ContextIndexRelation source.length target.length :=
  ConcreteElaboration.ContextIndexRelation.backwardMap context.sourceIndex

noncomputable def extend
    (context : Context input consumedWire producer consumer hdistinct
      consumerRegion producerTerm consumerTerm producerWire consumerWire
      consumedPort source target)
    (region : Fin input.val.regionCount)
    (sourceExact : (source.extend region).Exact region)
    (targetExact : (target.extend region).Exact region) :
    Context input consumedWire producer consumer hdistinct consumerRegion
      producerTerm consumerTerm producerWire consumerWire consumedPort
      (source.extend region) (target.extend region) :=
  ofExact input consumedWire producer consumer hdistinct consumerRegion
    producerTerm consumerTerm producerWire consumerWire consumedPort region
    (source.extend region) (target.extend region) sourceExact targetExact

theorem sourceIndex_eq_of_get
    (context : Context input consumedWire producer consumer hdistinct
      consumerRegion producerTerm consumerTerm producerWire consumerWire
      consumedPort source target)
    (sourceNodup : source.Nodup)
    (targetIndex : Fin target.length)
    (sourceIndex : Fin source.length)
    (same : source.get sourceIndex =
      (fusionWireDomain input.val consumedWire).origin
        (target.get targetIndex)) :
    context.sourceIndex targetIndex = sourceIndex := by
  apply Fin.ext
  exact (List.getElem_inj sourceNodup).mp (by
    simpa only [List.get_eq_getElem] using
      (context.get targetIndex).trans same.symm)

end Context

/-- At the consumer node, the producer equation turns the executor's concrete
term rewrite into the one-point substitution law.  All wire values are read
through exact compiler contexts, so repeated wire aliases in the syntax are
preserved rather than assumed injective. -/
theorem consumerItem_denote_iff
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (producerRegion consumerRegion : Fin input.val.regionCount)
    (producerPorts consumerPorts : Nat)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts)
    (producerShape : input.val.nodes producer =
      .term producerRegion producerPorts producerTerm)
    (consumerShape : input.val.nodes consumer =
      .term consumerRegion consumerPorts consumerTerm)
    (scope : producerRegion = (input.val.wires consumedWire).scope)
    (producerResolved : resolveNodeFreeWires? input producer producerPorts =
      some producerWire)
    (consumerResolved : resolveNodeFreeWires? input consumer consumerPorts =
      some consumerWire)
    (endpoints :
      (input.val.wires consumedWire).endpoints = [
          { node := producer, port := CPort.output },
          { node := consumer, port := CPort.free consumedPort.val }] ∨
        (input.val.wires consumedWire).endpoints = [
          { node := consumer, port := CPort.free consumedPort.val },
          { node := producer, port := CPort.output }])
    (targetWellFormed :
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort
      ).WellFormed signature)
    (sourceContext : ConcreteElaboration.WireContext input.val)
    (targetContext : ConcreteElaboration.WireContext
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort))
    (sourceExact : sourceContext.Exact consumerRegion)
    (targetExact : targetContext.Exact consumerRegion)
    (context : Context input consumedWire producer consumer hdistinct
      consumerRegion producerTerm consumerTerm producerWire consumerWire
      consumedPort sourceContext targetContext)
    (sourceBinders : ConcreteElaboration.BinderContext input.val rels)
    (targetBinders : ConcreteElaboration.BinderContext
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort) rels)
    (sourceItem : Item signature sourceContext.length rels)
    (targetItem : Item signature targetContext.length rels)
    (sourceCompiled : ConcreteElaboration.compileNode? signature input.val
      sourceContext sourceBinders consumer = some sourceItem)
    (targetCompiled : ConcreteElaboration.compileNode? signature
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort)
      targetContext targetBinders
      (mappedConsumer input producer consumer hdistinct) = some targetItem)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceEnv : Fin sourceContext.length → model.Carrier)
    (targetEnv : Fin targetContext.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (agrees : (context.indexRelation).EnvironmentsAgree sourceEnv targetEnv)
    (consumedValue :
      sourceEnv (visibleIndex input.val sourceContext consumerRegion sourceExact
        consumedWire (consumedWire_encloses_consumer input consumedWire producer
          consumer consumedPort.val consumerRegion consumerPorts consumerTerm
          consumerShape endpoints)) =
        model.eval producerTerm (fun port ↦
          sourceEnv (visibleIndex input.val sourceContext consumerRegion
            sourceExact (producerWire port)
            (producerWire_encloses_consumer input consumedWire producer consumer
              consumedPort.val producerRegion consumerRegion producerPorts
              consumerPorts producerTerm consumerTerm producerWire producerShape
              consumerShape scope producerResolved endpoints port)))) :
    denoteItem model named sourceEnv relEnv sourceItem ↔
      denoteItem model named targetEnv relEnv targetItem := by
  let mergedGlobal := fusionTerm producerTerm consumerTerm producerWire
    consumerWire consumedPort
  let consumedVisible := consumedWire_encloses_consumer input consumedWire
    producer consumer consumedPort.val consumerRegion consumerPorts consumerTerm
    consumerShape endpoints
  let consumedIndex := visibleIndex input.val sourceContext consumerRegion
    sourceExact consumedWire consumedVisible
  let fallback := sourceEnv consumedIndex
  let global : Fin input.val.wireCount → model.Carrier := fun wire ↦
    if visible : input.val.Encloses (input.val.wires wire).scope consumerRegion then
      sourceEnv (visibleIndex input.val sourceContext consumerRegion sourceExact
        wire visible)
    else fallback
  have global_visible : ∀ (wire : Fin input.val.wireCount)
      (visible : input.val.Encloses (input.val.wires wire).scope consumerRegion),
      global wire = sourceEnv (visibleIndex input.val sourceContext
        consumerRegion sourceExact wire visible) := by
    intro wire visible
    simp [global, visible]
  have consumerWireConsumed : consumerWire consumedPort = consumedWire := by
    have resolvedOccurs := resolvedFreePort_occurs input consumer consumerPorts
      consumerWire consumerResolved consumedPort
    exact ConcreteElaboration.endpoint_wire_unique
      input.property.wire_endpoints_are_disjoint resolvedOccurs
        (fusionEndpoints_consumer_occurs input consumedWire producer consumer
          consumedPort.val endpoints)
  have producerEval : model.eval producerTerm (global ∘ producerWire) =
      sourceEnv consumedIndex := by
    rw [show sourceEnv consumedIndex = model.eval producerTerm (fun port ↦
        sourceEnv (visibleIndex input.val sourceContext consumerRegion sourceExact
          (producerWire port)
          (producerWire_encloses_consumer input consumedWire producer consumer
            consumedPort.val producerRegion consumerRegion producerPorts
            consumerPorts producerTerm consumerTerm producerWire producerShape
            consumerShape scope producerResolved endpoints port))) by
      simpa [consumedIndex, consumedVisible] using consumedValue]
    apply congrArg (model.eval producerTerm)
    funext port
    exact global_visible (producerWire port)
      (producerWire_encloses_consumer input consumedWire producer consumer
        consumedPort.val producerRegion consumerRegion producerPorts consumerPorts
        producerTerm consumerTerm producerWire producerShape consumerShape scope
        producerResolved endpoints port)
  have fusedEval : model.eval mergedGlobal global =
      model.eval consumerTerm (global ∘ consumerWire) := by
    rw [show mergedGlobal = fusionTerm producerTerm consumerTerm producerWire
      consumerWire consumedPort by rfl, eval_fusionTerm]
    apply congrArg (model.eval consumerTerm)
    funext port
    by_cases selected : port = consumedPort
    · subst port
      rw [if_pos rfl, producerEval, Function.comp_apply, consumerWireConsumed]
      exact (global_visible consumedWire consumedVisible).symm
    · rw [if_neg selected]
      rfl
  unfold ConcreteElaboration.compileNode? at sourceCompiled targetCompiled
  rw [consumerShape] at sourceCompiled
  rw [fusionRaw_consumer_node] at targetCompiled
  cases sourceOutputResult : ConcreteElaboration.resolvePort? input.val
      sourceContext consumer .output with
  | none => simp [sourceOutputResult] at sourceCompiled
  | some sourceOutput =>
    cases sourceFreeResult : ConcreteElaboration.resolvePorts? input.val
        sourceContext consumer consumerPorts (fun port ↦ .free port) with
    | none => simp [sourceOutputResult, sourceFreeResult] at sourceCompiled
    | some sourceFree =>
      simp [sourceOutputResult, sourceFreeResult] at sourceCompiled
      subst sourceItem
      cases targetOutputResult : ConcreteElaboration.resolvePort?
          (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
            producerTerm consumerTerm producerWire consumerWire consumedPort)
          targetContext (mappedConsumer input producer consumer hdistinct)
          .output with
      | none => simp [targetOutputResult] at targetCompiled
      | some targetOutput =>
        cases targetFreeResult : ConcreteElaboration.resolvePorts?
            (fusionRaw input consumedWire producer consumer hdistinct
              consumerRegion producerTerm consumerTerm producerWire consumerWire
              consumedPort) targetContext
            (mappedConsumer input producer consumer hdistinct)
            mergedGlobal.freeSupport.length (fun port ↦ .free port) with
        | none => simp [mergedGlobal, targetOutputResult, targetFreeResult]
            at targetCompiled
        | some targetFree =>
          simp [mergedGlobal, targetOutputResult, targetFreeResult]
            at targetCompiled
          subst targetItem
          have sourceFreeEnv : sourceEnv ∘ sourceFree = global ∘ consumerWire := by
            funext port
            have resolvedPort := sequenceFin_sound sourceFreeResult port
            obtain ⟨owner, ownerOccurs, ownerGet⟩ :=
              ConcreteElaboration.resolvePort?_sound resolvedPort
            have ownerEq : owner = consumerWire port :=
              ConcreteElaboration.endpoint_wire_unique
                input.property.wire_endpoints_are_disjoint ownerOccurs
                (resolvedFreePort_occurs input consumer consumerPorts consumerWire
                  consumerResolved port)
            have visible := consumerWire_encloses_consumer input consumer
              consumerRegion consumerPorts consumerTerm consumerWire consumerShape
              consumerResolved port
            have indexEq := index_eq_visibleIndex_of_get input.val sourceContext
              consumerRegion sourceExact (consumerWire port) visible
              (sourceFree port) (ownerGet.trans ownerEq)
            simp only [Function.comp_apply, indexEq]
            exact (global_visible (consumerWire port) visible).symm
          have targetFreeEnv : targetEnv ∘ targetFree =
              global ∘ mergedGlobal.freeSupport.get := by
            funext port
            have resolvedPort := sequenceFin_sound targetFreeResult port
            obtain ⟨owner, ownerOccurs, ownerGet⟩ :=
              ConcreteElaboration.resolvePort?_sound resolvedPort
            have originEq := fusionRaw_consumer_free_origin input consumedWire
              producer consumer hdistinct consumerRegion producerTerm consumerTerm
              producerWire consumerWire consumedPort owner port ownerOccurs
            have sourceGet : sourceContext.get
                (context.sourceIndex (targetFree port)) =
                  mergedGlobal.freeSupport.get port := by
              have ownerGet' : targetContext.get (targetFree port) = owner := by
                simpa only [List.get_eq_getElem] using ownerGet
              rw [context.get, ownerGet', originEq]
            have targetOwnerVisible := targetWellFormed.wire_scopes_enclose owner
              { node := mappedConsumer input producer consumer hdistinct,
                port := .free port } ownerOccurs
            have sourceVisible : input.val.Encloses
                (input.val.wires (mergedGlobal.freeSupport.get port)).scope
                  consumerRegion :=
              (fusionRaw_encloses_iff input consumedWire producer consumer
                hdistinct consumerRegion producerTerm consumerTerm producerWire
                consumerWire consumedPort _ _).mp (by
                  simpa only [fusionRaw_wire_scope, originEq,
                    fusionRaw_consumer_node, CNode.region] using targetOwnerVisible)
            have sourceIndexEq := index_eq_visibleIndex_of_get input.val
              sourceContext consumerRegion sourceExact
              (mergedGlobal.freeSupport.get port) sourceVisible
              (context.sourceIndex (targetFree port)) sourceGet
            have envAgrees : sourceEnv (context.sourceIndex (targetFree port)) =
                targetEnv (targetFree port) := by
              exact agrees _ _ rfl
            simp only [Function.comp_apply]
            rw [← envAgrees, sourceIndexEq]
            exact (global_visible (mergedGlobal.freeSupport.get port)
              sourceVisible).symm
          obtain ⟨sourceOwner, sourceOwnerOccurs, sourceOwnerGet⟩ :=
            ConcreteElaboration.resolvePort?_sound sourceOutputResult
          obtain ⟨targetOwner, targetOwnerOccurs, targetOwnerGet⟩ :=
            ConcreteElaboration.resolvePort?_sound targetOutputResult
          have targetOriginOccurs := fusionRaw_consumer_output_origin_occurs
            input consumedWire producer consumer hdistinct consumerRegion
            producerTerm consumerTerm producerWire consumerWire consumedPort
            targetOwner targetOwnerOccurs
          have outputOwnerEq :
              (fusionWireDomain input.val consumedWire).origin targetOwner =
                sourceOwner :=
            ConcreteElaboration.endpoint_wire_unique
              input.property.wire_endpoints_are_disjoint targetOriginOccurs
                sourceOwnerOccurs
          have mappedOutputGet : sourceContext.get
              (context.sourceIndex targetOutput) = sourceOwner := by
            have targetOwnerGet' : targetContext.get targetOutput =
                targetOwner := by
              simpa only [List.get_eq_getElem] using targetOwnerGet
            rw [context.get, targetOwnerGet', outputOwnerEq]
          have sourceOutputEq : sourceOutput = context.sourceIndex targetOutput :=
            index_eq_visibleIndex_of_get input.val sourceContext consumerRegion
              sourceExact sourceOwner (by
                have encloses := input.property.wire_scopes_enclose sourceOwner
                  { node := consumer, port := .output } sourceOwnerOccurs
                simpa [consumerShape] using encloses)
              sourceOutput sourceOwnerGet |>.trans
                (index_eq_visibleIndex_of_get input.val sourceContext
                  consumerRegion sourceExact sourceOwner (by
                    have encloses := input.property.wire_scopes_enclose sourceOwner
                      { node := consumer, port := .output } sourceOwnerOccurs
                    simpa [consumerShape] using encloses)
                  (context.sourceIndex targetOutput) mappedOutputGet).symm
          have outputEnv : sourceEnv sourceOutput = targetEnv targetOutput := by
            rw [sourceOutputEq]
            exact agrees _ _ rfl
          simp only [denoteItem_equation]
          rw [model.eval_mapFree, model.eval_mapFree, sourceFreeEnv,
            targetFreeEnv]
          rw [VisualProof.Rule.LambdaModel.eval_compact model mergedGlobal global,
            fusedEval, outputEnv]

/-- Every node other than the deleted producer and rewritten consumer is
compiled through survivor compaction by the exact context relation. -/
theorem unchangedNode_itemSimulation
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer node : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (survives : node ≠ producer)
    (notConsumer : node ≠ consumer)
    (consumerRegion : Fin input.val.regionCount)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts)
    (sourceContext : ConcreteElaboration.WireContext input.val)
    (targetContext : ConcreteElaboration.WireContext
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort))
    (context : Context input consumedWire producer consumer hdistinct
      consumerRegion producerTerm consumerTerm producerWire consumerWire
      consumedPort sourceContext targetContext)
    (sourceExact : sourceContext.Nodup)
    (binders : ConcreteElaboration.BinderContext input.val rels)
    (sourceItem : Item signature sourceContext.length rels)
    (targetItem : Item signature targetContext.length rels)
    (sourceCompiled : ConcreteElaboration.compileNode? signature input.val
      sourceContext binders node = some sourceItem)
    (targetCompiled : ConcreteElaboration.compileNode? signature
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort)
      targetContext binders (mappedNode input producer node survives) =
        some targetItem)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection) :
    ConcreteElaboration.ItemSimulation model named direction
      context.indexRelation sourceItem targetItem := by
  have simulation :=
    ConcreteElaboration.compileNode?_itemSimulation_of_related_ports
      (source := input.val)
      (target := fusionRaw input consumedWire producer consumer hdistinct
        consumerRegion producerTerm consumerTerm producerWire consumerWire
        consumedPort)
      model named direction sourceContext targetContext context.indexRelation
      binders binders (ConcreteElaboration.identityRelationRenaming rels)
      node (mappedNode input producer node survives) id id
      (by
        rw [fusionRaw_old_node_of_ne_consumer input consumedWire producer
          consumer node hdistinct survives notConsumer consumerRegion producerTerm
          consumerTerm producerWire consumerWire consumedPort]
        cases input.val.nodes node <;> rfl)
      (by
        intro port sourceIndex targetIndex sourceResolved targetResolved
        obtain ⟨sourceOwner, sourceOccurs, sourceGet⟩ :=
          ConcreteElaboration.resolvePort?_sound sourceResolved
        obtain ⟨targetOwner, targetOccurs, targetGet⟩ :=
          ConcreteElaboration.resolvePort?_sound targetResolved
        have originOccurs := fusionRaw_mappedNode_endpoint_origin_occurs input
          consumedWire producer consumer node hdistinct survives notConsumer
          consumerRegion producerTerm consumerTerm producerWire consumerWire
          consumedPort targetOwner port targetOccurs
        have ownerEq : (fusionWireDomain input.val consumedWire).origin
            targetOwner = sourceOwner :=
          ConcreteElaboration.endpoint_wire_unique
            input.property.wire_endpoints_are_disjoint originOccurs sourceOccurs
        have targetGet' : targetContext.get targetIndex = targetOwner := by
          simpa only [List.get_eq_getElem] using targetGet
        have sourceGet' : sourceContext.get sourceIndex = sourceOwner := by
          simpa only [List.get_eq_getElem] using sourceGet
        have mappedGet : sourceContext.get (context.sourceIndex targetIndex) =
            sourceOwner := by
          rw [context.get, targetGet', ownerEq]
        change context.sourceIndex targetIndex = sourceIndex
        apply Fin.ext
        exact (List.getElem_inj sourceExact).mp (by
          simpa only [List.get_eq_getElem] using mappedGet.trans sourceGet'.symm))
      (by
        intro region binder arity sourceRelation nodeShape binderLookup
        simpa [ConcreteElaboration.identityRelationRenaming] using binderLookup)
      sourceItem targetItem sourceCompiled targetCompiled
  have relationMapEq :
      (ConcreteElaboration.identityRelationRenaming rels :
        RelationRenaming rels rels) =
      (fun {arity} (relation : RelVar rels arity) ↦ relation) := rfl
  rw [relationMapEq, Item.renameRelations_id] at simulation
  exact simulation

end FusionSoundness

end VisualProof.Rule
