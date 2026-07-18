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

end Context

end FusionSoundness

end VisualProof.Rule
