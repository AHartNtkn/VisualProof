import VisualProof.Rule.Soundness.Comprehension.InstantiationFinalEnvironment
import VisualProof.Rule.Soundness.Comprehension.InstantiationDropNodeCompiler

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationTrace

/-- Endpoint ownership at a regular final node is exactly endpoint ownership
at its certified original node.  The final wire is the composite image of the
original wire; atom compaction and vacuous promotion do not change ownership
for this surviving node. -/
theorem final_endpointOccurs_reverseNode_iff
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    {raw : ConcreteDiagram}
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (finalRegion : Fin elimTrace.sourceDiagram.regionCount)
    (regular : copyTrace.FinalRegularPreimage elimTrace finalWellFormed
      finalRegion)
    (finalNode : Fin elimTrace.sourceDiagram.nodeCount)
    (nodeRegion : (elimTrace.sourceDiagram.nodes finalNode).region =
      finalRegion)
    (wire : Fin input.val.wireCount)
    (port : CPort) :
    elimTrace.sourceDiagram.EndpointOccurs
        (copyTrace.finalWireMap elimTrace wire) ⟨finalNode, port⟩ ↔
      input.val.EndpointOccurs wire
        ⟨copyTrace.reverseNodeMap elimTrace finalWellFormed finalRegion regular
          finalNode nodeRegion, port⟩ := by
  let preimage := copyTrace.finalNode_preimage_of_regular elimTrace
    finalWellFormed finalRegion regular finalNode nodeRegion
  let originalNode := copyTrace.reverseNodeMap elimTrace finalWellFormed
    finalRegion regular finalNode nodeRegion
  have originalSpec := Classical.choose_spec preimage
  have originalRegion := originalSpec.1
  let outside := node_outside_bubble_of_regular payload
    (copyTrace.reverseRegionMap elimTrace finalWellFormed finalRegion)
    (copyTrace.reverseRegionMap_spec elimTrace finalWellFormed finalRegion
      regular).1 originalNode originalRegion
  have finalNodeEq : copyTrace.finalNodeMap elimTrace originalNode outside =
      finalNode := by
    exact originalSpec.2
  change elimTrace.sourceDiagram.EndpointOccurs
      (copyTrace.finalWireMap elimTrace wire) ⟨finalNode, port⟩ ↔
    input.val.EndpointOccurs wire ⟨originalNode, port⟩
  rw [← finalNodeEq]
  unfold finalWireMap finalNodeMap
  change ⟨copyTrace.droppedNodeMap originalNode outside, port⟩ ∈
      (elimTrace.promotion.wires (copyTrace.wireMap wire)).endpoints ↔
    input.val.EndpointOccurs wire ⟨originalNode, port⟩
  rw [elimTrace.promotedWire_endpoints]
  change
    (dropInstantiationAtomsRaw result).EndpointOccurs (copyTrace.wireMap wire)
        ⟨copyTrace.droppedNodeMap originalNode outside, port⟩ ↔
      input.val.EndpointOccurs wire ⟨originalNode, port⟩
  rw [InstantiationSemantic.drop_endpointOccurs_origin_iff]
  rw [copyTrace.droppedNodeMap_origin originalNode outside]
  exact copyTrace.endpointOccurs_wireMap_nodeMap_iff wire originalNode port

/-- Resolved ports at a regular final node are related by the certified
final-to-original lexical-context relation. -/
theorem regularNode_resolvedPorts_related
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    {raw : ConcreteDiagram}
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (sourceWellFormed : elimTrace.sourceDiagram.WellFormed signature)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (sourceContext : ConcreteElaboration.WireContext
      elimTrace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input.val)
    (context : FinalContextWitness copyTrace elimTrace sourceContext
      targetContext)
    (sourceNodup : sourceContext.Nodup)
    (finalRegion : Fin elimTrace.sourceDiagram.regionCount)
    (regular : copyTrace.FinalRegularPreimage elimTrace finalWellFormed
      finalRegion)
    (finalNode : Fin elimTrace.sourceDiagram.nodeCount)
    (nodeRegion : (elimTrace.sourceDiagram.nodes finalNode).region =
      finalRegion)
    (port : CPort)
    (sourceIndex : Fin sourceContext.length)
    (targetIndex : Fin targetContext.length)
    (sourceResolved : ConcreteElaboration.resolvePort?
      elimTrace.sourceDiagram sourceContext finalNode port = some sourceIndex)
    (targetResolved : ConcreteElaboration.resolvePort? input.val targetContext
      (copyTrace.reverseNodeMap elimTrace finalWellFormed finalRegion regular
        finalNode nodeRegion) port = some targetIndex) :
    context.indexRelation.Rel sourceIndex targetIndex := by
  obtain ⟨sourceWire, sourceOccurs, sourceGet⟩ :=
    ConcreteElaboration.resolvePort?_sound sourceResolved
  obtain ⟨targetWire, targetOccurs, targetGet⟩ :=
    ConcreteElaboration.resolvePort?_sound targetResolved
  have mappedTargetOccurs : elimTrace.sourceDiagram.EndpointOccurs
      (copyTrace.finalWireMap elimTrace targetWire) ⟨finalNode, port⟩ :=
    (copyTrace.final_endpointOccurs_reverseNode_iff elimTrace finalWellFormed
      finalRegion regular finalNode nodeRegion targetWire port).2
      targetOccurs
  have wireEq : sourceWire = copyTrace.finalWireMap elimTrace targetWire :=
    ConcreteElaboration.endpoint_wire_unique
      sourceWellFormed.wire_endpoints_are_disjoint sourceOccurs
        mappedTargetOccurs
  have mappedLookup := context.sourceIndex_lookup targetIndex
  change targetContext.get targetIndex = targetWire at targetGet
  change sourceContext.lookup?
      (copyTrace.finalWireMap elimTrace (targetContext.get targetIndex)) =
        some (context.sourceIndex targetIndex) at mappedLookup
  rw [targetGet] at mappedLookup
  change context.sourceIndex targetIndex = sourceIndex
  exact (ConcreteElaboration.WireContext.lookup?_unique sourceNodup mappedLookup
    (sourceGet.trans wireEq)).symm

/-- Every retained final node compiles to an item semantically equivalent to
the item compiled from its certified original node under the reverse context
and binder maps. -/
theorem regularNode_itemSimulation
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    {raw : ConcreteDiagram}
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (sourceWellFormed : elimTrace.sourceDiagram.WellFormed signature)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (sourceContext : ConcreteElaboration.WireContext
      elimTrace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input.val)
    (context : FinalContextWitness copyTrace elimTrace sourceContext
      targetContext)
    (sourceNodup : sourceContext.Nodup)
    (sourceBinders : ConcreteElaboration.BinderContext
      elimTrace.sourceDiagram sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext input.val targetRels)
    (binderWitness : FinalBinderWitness copyTrace elimTrace finalWellFormed
      sourceBinders targetBinders)
    (finalRegion : Fin elimTrace.sourceDiagram.regionCount)
    (regular : copyTrace.FinalRegularPreimage elimTrace finalWellFormed
      finalRegion)
    (finalNode : Fin elimTrace.sourceDiagram.nodeCount)
    (nodeRegion : (elimTrace.sourceDiagram.nodes finalNode).region =
      finalRegion)
    (sourceItem : Item signature sourceContext.length sourceRels)
    (targetItem : Item signature targetContext.length targetRels)
    (sourceCompiled : ConcreteElaboration.compileNode? signature
      elimTrace.sourceDiagram sourceContext sourceBinders finalNode =
        some sourceItem)
    (targetCompiled : ConcreteElaboration.compileNode? signature input.val
      targetContext targetBinders
      (copyTrace.reverseNodeMap elimTrace finalWellFormed finalRegion regular
        finalNode nodeRegion) = some targetItem) :
    ConcreteElaboration.ItemSimulation model named direction
      context.indexRelation
      (sourceItem.renameRelations binderWitness.relationMap) targetItem := by
  apply ConcreteElaboration.compileNode?_itemSimulation_of_related_ports
    model named direction sourceContext targetContext context.indexRelation
    sourceBinders targetBinders binderWitness.relationMap finalNode
    (copyTrace.reverseNodeMap elimTrace finalWellFormed finalRegion regular
      finalNode nodeRegion)
    (copyTrace.reverseRegionMap elimTrace finalWellFormed)
    (copyTrace.reverseRegionMap elimTrace finalWellFormed)
  · have shape := copyTrace.reverse_node_shape_of_regular elimTrace
      finalWellFormed finalRegion regular finalNode nodeRegion
    cases finalShape : elimTrace.sourceDiagram.nodes finalNode <;>
      simp only [finalShape] at shape ⊢ <;> exact shape
  · intro port sourceIndex targetIndex sourceResolved targetResolved
    exact copyTrace.regularNode_resolvedPorts_related elimTrace
      sourceWellFormed finalWellFormed sourceContext targetContext
      context sourceNodup finalRegion regular finalNode nodeRegion port
      sourceIndex targetIndex sourceResolved targetResolved
  · intro region binder arity sourceRelation sourceShape sourceLookup
    exact binderWitness.bindersMapped binder arity sourceRelation sourceLookup
  · exact sourceCompiled
  · exact targetCompiled

end InstantiationTrace

end VisualProof.Rule
