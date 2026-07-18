import VisualProof.Rule.Soundness.Equational.FusionSemantic

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace FusionSoundness

private theorem filterFin_survivor_origin
    (domain : SurvivorDomain size)
    (sourceP : Fin size → Bool)
    (targetP : domain.Carrier → Bool)
    (predicateEq : ∀ index, targetP index = sourceP (domain.origin index))
    (subset : ∀ original, sourceP original = true →
      domain.survives original = true) :
    (filterFin targetP).map domain.origin = filterFin sourceP := by
  have enumerationEq :
      (allFin domain.count).map domain.origin = domain.enumeration := by
    rw [allFin_eq_finRange, List.finRange, List.map_ofFn]
    change List.ofFn (fun index ↦ domain.enumeration.get index) =
      domain.enumeration
    exact List.ofFn_getElem
  unfold filterFin
  have filterEq :
      List.filter targetP (allFin domain.count) =
        List.filter (sourceP ∘ domain.origin) (allFin domain.count) := by
    apply congrArg (fun predicate ↦
      List.filter predicate (allFin domain.count))
    funext index
    exact predicateEq index
  rw [filterEq, ← List.filter_map, enumerationEq]
  change List.filter sourceP
      (List.filter domain.survives (allFin size)) =
    List.filter sourceP (allFin size)
  rw [List.filter_filter]
  apply congrArg (fun predicate ↦ List.filter predicate (allFin size))
  funext original
  cases selected : sourceP original with
  | false => simp [selected]
  | true => simp [selected, subset original selected]

/-- Total occurrence map used below the producer site.  The producer branch
is an unreachable placeholder whenever the current region differs from the
producer region; retaining a total function lets the authoritative list
compiler's pointwise lifting theorem apply directly. -/
def mapOccurrence
    (input : CheckedDiagram signature)
    (producer : Fin input.val.nodeCount) :
    ConcreteElaboration.LocalOccurrence input.val.regionCount input.val.nodeCount →
      ConcreteElaboration.LocalOccurrence input.val.regionCount
        (fusionNodeDomain input.val producer).count
  | .node node =>
      if survives : node ≠ producer then
        .node (mappedNode input producer node survives)
      else .child input.val.root
  | .child region => .child region

@[simp] theorem mapOccurrence_node
    (input : CheckedDiagram signature)
    (producer node : Fin input.val.nodeCount)
    (survives : node ≠ producer) :
    mapOccurrence input producer (.node node) =
      .node (mappedNode input producer node survives) := by
  simp [mapOccurrence, survives]

@[simp] theorem mapOccurrence_child
    (input : CheckedDiagram signature)
    (producer : Fin input.val.nodeCount)
    (region : Fin input.val.regionCount) :
    mapOccurrence input producer (.child region) = .child region := rfl

@[simp] theorem mappedNode_consumer
    (input : CheckedDiagram signature)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer) :
    mappedNode input producer consumer hdistinct.symm =
      mappedConsumer input producer consumer hdistinct := by
  rfl

/-- Outside the producer's own region, stable node compaction and unchanged
region carriers map the compiler's complete ordered local occurrence list
exactly. -/
theorem fusionRaw_localOccurrences_map_of_ne
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
    (region : Fin input.val.regionCount)
    (different : region ≠ producerRegion) :
    ConcreteElaboration.localOccurrences
        (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
          producerTerm consumerTerm producerWire consumerWire consumedPort)
        region =
      (ConcreteElaboration.localOccurrences input.val region).map
        (mapOccurrence input producer) := by
  let domain := fusionNodeDomain input.val producer
  let sourceP : Fin input.val.nodeCount → Bool := fun node ↦
    decide ((input.val.nodes node).region = region)
  let targetP : Fin domain.count → Bool := fun node ↦
    decide (((fusionRaw input consumedWire producer consumer hdistinct
      consumerRegion producerTerm consumerTerm producerWire consumerWire
      consumedPort).nodes node).region = region)
  have predicateEq : ∀ node, targetP node = sourceP (domain.origin node) := by
    intro node
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, targetP, sourceP]
    rw [fusionRaw_node_region input consumedWire producer consumer hdistinct
      consumerRegion producerTerm consumerPorts consumerTerm producerWire
      consumerWire consumedPort consumerShape]
    rfl
  have subset : ∀ node, sourceP node = true → domain.survives node = true := by
    intro node selected
    have nodeRegion : (input.val.nodes node).region = region := by
      simpa [sourceP] using selected
    have nodeNe : node ≠ producer := by
      intro equality
      subst node
      rw [producerShape] at nodeRegion
      exact different nodeRegion.symm
    simp [domain, fusionNodeDomain, nodeNe]
  have origins := filterFin_survivor_origin domain sourceP targetP predicateEq
    subset
  have mappedOrigins :
      (filterFin sourceP).map (mapOccurrence input producer ∘
        ConcreteElaboration.LocalOccurrence.node) =
      (filterFin targetP).map ConcreteElaboration.LocalOccurrence.node := by
    rw [← origins, List.map_map]
    apply List.map_congr_left
    intro targetNode member
    change mapOccurrence input producer (.node (domain.origin targetNode)) =
      .node targetNode
    rw [mapOccurrence_node input producer (domain.origin targetNode) (by
      have survives := domain.origin_survives targetNode
      simpa [domain, fusionNodeDomain] using survives)]
    congr 1
    exact domain.index_origin targetNode
  let children := filterFin fun child : Fin input.val.regionCount ↦
    decide ((input.val.regions child).parent? = some region)
  unfold ConcreteElaboration.localOccurrences
  change (filterFin targetP).map
      (ConcreteElaboration.LocalOccurrence.node
        (regions := input.val.regionCount)) ++
      children.map (ConcreteElaboration.LocalOccurrence.child
        (nodes := domain.count)) =
    (((filterFin sourceP).map
        (ConcreteElaboration.LocalOccurrence.node
          (regions := input.val.regionCount))) ++
      children.map (ConcreteElaboration.LocalOccurrence.child
        (nodes := input.val.nodeCount))).map (mapOccurrence input producer)
  rw [List.map_append, List.map_map, mappedOrigins, List.map_map]
  apply congrArg (fun tail ↦
    (filterFin targetP).map
      (ConcreteElaboration.LocalOccurrence.node
        (regions := input.val.regionCount)) ++ tail)
  apply List.map_congr_left
  intro child _
  rfl

/-- Away from the consumed wire's scope, stable wire compaction maps the
target's complete local-wire enumeration exactly onto the source enumeration.
This is the local-context counterpart of interface provenance. -/
theorem fusionRaw_exactScopeWires_map_of_ne
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (producerRegion consumerRegion : Fin input.val.regionCount)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts)
    (scope : producerRegion = (input.val.wires consumedWire).scope)
    (region : Fin input.val.regionCount)
    (different : region ≠ producerRegion) :
    (ConcreteElaboration.exactScopeWires
        (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
          producerTerm consumerTerm producerWire consumerWire consumedPort)
        region).map (fusionWireDomain input.val consumedWire).origin =
      ConcreteElaboration.exactScopeWires input.val region := by
  let domain := fusionWireDomain input.val consumedWire
  let sourceP : Fin input.val.wireCount → Bool := fun wire ↦
    decide ((input.val.wires wire).scope = region)
  let targetP : Fin domain.count → Bool := fun wire ↦
    decide (((fusionRaw input consumedWire producer consumer hdistinct
      consumerRegion producerTerm consumerTerm producerWire consumerWire
      consumedPort).wires wire).scope = region)
  have predicateEq : ∀ wire, targetP wire = sourceP (domain.origin wire) := by
    intro wire
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, targetP, sourceP]
    rw [fusionRaw_wire_scope]
    rfl
  have subset : ∀ wire, sourceP wire = true → domain.survives wire = true := by
    intro wire selected
    have wireScope : (input.val.wires wire).scope = region := by
      simpa [sourceP] using selected
    have wireNe : wire ≠ consumedWire := by
      intro equality
      subst wire
      exact different (scope.trans wireScope).symm
    simp [domain, fusionWireDomain, wireNe]
  simpa [ConcreteElaboration.exactScopeWires, sourceP, targetP] using
    (filterFin_survivor_origin domain sourceP targetP predicateEq subset)

theorem fusionRaw_exactScopeWires_length_of_ne
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (producerRegion consumerRegion : Fin input.val.regionCount)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts)
    (scope : producerRegion = (input.val.wires consumedWire).scope)
    (region : Fin input.val.regionCount)
    (different : region ≠ producerRegion) :
    (ConcreteElaboration.exactScopeWires
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort)
      region).length =
        (ConcreteElaboration.exactScopeWires input.val region).length := by
  have mapped := congrArg List.length
    (fusionRaw_exactScopeWires_map_of_ne input consumedWire producer consumer
      hdistinct producerRegion consumerRegion producerTerm consumerTerm
      producerWire consumerWire consumedPort scope region different)
  simpa using mapped

namespace Context

theorem extend_sourceIndex_inherited
    (context : Context input consumedWire producer consumer hdistinct
      consumerRegion producerTerm consumerTerm producerWire consumerWire
      consumedPort source target)
    (region : Fin input.val.regionCount)
    (sourceExact : (source.extend region).Exact region)
    (targetExact : (target.extend region).Exact region)
    (index : Fin target.length) :
    (context.extend region sourceExact targetExact).sourceIndex
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend target region).symm
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires
              (fusionRaw input consumedWire producer consumer hdistinct
                consumerRegion producerTerm consumerTerm producerWire
                consumerWire consumedPort) region).length index)) =
      Fin.cast
        (ConcreteElaboration.WireContext.length_extend source region).symm
        (Fin.castAdd
          (ConcreteElaboration.exactScopeWires input.val region).length
          (context.sourceIndex index)) := by
  let targetIndex : Fin (target.extend region).length :=
    Fin.cast
      (ConcreteElaboration.WireContext.length_extend target region).symm
      (Fin.castAdd
        (ConcreteElaboration.exactScopeWires
          (fusionRaw input consumedWire producer consumer hdistinct
            consumerRegion producerTerm consumerTerm producerWire consumerWire
            consumedPort) region).length index)
  let sourceIndex : Fin (source.extend region).length :=
    Fin.cast
      (ConcreteElaboration.WireContext.length_extend source region).symm
      (Fin.castAdd
        (ConcreteElaboration.exactScopeWires input.val region).length
        (context.sourceIndex index))
  change (context.extend region sourceExact targetExact).sourceIndex targetIndex =
    sourceIndex
  have targetGet : (target.extend region).get targetIndex = target.get index := by
    have indexEq : targetIndex = target.outerIndex region index := by
      apply Fin.ext
      rfl
    rw [indexEq]
    exact ConcreteElaboration.WireContext.extend_outer target region index
  have sourceGet :
      (source.extend region).get sourceIndex =
        source.get (context.sourceIndex index) := by
    simp [sourceIndex, ConcreteElaboration.WireContext.extend]
  apply Context.sourceIndex_eq_of_get _ sourceExact.nodup targetIndex sourceIndex
  rw [targetGet, sourceGet]
  exact context.get index

theorem extend_sourceIndex_local_of_ne
    (context : Context input consumedWire producer consumer hdistinct
      consumerRegion producerTerm consumerTerm producerWire consumerWire
      consumedPort source target)
    (producerRegion : Fin input.val.regionCount)
    (scope : producerRegion = (input.val.wires consumedWire).scope)
    (region : Fin input.val.regionCount)
    (different : region ≠ producerRegion)
    (sourceExact : (source.extend region).Exact region)
    (targetExact : (target.extend region).Exact region)
    (index : Fin (ConcreteElaboration.exactScopeWires
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort)
      region).length) :
    (context.extend region sourceExact targetExact).sourceIndex
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend target region).symm
          (Fin.natAdd target.length index)) =
      Fin.cast
        (ConcreteElaboration.WireContext.length_extend source region).symm
        (Fin.natAdd source.length
          (Fin.cast
            (fusionRaw_exactScopeWires_length_of_ne input consumedWire producer
              consumer hdistinct producerRegion consumerRegion producerTerm
              consumerTerm producerWire consumerWire consumedPort scope region
              different)
            index)) := by
  let hlist := fusionRaw_exactScopeWires_map_of_ne input consumedWire producer
    consumer hdistinct producerRegion consumerRegion producerTerm consumerTerm
    producerWire consumerWire consumedPort scope region different
  let lengthEq := fusionRaw_exactScopeWires_length_of_ne input consumedWire
    producer consumer hdistinct producerRegion consumerRegion producerTerm
    consumerTerm producerWire consumerWire consumedPort scope region different
  let sourceLocal := Fin.cast lengthEq index
  let targetIndex : Fin (target.extend region).length :=
    Fin.cast
      (ConcreteElaboration.WireContext.length_extend target region).symm
      (Fin.natAdd target.length index)
  let sourceIndex : Fin (source.extend region).length :=
    Fin.cast
      (ConcreteElaboration.WireContext.length_extend source region).symm
      (Fin.natAdd source.length sourceLocal)
  change (context.extend region sourceExact targetExact).sourceIndex targetIndex =
    sourceIndex
  have targetGet :
      (target.extend region).get targetIndex =
        (ConcreteElaboration.exactScopeWires
          (fusionRaw input consumedWire producer consumer hdistinct
            consumerRegion producerTerm consumerTerm producerWire consumerWire
            consumedPort) region).get index := by
    simpa [targetIndex] using
      (ConcreteElaboration.WireContext.extend_local target region index)
  have localGet :
      (fusionWireDomain input.val consumedWire).origin
          ((ConcreteElaboration.exactScopeWires
            (fusionRaw input consumedWire producer consumer hdistinct
              consumerRegion producerTerm consumerTerm producerWire consumerWire
              consumedPort) region).get index) =
        (ConcreteElaboration.exactScopeWires input.val region).get sourceLocal := by
    let mapIndex : Fin (List.map (fusionWireDomain input.val consumedWire).origin
        (ConcreteElaboration.exactScopeWires
          (fusionRaw input consumedWire producer consumer hdistinct
            consumerRegion producerTerm consumerTerm producerWire consumerWire
            consumedPort) region)).length :=
      Fin.cast (List.length_map _).symm index
    let mappedIndex := Fin.cast (congrArg List.length hlist) mapIndex
    have mappedGet := get_of_eq hlist mappedIndex
    have recovered :
        Fin.cast (congrArg List.length hlist).symm mappedIndex = mapIndex := by
      apply Fin.ext
      rfl
    rw [recovered] at mappedGet
    have mappedIndexEq : mappedIndex = sourceLocal := by
      apply Fin.ext
      simp [mappedIndex, mapIndex, sourceLocal]
    simpa [mapIndex, mappedIndexEq] using mappedGet
  have sourceGet :
      (source.extend region).get sourceIndex =
        (ConcreteElaboration.exactScopeWires input.val region).get sourceLocal := by
    simp [sourceIndex, ConcreteElaboration.WireContext.extend]
  apply Context.sourceIndex_eq_of_get _ sourceExact.nodup targetIndex sourceIndex
  rw [targetGet, sourceGet, localGet]

end Context

def fusionExtendedEnv
    (context : ConcreteElaboration.WireContext diagram)
    (region : Fin diagram.regionCount)
    (outerEnv : Fin context.length → D)
    (localEnv : Fin (ConcreteElaboration.exactScopeWires diagram region).length →
      D) : Fin (context.extend region).length → D :=
  ConcreteElaboration.extendedEnvironment context region outerEnv localEnv

theorem fusionExtendedEnv_outer
    (context : ConcreteElaboration.WireContext diagram)
    (region : Fin diagram.regionCount)
    (outerEnv : Fin context.length → D)
    (localEnv : Fin (ConcreteElaboration.exactScopeWires diagram region).length →
      D)
    (index : Fin context.length) :
    fusionExtendedEnv context region outerEnv localEnv
        (context.outerIndex region index) = outerEnv index := by
  unfold fusionExtendedEnv ConcreteElaboration.extendedEnvironment
  simp only [Function.comp_apply]
  have castEq : Fin.cast
      (ConcreteElaboration.WireContext.length_extend context region)
      (context.outerIndex region index) =
        Fin.castAdd
          (ConcreteElaboration.exactScopeWires diagram region).length index := by
    apply Fin.ext
    rfl
  rw [castEq]
  exact Fin.addCases_left index

noncomputable def fusionTargetLocalEnv
    (context : Context input consumedWire producer consumer hdistinct
      consumerRegion producerTerm consumerTerm producerWire consumerWire
      consumedPort source target)
    (region : Fin input.val.regionCount)
    (sourceExact : (source.extend region).Exact region)
    (targetExact : (target.extend region).Exact region)
    (sourceOuter : Fin source.length → D)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires input.val region).length
      → D) :
    Fin (ConcreteElaboration.exactScopeWires
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort)
      region).length → D :=
  fun localIndex ↦
    fusionExtendedEnv source region sourceOuter sourceLocal
      ((context.extend region sourceExact targetExact).sourceIndex
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend target region).symm
          (Fin.natAdd target.length localIndex)))

theorem fusionExtendedEnv_forward
    (context : Context input consumedWire producer consumer hdistinct
      consumerRegion producerTerm consumerTerm producerWire consumerWire
      consumedPort source target)
    (region : Fin input.val.regionCount)
    (sourceExact : (source.extend region).Exact region)
    (targetExact : (target.extend region).Exact region)
    (sourceOuter : Fin source.length → D)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires input.val region).length
      → D) :
    fusionExtendedEnv source region sourceOuter sourceLocal ∘
        (context.extend region sourceExact targetExact).sourceIndex =
      fusionExtendedEnv target region
        (sourceOuter ∘ context.sourceIndex)
        (fusionTargetLocalEnv context region sourceExact targetExact sourceOuter
          sourceLocal) := by
  funext targetIndex
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend target region) targetIndex
  have recover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend target region).symm split =
        targetIndex := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun inherited ↦ ?_) (fun localIndex ↦ ?_) split
  · have mapped := context.extend_sourceIndex_inherited region sourceExact
      targetExact inherited
    simp only [Function.comp_apply, fusionExtendedEnv,
      ConcreteElaboration.extendedEnvironment, extendWireEnv]
    rw [mapped]
    simp [Function.comp_def]
  · simp [fusionTargetLocalEnv, fusionExtendedEnv,
      ConcreteElaboration.extendedEnvironment, Function.comp_def, extendWireEnv]

noncomputable def fusionSourceLocalEnvOfNe
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (hdistinct : producer ≠ consumer)
    (producerRegion consumerRegion : Fin input.val.regionCount)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumerWire : Fin consumerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts)
    (scope : producerRegion = (input.val.wires consumedWire).scope)
    (region : Fin input.val.regionCount)
    (different : region ≠ producerRegion)
    (targetLocal : Fin (ConcreteElaboration.exactScopeWires
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort)
      region).length → D) :
    Fin (ConcreteElaboration.exactScopeWires input.val region).length → D :=
  targetLocal ∘ Fin.cast
    (fusionRaw_exactScopeWires_length_of_ne input consumedWire producer consumer
      hdistinct producerRegion consumerRegion producerTerm consumerTerm
      producerWire consumerWire consumedPort scope region different).symm

theorem fusionExtendedEnv_backward_of_ne
    (context : Context input consumedWire producer consumer hdistinct
      consumerRegion producerTerm consumerTerm producerWire consumerWire
      consumedPort source target)
    (producerRegion : Fin input.val.regionCount)
    (scope : producerRegion = (input.val.wires consumedWire).scope)
    (region : Fin input.val.regionCount)
    (different : region ≠ producerRegion)
    (sourceExact : (source.extend region).Exact region)
    (targetExact : (target.extend region).Exact region)
    (sourceOuter : Fin source.length → D)
    (targetOuter : Fin target.length → D)
    (outerAgrees : sourceOuter ∘ context.sourceIndex = targetOuter)
    (targetLocal : Fin (ConcreteElaboration.exactScopeWires
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort)
      region).length → D) :
    fusionExtendedEnv source region sourceOuter
          (fusionSourceLocalEnvOfNe input consumedWire producer consumer hdistinct
            producerRegion consumerRegion producerTerm consumerTerm producerWire
            consumerWire consumedPort scope region different targetLocal) ∘
        (context.extend region sourceExact targetExact).sourceIndex =
      fusionExtendedEnv target region targetOuter targetLocal := by
  funext targetIndex
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend target region) targetIndex
  have recover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend target region).symm split =
        targetIndex := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun inherited ↦ ?_) (fun localIndex ↦ ?_) split
  · have mapped := context.extend_sourceIndex_inherited region sourceExact
      targetExact inherited
    simp only [Function.comp_apply, fusionExtendedEnv,
      ConcreteElaboration.extendedEnvironment, extendWireEnv]
    rw [mapped]
    simpa [Function.comp_def] using congrFun outerAgrees inherited
  · have mapped := context.extend_sourceIndex_local_of_ne producerRegion scope
      region different sourceExact targetExact localIndex
    simp only [Function.comp_apply, fusionExtendedEnv,
      ConcreteElaboration.extendedEnvironment, extendWireEnv]
    rw [mapped]
    simp [fusionSourceLocalEnvOfNe, Function.comp_def]


/-- Lift the unchanged-node compiler kernel and a caller-supplied child
simulation across an ordered frame occurrence list.  Route induction uses
this for the material before and after its selected child. -/
theorem compileOccurrences_frameSimulation
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
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (sourceRecurse : ∀ {relations : RelCtx},
      Fin input.val.regionCount →
      (recurseContext : ConcreteElaboration.WireContext input.val) →
      ConcreteElaboration.BinderContext input.val relations →
      Option (Region signature recurseContext.length relations))
    (targetRecurse : ∀ {relations : RelCtx},
      Fin input.val.regionCount →
      (recurseContext : ConcreteElaboration.WireContext
        (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
          producerTerm consumerTerm producerWire consumerWire consumedPort)) →
      ConcreteElaboration.BinderContext
        (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
          producerTerm consumerTerm producerWire consumerWire consumedPort)
        relations →
      Option (Region signature recurseContext.length relations))
    (sourceContext : ConcreteElaboration.WireContext input.val)
    (targetContext : ConcreteElaboration.WireContext
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort))
    (context : Context input consumedWire producer consumer hdistinct
      consumerRegion producerTerm consumerTerm producerWire consumerWire
      consumedPort sourceContext targetContext)
    (sourceNodup : sourceContext.Nodup)
    (binders : ConcreteElaboration.BinderContext input.val rels)
    (occurrences : List (ConcreteElaboration.LocalOccurrence
      input.val.regionCount input.val.nodeCount))
    (nodesAway : ∀ node, .node node ∈ occurrences →
      node ≠ producer ∧ node ≠ consumer)
    (childSimulation : ∀ child,
      .child child ∈ occurrences →
      ∀ (sourceItem : Item signature sourceContext.length rels)
        (targetItem : Item signature targetContext.length rels),
      ConcreteElaboration.compileOccurrenceWith? signature input.val
          sourceRecurse sourceContext binders (.child child) = some sourceItem →
      ConcreteElaboration.compileOccurrenceWith? signature
          (fusionRaw input consumedWire producer consumer hdistinct
            consumerRegion producerTerm consumerTerm producerWire consumerWire
            consumedPort)
          targetRecurse targetContext binders
          (mapOccurrence input producer (.child child)) = some targetItem →
      ConcreteElaboration.ItemSimulation model named direction
        context.indexRelation sourceItem targetItem)
    (sourceItems : ItemSeq signature sourceContext.length rels)
    (targetItems : ItemSeq signature targetContext.length rels)
    (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      input.val sourceRecurse sourceContext binders occurrences =
        some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort)
      targetRecurse targetContext binders
      (occurrences.map (mapOccurrence input producer)) = some targetItems) :
    ConcreteElaboration.ItemSeqSimulation model named direction
      context.indexRelation sourceItems targetItems := by
  have lifted :=
    ConcreteElaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
      model named direction sourceRecurse targetRecurse sourceContext
      targetContext binders binders context.indexRelation
      (ConcreteElaboration.identityRelationRenaming rels)
      (mapOccurrence input producer) occurrences (by
        intro occurrence member sourceItem targetItem sourceOccurrence
          targetOccurrence
        cases occurrence with
        | node node =>
            obtain ⟨survives, notConsumer⟩ := nodesAway node member
            simp only [ConcreteElaboration.compileOccurrenceWith?,
              mapOccurrence_node input producer node survives]
              at sourceOccurrence targetOccurrence
            have simulation := unchangedNode_itemSimulation input consumedWire
              producer consumer node hdistinct survives notConsumer
              consumerRegion producerTerm consumerTerm producerWire consumerWire
              consumedPort sourceContext targetContext context sourceNodup binders
              sourceItem targetItem sourceOccurrence targetOccurrence model named
              direction
            have mapEq :
                (ConcreteElaboration.identityRelationRenaming rels :
                  RelationRenaming rels rels) =
                (fun {arity} (relation : RelVar rels arity) ↦ relation) := rfl
            rw [mapEq, Item.renameRelations_id]
            exact simulation
        | child child =>
            have simulation := childSimulation child member sourceItem targetItem
              sourceOccurrence targetOccurrence
            have mapEq :
                (ConcreteElaboration.identityRelationRenaming rels :
                  RelationRenaming rels rels) =
                (fun {arity} (relation : RelVar rels arity) ↦ relation) := rfl
            rw [mapEq, Item.renameRelations_id]
            exact simulation)
      sourceItems targetItems sourceCompiled targetCompiled
  have relationMapEq :
      (ConcreteElaboration.identityRelationRenaming rels :
        RelationRenaming rels rels) =
      (fun {arity} (relation : RelVar rels arity) ↦ relation) := rfl
  rw [relationMapEq, ItemSeq.renameRelations_id] at lifted
  exact lifted

theorem option_bind_pure_eq_map (value : Option α) (f : α → β) :
    (value.bind fun current ↦ some (f current)) = value.map f := by
  cases value <;> rfl

theorem directChild_encloses
    {diagram : ConcreteDiagram} {parent child : Fin diagram.regionCount}
    (parentEq : (diagram.regions child).parent? = some parent) :
    diagram.Encloses parent child := by
  have positive : 0 < diagram.regionCount :=
    Nat.lt_of_le_of_lt (Nat.zero_le child.val) child.isLt
  refine ⟨⟨1, by omega⟩, ?_⟩
  change (match (diagram.regions child).parent? with
    | none => none
    | some directParent => diagram.climb 0 directParent) = some parent
  rw [parentEq]
  rfl

theorem sibling_not_encloses_descendant
    (input : ConcreteDiagram) (wellFormed : input.WellFormed signature)
    {parent selected other descendant : Fin input.regionCount}
    (selectedParent : (input.regions selected).parent? = some parent)
    (otherParent : (input.regions other).parent? = some parent)
    (selectedDescendant : input.Encloses selected descendant)
    (distinct : other ≠ selected) :
    ¬ input.Encloses other descendant := by
  intro otherDescendant
  obtain ⟨selectedSteps, selectedClimb⟩ := selectedDescendant
  obtain ⟨otherSteps, otherClimb⟩ := otherDescendant
  obtain ⟨rootSteps, parentRoot⟩ := wellFormed.all_regions_reach_root parent
  have selectedParentClimb :
      input.climb (selectedSteps.val + 1) descendant = some parent := by
    apply ConcreteElaboration.climb_add selectedClimb
    simp [ConcreteDiagram.climb, selectedParent]
  have otherParentClimb :
      input.climb (otherSteps.val + 1) descendant = some parent := by
    apply ConcreteElaboration.climb_add otherClimb
    simp [ConcreteDiagram.climb, otherParent]
  have selectedRoot :
      input.climb ((selectedSteps.val + 1) + rootSteps.val) descendant =
        some input.root :=
    ConcreteElaboration.climb_add selectedParentClimb parentRoot
  have otherRoot :
      input.climb ((otherSteps.val + 1) + rootSteps.val) descendant =
        some input.root :=
    ConcreteElaboration.climb_add otherParentClimb parentRoot
  have stepsEq :=
    ConcreteElaboration.ParentTraversal.climb_to_root_steps_unique input
      wellFormed.root_is_sheet selectedRoot otherRoot
  have sameSteps : selectedSteps.val = otherSteps.val := by omega
  rw [sameSteps] at selectedClimb
  exact distinct (Option.some.inj (otherClimb.symm.trans selectedClimb))

theorem frame_entails
    (direction : ConcreteElaboration.SimulationDirection)
    (before : direction.Entails sourceBefore targetBefore)
    (focus : sourceFocus ↔ targetFocus)
    (after : direction.Entails sourceAfter targetAfter) :
    direction.Entails
      (sourceBefore ∧ sourceFocus ∧ sourceAfter)
      (targetBefore ∧ targetFocus ∧ targetAfter) := by
  cases direction with
  | forward =>
      rintro ⟨sourceBeforeProof, sourceFocusProof, sourceAfterProof⟩
      exact ⟨before sourceBeforeProof, focus.mp sourceFocusProof,
        after sourceAfterProof⟩
  | backward =>
      rintro ⟨targetBeforeProof, targetFocusProof, targetAfterProof⟩
      exact ⟨before targetBeforeProof, focus.mpr targetFocusProof,
        after targetAfterProof⟩

/-- A subtree containing neither endpoint of fusion is semantically unchanged
apart from stable node/wire compaction.  This is the side-branch kernel used by
the selected producer-to-consumer route. -/
theorem compileRegion_awaySimulation
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
    (targetWellFormed :
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort
      ).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature) :
    ∀ (direction : ConcreteElaboration.SimulationDirection)
      {rels : RelCtx} (fuel : Nat)
      (region : Fin input.val.regionCount)
      (source : ConcreteElaboration.WireContext input.val)
      (target : ConcreteElaboration.WireContext
        (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
          producerTerm consumerTerm producerWire consumerWire consumedPort))
      (context : Context input consumedWire producer consumer hdistinct
        consumerRegion producerTerm consumerTerm producerWire consumerWire
        consumedPort source target)
      (binders : ConcreteElaboration.BinderContext input.val rels),
      ¬ input.val.Encloses region producerRegion →
      ¬ input.val.Encloses region consumerRegion →
      (source.extend region).Exact region →
      (target.extend region).Exact region →
      ∀ (sourceBody : Region signature source.length rels)
        (targetBody : Region signature target.length rels),
      ConcreteElaboration.compileRegion? signature input.val fuel region source
          binders = some sourceBody →
      ConcreteElaboration.compileRegion? signature
          (fusionRaw input consumedWire producer consumer hdistinct
            consumerRegion producerTerm consumerTerm producerWire consumerWire
            consumedPort)
          fuel region target binders = some targetBody →
      ConcreteElaboration.RegionSimulation model named direction
        context.indexRelation sourceBody targetBody := by
  intro direction rels fuel
  induction fuel generalizing direction rels with
  | zero =>
      intro region source target context binders producerAway consumerAway
        sourceExact targetExact sourceBody targetBody sourceCompiled
        targetCompiled
      simp [ConcreteElaboration.compileRegion?] at sourceCompiled
  | succ childFuel ih =>
      intro region source target context binders producerAway consumerAway
        sourceExact targetExact sourceBody targetBody sourceCompiled
        targetCompiled
      have regionNeProducer : region ≠ producerRegion := by
        intro equality
        subst region
        exact producerAway (ConcreteDiagram.Encloses.refl input.val producerRegion)
      simp only [ConcreteElaboration.compileRegion?] at sourceCompiled targetCompiled
      cases sourceItemsResult :
          ConcreteElaboration.compileOccurrencesWith? signature input.val
            (ConcreteElaboration.compileRegion? signature input.val childFuel)
            (source.extend region) binders
            (ConcreteElaboration.localOccurrences input.val region) with
      | none => simp [sourceItemsResult] at sourceCompiled
      | some sourceItems =>
        simp [sourceItemsResult] at sourceCompiled
        subst sourceBody
        have targetLocalEq := fusionRaw_localOccurrences_map_of_ne input
          consumedWire producer consumer hdistinct producerRegion consumerRegion
          producerPorts consumerPorts producerTerm consumerTerm producerWire
          consumerWire consumedPort producerShape consumerShape region
          regionNeProducer
        cases targetItemsResult :
            ConcreteElaboration.compileOccurrencesWith? signature
              (fusionRaw input consumedWire producer consumer hdistinct
                consumerRegion producerTerm consumerTerm producerWire
                consumerWire consumedPort)
              (ConcreteElaboration.compileRegion? signature
                (fusionRaw input consumedWire producer consumer hdistinct
                  consumerRegion producerTerm consumerTerm producerWire
                  consumerWire consumedPort) childFuel)
              (target.extend region) binders
              (ConcreteElaboration.localOccurrences
                (fusionRaw input consumedWire producer consumer hdistinct
                  consumerRegion producerTerm consumerTerm producerWire
                  consumerWire consumedPort) region) with
        | none => simp [targetItemsResult] at targetCompiled
        | some targetItems =>
          simp [targetItemsResult] at targetCompiled
          subst targetBody
          let extendedContext := context.extend region sourceExact targetExact
          have targetMapped :
              ConcreteElaboration.compileOccurrencesWith? signature
                (fusionRaw input consumedWire producer consumer hdistinct
                  consumerRegion producerTerm consumerTerm producerWire
                  consumerWire consumedPort)
                (ConcreteElaboration.compileRegion? signature
                  (fusionRaw input consumedWire producer consumer hdistinct
                    consumerRegion producerTerm consumerTerm producerWire
                    consumerWire consumedPort) childFuel)
                (target.extend region) binders
                ((ConcreteElaboration.localOccurrences input.val region).map
                  (mapOccurrence input producer)) = some targetItems := by
            simpa only [targetLocalEq] using targetItemsResult
          have itemsSimulation := compileOccurrences_frameSimulation input
            consumedWire producer consumer hdistinct consumerRegion producerTerm
            consumerTerm producerWire consumerWire consumedPort model named
            direction
            (ConcreteElaboration.compileRegion? signature input.val childFuel)
            (ConcreteElaboration.compileRegion? signature
              (fusionRaw input consumedWire producer consumer hdistinct
                consumerRegion producerTerm consumerTerm producerWire
                consumerWire consumedPort) childFuel)
            (source.extend region) (target.extend region) extendedContext
            sourceExact.nodup binders
            (ConcreteElaboration.localOccurrences input.val region)
            (by
              intro node member
              have nodeRegion :=
                (ConcreteElaboration.mem_localOccurrences_node input.val region
                  node).mp member
              constructor
              · intro equality
                subst node
                rw [producerShape] at nodeRegion
                exact regionNeProducer nodeRegion.symm
              · intro equality
                subst node
                rw [consumerShape] at nodeRegion
                have regionEq : region = consumerRegion := by
                  simpa using nodeRegion.symm
                subst region
                exact consumerAway
                  (ConcreteDiagram.Encloses.refl input.val consumerRegion))
            (by
              intro child member sourceItem targetItem sourceItemCompiled
                targetItemCompiled
              have parent :=
                (ConcreteElaboration.mem_localOccurrences_child input.val region
                  child).mp member
              have childProducerAway :
                  ¬ input.val.Encloses child producerRegion := by
                intro childAbove
                exact producerAway
                  (ConcreteElaboration.checked_encloses_trans input.property
                    (directChild_encloses parent) childAbove)
              have childConsumerAway :
                  ¬ input.val.Encloses child consumerRegion := by
                intro childAbove
                exact consumerAway
                  (ConcreteElaboration.checked_encloses_trans input.property
                    (directChild_encloses parent) childAbove)
              have sourceChildExact := sourceExact.extend_child input.property
                parent
              have targetParent :
                  ((fusionRaw input consumedWire producer consumer hdistinct
                    consumerRegion producerTerm consumerTerm producerWire
                    consumerWire consumedPort).regions child).parent? =
                      some region := by
                simpa only [fusionRaw_regions] using parent
              have targetChildExact := targetExact.extend_child targetWellFormed
                targetParent
              cases kind : input.val.regions child with
              | sheet =>
                  simp [ConcreteElaboration.compileOccurrenceWith?, kind]
                    at sourceItemCompiled
              | cut actualParent =>
                  have actualParentEq : actualParent = region := by
                    rw [kind] at parent
                    exact Option.some.inj parent
                  subst actualParent
                  simp only [ConcreteElaboration.compileOccurrenceWith?, kind,
                    mapOccurrence_child, fusionRaw_regions]
                    at sourceItemCompiled targetItemCompiled
                  cases sourceChildResult :
                      ConcreteElaboration.compileRegion? signature input.val
                        childFuel child (source.extend region) binders with
                  | none => simp [sourceChildResult] at sourceItemCompiled
                  | some sourceChild =>
                    simp [sourceChildResult] at sourceItemCompiled
                    subst sourceItem
                    cases targetChildResult :
                        ConcreteElaboration.compileRegion? signature
                          (fusionRaw input consumedWire producer consumer
                            hdistinct consumerRegion producerTerm consumerTerm
                            producerWire consumerWire consumedPort)
                          childFuel child (target.extend region) binders with
                    | none => simp [targetChildResult] at targetItemCompiled
                    | some targetChild =>
                      simp [targetChildResult] at targetItemCompiled
                      subst targetItem
                      have bodies := ih direction.flip child
                        (source.extend region) (target.extend region)
                        extendedContext binders childProducerAway
                        childConsumerAway sourceChildExact targetChildExact
                        sourceChild targetChild sourceChildResult targetChildResult
                      intro sourceEnv targetEnv relEnv environments
                      have bodyEntailment := bodies sourceEnv targetEnv relEnv
                        environments
                      simp only [cut_denotes_negation]
                      cases direction with
                      | forward =>
                          exact fun sourceNot targetDenotes ↦
                            sourceNot (bodyEntailment targetDenotes)
                      | backward =>
                          exact fun targetNot sourceDenotes ↦
                            targetNot (bodyEntailment sourceDenotes)
              | bubble actualParent arity =>
                  have actualParentEq : actualParent = region := by
                    rw [kind] at parent
                    exact Option.some.inj parent
                  subst actualParent
                  simp only [ConcreteElaboration.compileOccurrenceWith?, kind,
                    mapOccurrence_child, fusionRaw_regions]
                    at sourceItemCompiled targetItemCompiled
                  cases sourceChildResult :
                      ConcreteElaboration.compileRegion? signature input.val
                        childFuel child (source.extend region)
                        (binders.push child arity) with
                  | none => simp [sourceChildResult] at sourceItemCompiled
                  | some sourceChild =>
                    simp [sourceChildResult] at sourceItemCompiled
                    subst sourceItem
                    change (ConcreteElaboration.compileRegion? signature
                      (fusionRaw input consumedWire producer consumer hdistinct
                        consumerRegion producerTerm consumerTerm producerWire
                        consumerWire consumedPort)
                      childFuel child (target.extend region)
                        (binders.push child arity)).bind
                          (fun body ↦ some (Item.bubble arity body)) =
                            some targetItem at targetItemCompiled
                    cases targetChildResult :
                        ConcreteElaboration.compileRegion? signature
                          (fusionRaw input consumedWire producer consumer
                            hdistinct consumerRegion producerTerm consumerTerm
                            producerWire consumerWire consumedPort)
                          childFuel child (target.extend region)
                          (binders.push child arity) with
                    | none =>
                        simp [targetChildResult] at targetItemCompiled
                    | some targetChild =>
                      simp [targetChildResult] at targetItemCompiled
                      subst targetItem
                      have bodies := ih direction child
                        (source.extend region) (target.extend region)
                        extendedContext (binders.push child arity)
                        childProducerAway childConsumerAway
                        sourceChildExact targetChildExact sourceChild targetChild
                        sourceChildResult targetChildResult
                      intro sourceEnv targetEnv relEnv environments
                      simp only [bubble_denotes_exists]
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
                              environments targetDenotes⟩)
            sourceItems targetItems sourceItemsResult targetMapped
          apply ConcreteElaboration.finishRegion_denote direction source target
            region region context.indexRelation model named sourceItems
            targetItems
          intro relEnv sourceOuter targetOuter outerAgrees
          have outerEq : sourceOuter ∘ context.sourceIndex = targetOuter := by
            simpa [Context.indexRelation] using outerAgrees
          cases direction with
          | forward =>
              intro sourceLocal sourceDenotes
              let targetLocal := fusionTargetLocalEnv context region sourceExact
                targetExact sourceOuter sourceLocal
              refine ⟨targetLocal, itemsSimulation
                (fusionExtendedEnv source region sourceOuter sourceLocal)
                (fusionExtendedEnv target region targetOuter targetLocal)
                relEnv ?_ sourceDenotes⟩
              simpa [extendedContext, Context.indexRelation, targetLocal,
                outerEq] using
                (fusionExtendedEnv_forward context region sourceExact targetExact
                  sourceOuter sourceLocal)
          | backward =>
              intro targetLocal targetDenotes
              let sourceLocal := fusionSourceLocalEnvOfNe input consumedWire
                producer consumer hdistinct producerRegion consumerRegion
                producerTerm consumerTerm producerWire consumerWire consumedPort
                scope region regionNeProducer targetLocal
              refine ⟨sourceLocal, itemsSimulation
                (fusionExtendedEnv source region sourceOuter sourceLocal)
                (fusionExtendedEnv target region targetOuter targetLocal)
                relEnv ?_ targetDenotes⟩
              simpa [extendedContext, Context.indexRelation, sourceLocal] using
                (fusionExtendedEnv_backward_of_ne context producerRegion scope
                  region regionNeProducer sourceExact targetExact sourceOuter
                  targetOuter outerEq targetLocal)

/-- Package an away child region as the cut/bubble item expected by its
parent's ordered occurrence compiler. -/
theorem childOccurrence_awaySimulation
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
    (targetWellFormed :
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort
      ).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (fuel : Nat)
    (parent child : Fin input.val.regionCount)
    (source : ConcreteElaboration.WireContext input.val)
    (target : ConcreteElaboration.WireContext
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort))
    (context : Context input consumedWire producer consumer hdistinct
      consumerRegion producerTerm consumerTerm producerWire consumerWire
      consumedPort source target)
    (binders : ConcreteElaboration.BinderContext input.val rels)
    (parentEq : (input.val.regions child).parent? = some parent)
    (producerAway : ¬ input.val.Encloses child producerRegion)
    (consumerAway : ¬ input.val.Encloses child consumerRegion)
    (sourceExact : (source.extend child).Exact child)
    (targetExact : (target.extend child).Exact child)
    (sourceItem : Item signature source.length rels)
    (targetItem : Item signature target.length rels)
    (sourceCompiled : ConcreteElaboration.compileOccurrenceWith? signature
      input.val (ConcreteElaboration.compileRegion? signature input.val fuel)
      source binders (.child child) = some sourceItem)
    (targetCompiled : ConcreteElaboration.compileOccurrenceWith? signature
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort)
      (ConcreteElaboration.compileRegion? signature
        (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
          producerTerm consumerTerm producerWire consumerWire consumedPort) fuel)
      target binders (.child child) = some targetItem) :
    ConcreteElaboration.ItemSimulation model named direction
      context.indexRelation sourceItem targetItem := by
  cases kind : input.val.regions child with
  | sheet =>
      simp [ConcreteElaboration.compileOccurrenceWith?, kind] at sourceCompiled
  | cut actualParent =>
      have actualParentEq : actualParent = parent := by
        rw [kind] at parentEq
        exact Option.some.inj parentEq
      subst actualParent
      simp only [ConcreteElaboration.compileOccurrenceWith?, kind,
        fusionRaw_regions] at sourceCompiled targetCompiled
      cases sourceResult : ConcreteElaboration.compileRegion? signature input.val
          fuel child source binders with
      | none => simp [sourceResult] at sourceCompiled
      | some sourceBody =>
        simp [sourceResult] at sourceCompiled
        subst sourceItem
        cases targetResult : ConcreteElaboration.compileRegion? signature
            (fusionRaw input consumedWire producer consumer hdistinct
              consumerRegion producerTerm consumerTerm producerWire consumerWire
              consumedPort) fuel child target binders with
        | none => simp [targetResult] at targetCompiled
        | some targetBody =>
          simp [targetResult] at targetCompiled
          subst targetItem
          have bodies := compileRegion_awaySimulation input consumedWire producer
            consumer hdistinct producerRegion consumerRegion producerPorts
            consumerPorts producerTerm consumerTerm producerWire consumerWire
            consumedPort producerShape consumerShape scope targetWellFormed model
            named direction.flip fuel child source target context binders
            producerAway consumerAway sourceExact targetExact sourceBody
            targetBody sourceResult targetResult
          intro sourceEnv targetEnv relEnv environments
          have bodyEntailment := bodies sourceEnv targetEnv relEnv environments
          simp only [cut_denotes_negation]
          cases direction with
          | forward =>
              exact fun sourceNot targetDenotes ↦
                sourceNot (bodyEntailment targetDenotes)
          | backward =>
              exact fun targetNot sourceDenotes ↦
                targetNot (bodyEntailment sourceDenotes)
  | bubble actualParent arity =>
      have actualParentEq : actualParent = parent := by
        rw [kind] at parentEq
        exact Option.some.inj parentEq
      subst actualParent
      simp only [ConcreteElaboration.compileOccurrenceWith?, kind,
        fusionRaw_regions] at sourceCompiled targetCompiled
      cases sourceResult : ConcreteElaboration.compileRegion? signature input.val
          fuel child source (binders.push child arity) with
      | none => simp [sourceResult] at sourceCompiled
      | some sourceBody =>
        simp [sourceResult] at sourceCompiled
        subst sourceItem
        change (ConcreteElaboration.compileRegion? signature
          (fusionRaw input consumedWire producer consumer hdistinct
            consumerRegion producerTerm consumerTerm producerWire consumerWire
            consumedPort) fuel child target (binders.push child arity)).bind
              (fun body ↦ some (Item.bubble arity body)) =
                some targetItem at targetCompiled
        cases targetResult : ConcreteElaboration.compileRegion? signature
            (fusionRaw input consumedWire producer consumer hdistinct
              consumerRegion producerTerm consumerTerm producerWire consumerWire
              consumedPort) fuel child target (binders.push child arity) with
        | none => simp [targetResult] at targetCompiled
        | some targetBody =>
          simp [targetResult] at targetCompiled
          subst targetItem
          have bodies := compileRegion_awaySimulation input consumedWire producer
            consumer hdistinct producerRegion consumerRegion producerPorts
            consumerPorts producerTerm consumerTerm producerWire consumerWire
            consumedPort producerShape consumerShape scope targetWellFormed model
            named direction fuel child source target context
            (binders.push child arity) producerAway consumerAway sourceExact
            targetExact sourceBody targetBody sourceResult targetResult
          intro sourceEnv targetEnv relEnv environments
          simp only [bubble_denotes_exists]
          cases direction with
          | forward =>
              rintro ⟨relationValue, sourceDenotes⟩
              exact ⟨relationValue,
                bodies sourceEnv targetEnv (relationValue, relEnv) environments
                  sourceDenotes⟩
          | backward =>
              rintro ⟨relationValue, targetDenotes⟩
              exact ⟨relationValue,
                bodies sourceEnv targetEnv (relationValue, relEnv) environments
                  targetDenotes⟩

/-- Ordered conjunction transport at the consumer site.  The only changed
item is discharged by the one-point substitution law; every surrounding item
uses the certified away-subtree simulation. -/
theorem consumerItems_entails
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
    (producerEnclosesConsumer : input.val.Encloses producerRegion consumerRegion)
    (regionNe : consumerRegion ≠ producerRegion)
    (targetWellFormed :
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort
      ).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (fuel : Nat)
    (sourceContext : ConcreteElaboration.WireContext input.val)
    (targetContext : ConcreteElaboration.WireContext
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort))
    (sourceExact : sourceContext.Exact consumerRegion)
    (targetExact : targetContext.Exact consumerRegion)
    (context : Context input consumedWire producer consumer hdistinct
      consumerRegion producerTerm consumerTerm producerWire consumerWire
      consumedPort sourceContext targetContext)
    (binders : ConcreteElaboration.BinderContext input.val rels)
    (sourceItems : ItemSeq signature sourceContext.length rels)
    (targetItems : ItemSeq signature targetContext.length rels)
    (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      input.val (ConcreteElaboration.compileRegion? signature input.val fuel)
      sourceContext binders
      (ConcreteElaboration.localOccurrences input.val consumerRegion) =
        some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort)
      (ConcreteElaboration.compileRegion? signature
        (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
          producerTerm consumerTerm producerWire consumerWire consumedPort) fuel)
      targetContext binders
      (ConcreteElaboration.localOccurrences
        (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
          producerTerm consumerTerm producerWire consumerWire consumedPort)
        consumerRegion) = some targetItems)
    (sourceEnv : Fin sourceContext.length → model.Carrier)
    (targetEnv : Fin targetContext.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (agrees : context.indexRelation.EnvironmentsAgree sourceEnv targetEnv)
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
    direction.Entails
      (denoteItemSeq model named sourceEnv relEnv sourceItems)
      (denoteItemSeq model named targetEnv relEnv targetItems) := by
  have consumerMember :
      ConcreteElaboration.LocalOccurrence.node consumer ∈
        ConcreteElaboration.localOccurrences input.val consumerRegion := by
    rw [ConcreteElaboration.mem_localOccurrences_node, consumerShape]
    rfl
  obtain ⟨before, after, localEq⟩ := List.append_of_mem consumerMember
  have decomposedNodup :
      (before ++ ConcreteElaboration.LocalOccurrence.node consumer :: after).Nodup := by
    rw [← localEq]
    exact ConcreteElaboration.localOccurrences_nodup input.val consumerRegion
  have consumerNotBefore :
      ConcreteElaboration.LocalOccurrence.node consumer ∉ before := by
    intro member
    have parts := List.nodup_append.mp decomposedNodup
    exact parts.2.2 _ member _ (by simp) rfl
  have consumerNotAfter :
      ConcreteElaboration.LocalOccurrence.node consumer ∉ after := by
    have parts := List.nodup_append.mp decomposedNodup
    exact (List.nodup_cons.mp parts.2.1).1
  have targetLocalEq := fusionRaw_localOccurrences_map_of_ne input consumedWire
    producer consumer hdistinct producerRegion consumerRegion producerPorts
    consumerPorts producerTerm consumerTerm producerWire consumerWire
    consumedPort producerShape consumerShape consumerRegion regionNe
  have sourceFramed : ConcreteElaboration.compileOccurrencesWith? signature
      input.val (ConcreteElaboration.compileRegion? signature input.val fuel)
      sourceContext binders
      (before ++ .node consumer :: after) = some sourceItems := by
    rw [← localEq]
    exact sourceCompiled
  obtain ⟨sourceBefore, sourceFocus, sourceAfter, sourceBeforeCompiled,
      sourceFocusCompiled, sourceAfterCompiled, sourceItemsEq⟩ :=
    compileOccurrencesWith?_frame_split
      (ConcreteElaboration.compileRegion? signature input.val fuel)
      sourceContext binders before after (.node consumer) sourceItems sourceFramed
  have targetFramed : ConcreteElaboration.compileOccurrencesWith? signature
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort)
      (ConcreteElaboration.compileRegion? signature
        (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
          producerTerm consumerTerm producerWire consumerWire consumedPort) fuel)
      targetContext binders
      (before.map (mapOccurrence input producer) ++
        mapOccurrence input producer (.node consumer) ::
        after.map (mapOccurrence input producer)) = some targetItems := by
    rw [← List.map_cons, ← List.map_append, ← localEq, ← targetLocalEq]
    exact targetCompiled
  obtain ⟨targetBefore, targetFocus, targetAfter, targetBeforeCompiled,
      targetFocusCompiled, targetAfterCompiled, targetItemsEq⟩ :=
    compileOccurrencesWith?_frame_split
      (ConcreteElaboration.compileRegion? signature
        (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
          producerTerm consumerTerm producerWire consumerWire consumedPort) fuel)
      targetContext binders (before.map (mapOccurrence input producer))
      (after.map (mapOccurrence input producer))
      (mapOccurrence input producer (.node consumer)) targetItems targetFramed
  have simulateFrame : ∀ (frame : List (ConcreteElaboration.LocalOccurrence
      input.val.regionCount input.val.nodeCount)),
      (∀ occurrence, occurrence ∈ frame →
        occurrence ∈ ConcreteElaboration.localOccurrences input.val
          consumerRegion) →
      ConcreteElaboration.LocalOccurrence.node consumer ∉ frame →
      ∀ (sourceFrame : ItemSeq signature sourceContext.length rels)
        (targetFrame : ItemSeq signature targetContext.length rels),
      ConcreteElaboration.compileOccurrencesWith? signature input.val
          (ConcreteElaboration.compileRegion? signature input.val fuel)
          sourceContext binders frame = some sourceFrame →
      ConcreteElaboration.compileOccurrencesWith? signature
          (fusionRaw input consumedWire producer consumer hdistinct
            consumerRegion producerTerm consumerTerm producerWire consumerWire
            consumedPort)
          (ConcreteElaboration.compileRegion? signature
            (fusionRaw input consumedWire producer consumer hdistinct
              consumerRegion producerTerm consumerTerm producerWire consumerWire
              consumedPort) fuel)
          targetContext binders (frame.map (mapOccurrence input producer)) =
            some targetFrame →
      ConcreteElaboration.ItemSeqSimulation model named direction
        context.indexRelation sourceFrame targetFrame := by
    intro frame localMembership noConsumer sourceFrame targetFrame
      sourceFrameCompiled targetFrameCompiled
    apply compileOccurrences_frameSimulation input consumedWire producer consumer
      hdistinct consumerRegion producerTerm consumerTerm producerWire consumerWire
      consumedPort model named direction
      (ConcreteElaboration.compileRegion? signature input.val fuel)
      (ConcreteElaboration.compileRegion? signature
        (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
          producerTerm consumerTerm producerWire consumerWire consumedPort) fuel)
      sourceContext targetContext context sourceExact.nodup binders frame
    · intro node member
      have localMember := localMembership (.node node) member
      have nodeRegion :=
        (ConcreteElaboration.mem_localOccurrences_node input.val consumerRegion
          node).mp localMember
      constructor
      · intro equality
        subst node
        rw [producerShape] at nodeRegion
        exact regionNe nodeRegion.symm
      · intro equality
        subst node
        exact noConsumer member
    · intro child member sourceItem targetItem sourceItemCompiled
        targetItemCompiled
      have localMember := localMembership (.child child) member
      have parent :=
        (ConcreteElaboration.mem_localOccurrences_child input.val consumerRegion
          child).mp localMember
      have producerAway : ¬ input.val.Encloses child producerRegion := by
        intro childAbove
        exact (ConcreteElaboration.checked_direct_child_not_encloses_parent
          input.property parent)
          (ConcreteElaboration.checked_encloses_trans input.property childAbove
            producerEnclosesConsumer)
      have consumerAway : ¬ input.val.Encloses child consumerRegion :=
        ConcreteElaboration.checked_direct_child_not_encloses_parent
          input.property parent
      have sourceChildExact := sourceExact.extend_child input.property parent
      have targetParent :
          ((fusionRaw input consumedWire producer consumer hdistinct
            consumerRegion producerTerm consumerTerm producerWire consumerWire
            consumedPort).regions child).parent? = some consumerRegion := by
        simpa only [fusionRaw_regions] using parent
      have targetChildExact := targetExact.extend_child targetWellFormed
        targetParent
      exact childOccurrence_awaySimulation input consumedWire producer consumer
        hdistinct producerRegion consumerRegion producerPorts consumerPorts
        producerTerm consumerTerm producerWire consumerWire consumedPort
        producerShape consumerShape scope targetWellFormed model named direction
        fuel consumerRegion child sourceContext targetContext context binders
        parent producerAway consumerAway sourceChildExact targetChildExact
        sourceItem targetItem sourceItemCompiled targetItemCompiled
    · exact sourceFrameCompiled
    · exact targetFrameCompiled
  have beforeSimulation := simulateFrame before (by
    intro occurrence member
    rw [localEq]
    simp [member]) consumerNotBefore sourceBefore targetBefore
      sourceBeforeCompiled targetBeforeCompiled
  have afterSimulation := simulateFrame after (by
    intro occurrence member
    rw [localEq]
    simp [member]) consumerNotAfter sourceAfter targetAfter
      sourceAfterCompiled targetAfterCompiled
  have focusEquiv := consumerItem_denote_iff input consumedWire producer consumer
    hdistinct producerRegion consumerRegion producerPorts consumerPorts
    producerTerm consumerTerm producerWire consumerWire consumedPort producerShape
    consumerShape scope producerResolved consumerResolved endpoints
    targetWellFormed sourceContext targetContext sourceExact targetExact context
    binders binders sourceFocus targetFocus (by
      simpa [ConcreteElaboration.compileOccurrenceWith?] using
        sourceFocusCompiled) (by
      simpa [ConcreteElaboration.compileOccurrenceWith?, mapOccurrence,
        hdistinct.symm] using targetFocusCompiled)
    model named sourceEnv targetEnv relEnv agrees consumedValue
  rw [sourceItemsEq, targetItemsEq, denoteItemSeq_frame,
    denoteItemSeq_frame]
  exact frame_entails direction
    (beforeSimulation sourceEnv targetEnv relEnv agrees) focusEquiv
    (afterSimulation sourceEnv targetEnv relEnv agrees)

theorem producerEquation_extended
    (input : CheckedDiagram signature)
    (consumedWire : Fin input.val.wireCount)
    (producer consumer : Fin input.val.nodeCount)
    (producerRegion consumerRegion : Fin input.val.regionCount)
    (producerPorts consumerPorts : Nat)
    (producerTerm : Lambda.Term 0 (Fin producerPorts))
    (consumerTerm : Lambda.Term 0 (Fin consumerPorts))
    (producerWire : Fin producerPorts → Fin input.val.wireCount)
    (consumedPort : Fin consumerPorts)
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
          { node := consumer, port := CPort.free consumedPort.val }] ∨
      (input.val.wires consumedWire).endpoints = [
          { node := consumer, port := CPort.free consumedPort.val },
          { node := producer, port := CPort.output }])
    (source : ConcreteElaboration.WireContext input.val)
    (sourceExact : (source.extend consumerRegion).Exact consumerRegion)
    (consumedIndex : Fin source.length)
    (consumedGet : source.get consumedIndex = consumedWire)
    (producerIndex : Fin producerPorts → Fin source.length)
    (producerGet : ∀ port, source.get (producerIndex port) = producerWire port)
    (model : Lambda.LambdaModel)
    (sourceOuter : Fin source.length → model.Carrier)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires input.val
      consumerRegion).length → model.Carrier)
    (producerEquation : sourceOuter consumedIndex =
      model.eval producerTerm (sourceOuter ∘ producerIndex)) :
    fusionExtendedEnv source consumerRegion sourceOuter sourceLocal
        (visibleIndex input.val (source.extend consumerRegion) consumerRegion
          sourceExact consumedWire
          (consumedWire_encloses_consumer input consumedWire producer consumer
            consumedPort.val consumerRegion consumerPorts consumerTerm
            consumerShape endpoints)) =
      model.eval producerTerm (fun port ↦
        fusionExtendedEnv source consumerRegion sourceOuter sourceLocal
          (visibleIndex input.val (source.extend consumerRegion) consumerRegion
            sourceExact (producerWire port)
            (producerWire_encloses_consumer input consumedWire producer consumer
              consumedPort.val producerRegion consumerRegion producerPorts
              consumerPorts producerTerm consumerTerm producerWire producerShape
              consumerShape scope producerResolved endpoints port))) := by
  have consumedOuterGet : (source.extend consumerRegion).get
      (source.outerIndex consumerRegion consumedIndex) = consumedWire := by
    simpa only [List.get_eq_getElem] using
      (source.extend_outer consumerRegion consumedIndex).trans consumedGet
  have consumedIndexEq := index_eq_visibleIndex_of_get input.val
    (source.extend consumerRegion) consumerRegion sourceExact consumedWire
    (consumedWire_encloses_consumer input consumedWire producer consumer
      consumedPort.val consumerRegion consumerPorts consumerTerm consumerShape
      endpoints) (source.outerIndex consumerRegion consumedIndex)
    consumedOuterGet
  rw [← consumedIndexEq, fusionExtendedEnv_outer, producerEquation]
  apply congrArg (model.eval producerTerm)
  funext port
  have producerOuterGet : (source.extend consumerRegion).get
      (source.outerIndex consumerRegion (producerIndex port)) =
        producerWire port := by
    simpa only [List.get_eq_getElem] using
      (source.extend_outer consumerRegion (producerIndex port)).trans
        (producerGet port)
  have producerIndexEq := index_eq_visibleIndex_of_get input.val
    (source.extend consumerRegion) consumerRegion sourceExact
    (producerWire port)
    (producerWire_encloses_consumer input consumedWire producer consumer
      consumedPort.val producerRegion consumerRegion producerPorts consumerPorts
      producerTerm consumerTerm producerWire producerShape consumerShape scope
      producerResolved endpoints port)
    (source.outerIndex consumerRegion (producerIndex port)) producerOuterGet
  simp only [Function.comp_apply]
  rw [← producerIndexEq, fusionExtendedEnv_outer]

theorem consumerRegion_entails
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
    (producerEnclosesConsumer : input.val.Encloses producerRegion consumerRegion)
    (regionNe : consumerRegion ≠ producerRegion)
    (targetWellFormed :
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort
      ).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (fuel : Nat)
    (source : ConcreteElaboration.WireContext input.val)
    (target : ConcreteElaboration.WireContext
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort))
    (context : Context input consumedWire producer consumer hdistinct
      consumerRegion producerTerm consumerTerm producerWire consumerWire
      consumedPort source target)
    (binders : ConcreteElaboration.BinderContext input.val rels)
    (sourceExact : (source.extend consumerRegion).Exact consumerRegion)
    (targetExact : (target.extend consumerRegion).Exact consumerRegion)
    (consumedIndex : Fin source.length)
    (consumedGet : source.get consumedIndex = consumedWire)
    (producerIndex : Fin producerPorts → Fin source.length)
    (producerGet : ∀ port, source.get (producerIndex port) = producerWire port)
    (sourceBody : Region signature source.length rels)
    (targetBody : Region signature target.length rels)
    (sourceCompiled : ConcreteElaboration.compileRegion? signature input.val
      (fuel + 1) consumerRegion source binders = some sourceBody)
    (targetCompiled : ConcreteElaboration.compileRegion? signature
      (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
        producerTerm consumerTerm producerWire consumerWire consumedPort)
      (fuel + 1) consumerRegion target binders = some targetBody)
    (sourceOuter : Fin source.length → model.Carrier)
    (targetOuter : Fin target.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels)
    (outerAgrees : context.indexRelation.EnvironmentsAgree sourceOuter targetOuter)
    (producerEquation : sourceOuter consumedIndex =
      model.eval producerTerm (sourceOuter ∘ producerIndex)) :
    direction.Entails
      (denoteRegion model named sourceOuter relEnv sourceBody)
      (denoteRegion model named targetOuter relEnv targetBody) := by
  simp only [ConcreteElaboration.compileRegion?] at sourceCompiled targetCompiled
  cases sourceItemsResult : ConcreteElaboration.compileOccurrencesWith? signature
      input.val (ConcreteElaboration.compileRegion? signature input.val fuel)
      (source.extend consumerRegion) binders
      (ConcreteElaboration.localOccurrences input.val consumerRegion) with
  | none => simp [sourceItemsResult] at sourceCompiled
  | some sourceItems =>
    simp [sourceItemsResult] at sourceCompiled
    subst sourceBody
    cases targetItemsResult : ConcreteElaboration.compileOccurrencesWith? signature
        (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
          producerTerm consumerTerm producerWire consumerWire consumedPort)
        (ConcreteElaboration.compileRegion? signature
          (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
            producerTerm consumerTerm producerWire consumerWire consumedPort) fuel)
        (target.extend consumerRegion) binders
        (ConcreteElaboration.localOccurrences
          (fusionRaw input consumedWire producer consumer hdistinct consumerRegion
            producerTerm consumerTerm producerWire consumerWire consumedPort)
          consumerRegion) with
    | none => simp [targetItemsResult] at targetCompiled
    | some targetItems =>
      simp [targetItemsResult] at targetCompiled
      subst targetBody
      have outerEq : sourceOuter ∘ context.sourceIndex = targetOuter := by
        simpa [Context.indexRelation] using outerAgrees
      cases direction with
      | forward =>
        intro sourceDenotes
        unfold ConcreteElaboration.finishRegion at sourceDenotes ⊢
        simp only [denoteRegion_mk, ItemSeq.castWiresEq_eq_renameWires]
          at sourceDenotes ⊢
        obtain ⟨sourceLocal, sourceCast⟩ := sourceDenotes
        let targetLocal := fusionTargetLocalEnv context consumerRegion sourceExact
          targetExact sourceOuter sourceLocal
        refine ⟨targetLocal, ?_⟩
        let sourceRaw := fusionExtendedEnv source consumerRegion sourceOuter
          sourceLocal
        let targetRaw := fusionExtendedEnv target consumerRegion targetOuter
          targetLocal
        have sourceRawItems := (denoteItemSeq_renameWires model named
          (Fin.cast (ConcreteElaboration.WireContext.length_extend source
            consumerRegion)) (extendWireEnv sourceOuter sourceLocal) relEnv
          sourceItems).mp sourceCast
        change denoteItemSeq model named sourceRaw relEnv sourceItems at sourceRawItems
        have extendedAgrees :
            ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
              (context.extend consumerRegion sourceExact targetExact).indexRelation
              sourceRaw targetRaw := by
          simpa [Context.indexRelation, sourceRaw, targetRaw, targetLocal,
            outerEq] using
            (fusionExtendedEnv_forward context consumerRegion sourceExact
              targetExact sourceOuter sourceLocal)
        have consumedValue := producerEquation_extended input consumedWire
          producer consumer producerRegion consumerRegion producerPorts
          consumerPorts producerTerm consumerTerm producerWire consumedPort
          producerShape consumerShape scope producerResolved endpoints source
          sourceExact consumedIndex consumedGet producerIndex producerGet model
          sourceOuter sourceLocal producerEquation
        have targetRawItems := consumerItems_entails input consumedWire producer
          consumer hdistinct producerRegion consumerRegion producerPorts
          consumerPorts producerTerm consumerTerm producerWire consumerWire
          consumedPort producerShape consumerShape scope producerResolved
          consumerResolved endpoints producerEnclosesConsumer regionNe
          targetWellFormed model named .forward fuel (source.extend consumerRegion)
          (target.extend consumerRegion) sourceExact targetExact
          (context.extend consumerRegion sourceExact targetExact) binders
          sourceItems targetItems sourceItemsResult targetItemsResult sourceRaw
          targetRaw relEnv extendedAgrees consumedValue sourceRawItems
        exact (denoteItemSeq_renameWires model named
          (Fin.cast (ConcreteElaboration.WireContext.length_extend target
            consumerRegion)) (extendWireEnv targetOuter targetLocal) relEnv
          targetItems).mpr targetRawItems
      | backward =>
        intro targetDenotes
        unfold ConcreteElaboration.finishRegion at targetDenotes ⊢
        simp only [denoteRegion_mk, ItemSeq.castWiresEq_eq_renameWires]
          at targetDenotes ⊢
        obtain ⟨targetLocal, targetCast⟩ := targetDenotes
        let sourceLocal := fusionSourceLocalEnvOfNe input consumedWire producer
          consumer hdistinct producerRegion consumerRegion producerTerm
          consumerTerm producerWire consumerWire consumedPort scope
          consumerRegion regionNe targetLocal
        refine ⟨sourceLocal, ?_⟩
        let sourceRaw := fusionExtendedEnv source consumerRegion sourceOuter
          sourceLocal
        let targetRaw := fusionExtendedEnv target consumerRegion targetOuter
          targetLocal
        have targetRawItems := (denoteItemSeq_renameWires model named
          (Fin.cast (ConcreteElaboration.WireContext.length_extend target
            consumerRegion)) (extendWireEnv targetOuter targetLocal) relEnv
          targetItems).mp targetCast
        change denoteItemSeq model named targetRaw relEnv targetItems at targetRawItems
        have extendedAgrees :
            ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
              (context.extend consumerRegion sourceExact targetExact).indexRelation
              sourceRaw targetRaw := by
          simpa [Context.indexRelation, sourceRaw, targetRaw, sourceLocal] using
            (fusionExtendedEnv_backward_of_ne context producerRegion scope
              consumerRegion regionNe sourceExact targetExact sourceOuter
              targetOuter outerEq targetLocal)
        have consumedValue := producerEquation_extended input consumedWire
          producer consumer producerRegion consumerRegion producerPorts
          consumerPorts producerTerm consumerTerm producerWire consumedPort
          producerShape consumerShape scope producerResolved endpoints source
          sourceExact consumedIndex consumedGet producerIndex producerGet model
          sourceOuter sourceLocal producerEquation
        have sourceRawItems := consumerItems_entails input consumedWire producer
          consumer hdistinct producerRegion consumerRegion producerPorts
          consumerPorts producerTerm consumerTerm producerWire consumerWire
          consumedPort producerShape consumerShape scope producerResolved
          consumerResolved endpoints producerEnclosesConsumer regionNe
          targetWellFormed model named .backward fuel
          (source.extend consumerRegion) (target.extend consumerRegion)
          sourceExact targetExact
          (context.extend consumerRegion sourceExact targetExact) binders
          sourceItems targetItems sourceItemsResult targetItemsResult sourceRaw
          targetRaw relEnv extendedAgrees consumedValue targetRawItems
        exact (denoteItemSeq_renameWires model named
          (Fin.cast (ConcreteElaboration.WireContext.length_extend source
            consumerRegion)) (extendWireEnv sourceOuter sourceLocal) relEnv
          sourceItems).mpr sourceRawItems

end FusionSoundness

end VisualProof.Rule
