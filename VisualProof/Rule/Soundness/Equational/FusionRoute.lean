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

end FusionSoundness

end VisualProof.Rule
