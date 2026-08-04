import VisualProof.Rule.Soundness.Equational.HeadStripCompaction.Structure

namespace VisualProof.Rule

open VisualProof
open Lambda
open VisualProof.Data.Finite
open Diagram
open Theory

namespace HeadStripCompaction

def reducedOldWire (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (wire : Fin input.val.wireCount) (notOutput : wire ≠ payload.outputWire) :
    Fin (Reduced input payload).wireCount :=
  Fin.castAdd payload.argumentIndices.length
    ((headStripWireDomain input.val payload.outputWire).index wire (by
      simp [headStripWireDomain, notOutput]))

@[simp] theorem expandWire_reducedOldWire (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (wire : Fin input.val.wireCount) (notOutput : wire ≠ payload.outputWire) :
    expandWire input payload (reducedOldWire input payload wire notOutput) =
      Fin.castAdd payload.argumentIndices.length wire := by
  apply Fin.ext
  simp only [expandWire, reducedOldWire, Fin.addCases_left]
  change ((headStripWireDomain input.val payload.outputWire).origin
    ((headStripWireDomain input.val payload.outputWire).index wire _)).val =
      wire.val
  rw [(headStripWireDomain input.val payload.outputWire).origin_index]

def reducedFirstWire (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (port : Fin payload.firstFreePorts) :
    Fin (Reduced input payload).wireCount :=
  reducedOldWire input payload (payload.firstWire port)
    (payload.firstWire_ne_output port)

def reducedSecondWire (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (port : Fin payload.secondFreePorts) :
    Fin (Reduced input payload).wireCount :=
  reducedOldWire input payload (payload.secondWire port)
    (payload.secondWire_ne_output port)

theorem reduced_climb (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second) :
    ∀ steps (region : Fin input.val.regionCount),
      (Reduced input payload).climb steps region = input.val.climb steps region := by
  intro steps
  induction steps with
  | zero => intro region; rfl
  | succ steps induction =>
      intro region
      unfold ConcreteDiagram.climb
      rw [show (Reduced input payload).regions region = input.val.regions region by
        rfl]
      split
      · rename_i hparent
        have hparentInput : (input.val.regions region).parent? =
            (none : Option (Fin input.val.regionCount)) := by
          simpa only [] using hparent
        have hright : input.val.climb (Nat.succ steps) region = none := by
          unfold ConcreteDiagram.climb
          rw [hparentInput]
        exact hright.symm
      · rename_i parent hparent
        let inputParent : Fin input.val.regionCount := Fin.cast (by rfl) parent
        have hparentInput : (input.val.regions region).parent? =
            some inputParent := by
          simpa only [inputParent] using hparent
        have hright : input.val.climb (Nat.succ steps) region =
            input.val.climb steps inputParent := by
          simp [ConcreteDiagram.climb, hparentInput]
        have leftCast : (Reduced input payload).climb steps parent =
            (Reduced input payload).climb steps inputParent := by rfl
        rw [leftCast]
        exact (induction inputParent).trans hright.symm

theorem reduced_encloses_of_input (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    {ancestor descendant : Fin input.val.regionCount}
    (encloses : input.val.Encloses ancestor descendant) :
    (Reduced input payload).Encloses ancestor descendant := by
  rcases encloses with ⟨steps, climbed⟩
  exact ⟨steps, (reduced_climb input payload steps descendant).trans climbed⟩

theorem reducedFirstWire_encloses (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (port : Fin payload.firstFreePorts) :
    (Reduced input payload).Encloses
      ((Reduced input payload).wires
        (reducedFirstWire input payload port)).scope payload.region := by
  have enclosed := input.property.wire_scopes_enclose
    (payload.firstWire port) { node := first, port := .free port }
      (payload.firstWire_occurs port)
  rw [payload.firstNode] at enclosed
  apply reduced_encloses_of_input input payload
  have scopeEq : ((Reduced input payload).wires
      (reducedFirstWire input payload port)).scope =
      (input.val.wires (payload.firstWire port)).scope := by
    rw [← expandWire_scope input payload,
      show expandWire input payload (reducedFirstWire input payload port) =
        Fin.castAdd payload.argumentIndices.length (payload.firstWire port) by
          exact expandWire_reducedOldWire input payload _ _]
    exact HeadStripSoundness.headStripExpandedRaw_oldWire_scope input payload _
  rw [scopeEq]
  simpa using enclosed

theorem reducedSecondWire_encloses (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (port : Fin payload.secondFreePorts) :
    (Reduced input payload).Encloses
      ((Reduced input payload).wires
        (reducedSecondWire input payload port)).scope payload.region := by
  have enclosed := input.property.wire_scopes_enclose
    (payload.secondWire port) { node := second, port := .free port }
      (payload.secondWire_occurs port)
  rw [payload.secondNode] at enclosed
  apply reduced_encloses_of_input input payload
  have scopeEq : ((Reduced input payload).wires
      (reducedSecondWire input payload port)).scope =
      (input.val.wires (payload.secondWire port)).scope := by
    rw [← expandWire_scope input payload,
      show expandWire input payload (reducedSecondWire input payload port) =
        Fin.castAdd payload.argumentIndices.length (payload.secondWire port) by
          exact expandWire_reducedOldWire input payload _ _]
    exact HeadStripSoundness.headStripExpandedRaw_oldWire_scope input payload _
  rw [scopeEq]
  simpa using enclosed

theorem reduced_shared_wire (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (left : Fin payload.firstFreePorts)
    (right : Fin payload.secondFreePorts)
    (commonEq : payload.firstPort left = payload.secondPort right) :
    reducedFirstWire input payload left =
      reducedSecondWire input payload right := by
  apply expandWire_injective input payload
  unfold reducedFirstWire reducedSecondWire
  rw [expandWire_reducedOldWire, expandWire_reducedOldWire,
    payload.shared_wire left right commonEq]

theorem reduced_common_environment
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (context : ConcreteElaboration.WireContext (Reduced input payload))
    (exact : context.Exact payload.region)
    (env : Fin context.length → Lambda.Individual) :
    ∃ common : Fin payload.commonPorts → Lambda.Individual,
      (∀ port index, context.get index = reducedFirstWire input payload port →
        env index = common (payload.firstPort port)) ∧
      (∀ port index, context.get index = reducedSecondWire input payload port →
        env index = common (payload.secondPort port)) := by
  have firstMember : ∀ port, reducedFirstWire input payload port ∈ context := by
    intro port
    exact (exact.mem_iff _).mpr (reducedFirstWire_encloses input payload port)
  have secondMember : ∀ port, reducedSecondWire input payload port ∈ context := by
    intro port
    exact (exact.mem_iff _).mpr (reducedSecondWire_encloses input payload port)
  let firstIndex : Fin payload.firstFreePorts → Fin context.length :=
    fun port => Classical.choose
      (ConcreteElaboration.WireContext.lookup?_complete (firstMember port))
  let secondIndex : Fin payload.secondFreePorts → Fin context.length :=
    fun port => Classical.choose
      (ConcreteElaboration.WireContext.lookup?_complete (secondMember port))
  have firstGet : ∀ port,
      context.get (firstIndex port) = reducedFirstWire input payload port := by
    intro port
    exact ConcreteElaboration.WireContext.lookup?_sound (Classical.choose_spec
      (ConcreteElaboration.WireContext.lookup?_complete (firstMember port)))
  have secondGet : ∀ port,
      context.get (secondIndex port) = reducedSecondWire input payload port := by
    intro port
    exact ConcreteElaboration.WireContext.lookup?_sound (Classical.choose_spec
      (ConcreteElaboration.WireContext.lookup?_complete (secondMember port)))
  have aligned : ∀ left right,
      payload.firstPort left = payload.secondPort right →
        (env ∘ firstIndex) left = (env ∘ secondIndex) right := by
    intro left right commonEq
    have indexEq : firstIndex left = secondIndex right := by
      apply Fin.ext
      exact (List.getElem_inj (i := (firstIndex left).val)
        (j := (secondIndex right).val) (h₀ := (firstIndex left).isLt)
        (h₁ := (secondIndex right).isLt) exact.nodup).mp (by
          simpa only [List.get_eq_getElem] using
            (firstGet left).trans
              ((reduced_shared_wire input payload left right commonEq).trans
                (secondGet right).symm))
    simp [indexEq]
  obtain ⟨common, firstCommon, secondCommon⟩ :=
    payload.exists_common_environment (env ∘ firstIndex)
      (env ∘ secondIndex) aligned
  refine ⟨common, ?_, ?_⟩
  · intro port index getWire
    have indexEq : index = firstIndex port := by
      apply Fin.ext
      exact (List.getElem_inj (i := index.val) (j := (firstIndex port).val)
        (h₀ := index.isLt) (h₁ := (firstIndex port).isLt) exact.nodup).mp
          (by simpa only [List.get_eq_getElem] using
            getWire.trans (firstGet port).symm)
    subst index
    exact (congrFun firstCommon port).symm
  · intro port index getWire
    have indexEq : index = secondIndex port := by
      apply Fin.ext
      exact (List.getElem_inj (i := index.val) (j := (secondIndex port).val)
        (h₀ := index.isLt) (h₁ := (secondIndex port).isLt) exact.nodup).mp
          (by simpa only [List.get_eq_getElem] using
            getWire.trans (secondGet port).symm)
    subst index
    exact (congrFun secondCommon port).symm

def reducedArgumentWire (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (position : Fin payload.argumentIndices.length) :
    Fin (Reduced input payload).wireCount :=
  Fin.natAdd (headStripWireDomain input.val payload.outputWire).count position

@[simp] theorem reduced_first_node (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (position : Fin payload.argumentIndices.length) :
    (Reduced input payload).nodes (payload.firstReducedNode position) =
      .term payload.region
        (payload.firstArgument
          (payload.argumentIndices.get position)).freeSupport.length
        (payload.firstArgument
          (payload.argumentIndices.get position)).compact := by
  rw [← expandNode_value input payload]
  rw [expandNode_firstReduced]
  exact HeadStripSoundness.headStripExpandedRaw_firstAddedNode payload position

@[simp] theorem reduced_second_node (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (position : Fin payload.argumentIndices.length) :
    (Reduced input payload).nodes (payload.secondReducedNode position) =
      .term payload.region
        (payload.secondArgument
          (payload.argumentIndices.get position)).freeSupport.length
        (payload.secondArgument
          (payload.argumentIndices.get position)).compact := by
  rw [← expandNode_value input payload]
  rw [expandNode_secondReduced]
  exact HeadStripSoundness.headStripExpandedRaw_secondAddedNode payload position

theorem reduced_first_output_occurs (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (position : Fin payload.argumentIndices.length) :
    (Reduced input payload).EndpointOccurs
      (reducedArgumentWire input payload position)
      { node := payload.firstReducedNode position, port := .output } := by
  apply (expandEndpoint_occurs input payload _ _).mpr
  change (Expanded input payload).EndpointOccurs
    (expandWire input payload
      (Fin.natAdd (headStripWireDomain input.val payload.outputWire).count
        position)) _
  rw [expandWire_fresh]
  simpa [expandEndpoint] using
    HeadStripSoundness.headStripExpandedRaw_firstAddedOutput_occurs
      payload position

theorem reduced_second_output_occurs (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (position : Fin payload.argumentIndices.length) :
    (Reduced input payload).EndpointOccurs
      (reducedArgumentWire input payload position)
      { node := payload.secondReducedNode position, port := .output } := by
  apply (expandEndpoint_occurs input payload _ _).mpr
  change (Expanded input payload).EndpointOccurs
    (expandWire input payload
      (Fin.natAdd (headStripWireDomain input.val payload.outputWire).count
        position)) _
  rw [expandWire_fresh]
  simpa [expandEndpoint] using
    HeadStripSoundness.headStripExpandedRaw_secondAddedOutput_occurs
      payload position

theorem reduced_first_free_occurs (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (position : Fin payload.argumentIndices.length)
    (port : Fin (payload.firstArgument
      (payload.argumentIndices.get position)).freeSupport.length) :
    (Reduced input payload).EndpointOccurs
      (reducedFirstWire input payload
        ((payload.firstArgument
          (payload.argumentIndices.get position)).freeSupport.get port))
      { node := payload.firstReducedNode position, port := .free port } := by
  apply (expandEndpoint_occurs input payload _ _).mpr
  unfold reducedFirstWire
  rw [expandWire_reducedOldWire]
  simpa [expandEndpoint] using
    HeadStripSoundness.headStripExpandedRaw_firstAddedFree_occurs
      payload position port

theorem reduced_second_free_occurs (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (position : Fin payload.argumentIndices.length)
    (port : Fin (payload.secondArgument
      (payload.argumentIndices.get position)).freeSupport.length) :
    (Reduced input payload).EndpointOccurs
      (reducedSecondWire input payload
        ((payload.secondArgument
          (payload.argumentIndices.get position)).freeSupport.get port))
      { node := payload.secondReducedNode position, port := .free port } := by
  apply (expandEndpoint_occurs input payload _ _).mpr
  unfold reducedSecondWire
  rw [expandWire_reducedOldWire]
  simpa [expandEndpoint] using
    HeadStripSoundness.headStripExpandedRaw_secondAddedFree_occurs
      payload position port

theorem reduced_position_evaluations_equal
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (reducedWellFormed : (Reduced input payload).WellFormed signature)
    (context : ConcreteElaboration.WireContext (Reduced input payload))
    (binders : ConcreteElaboration.BinderContext
      (Reduced input payload) rels)
    (fuel : Nat)
    (items : ItemSeq signature context.length rels)
    (compiled : ConcreteElaboration.compileOccurrencesWith? signature
      (Reduced input payload)
      (ConcreteElaboration.compileRegion? signature (Reduced input payload) fuel)
      context binders
      (ConcreteElaboration.localOccurrences (Reduced input payload)
        payload.region) = some items)
    (exact : context.Exact payload.region)
    (named : NamedEnv Lambda.Individual signature)
    (env : Fin context.length → Lambda.Individual)
    (relEnv : RelEnv Lambda.Individual rels)
    (itemsDenote : denoteItemSeq Lambda.canonicalModel named env relEnv items)
    (common : Fin payload.commonPorts → Lambda.Individual)
    (firstCommon : ∀ port index,
      context.get index = reducedFirstWire input payload port →
        env index = common (payload.firstPort port))
    (secondCommon : ∀ port index,
      context.get index = reducedSecondWire input payload port →
        env index = common (payload.secondPort port))
    (position : Fin payload.argumentIndices.length) :
    Lambda.canonicalModel.eval
        ((payload.firstArgument
          (payload.argumentIndices.get position)).mapFree payload.firstPort)
        common =
      Lambda.canonicalModel.eval
        ((payload.secondArgument
          (payload.argumentIndices.get position)).mapFree payload.secondPort)
        common := by
  let reducedChecked : CheckedDiagram signature :=
    ⟨Reduced input payload, reducedWellFormed⟩
  let firstArgument :=
    payload.firstArgument (payload.argumentIndices.get position)
  let secondArgument :=
    payload.secondArgument (payload.argumentIndices.get position)
  obtain ⟨firstOutput, firstFree, firstOutputResult, firstFreeResult,
      firstEquation⟩ :=
    CongruenceSoundness.compiled_items_term_node_equation
      (checked := reducedChecked) context binders fuel items compiled exact
      (payload.firstReducedNode position) firstArgument.freeSupport.length
      firstArgument.compact (by
        simpa [reducedChecked, firstArgument] using
          (reduced_first_node input payload position))
      Lambda.canonicalModel named env relEnv itemsDenote
  obtain ⟨secondOutput, secondFree, secondOutputResult, secondFreeResult,
      secondEquation⟩ :=
    CongruenceSoundness.compiled_items_term_node_equation
      (checked := reducedChecked) context binders fuel items compiled exact
      (payload.secondReducedNode position) secondArgument.freeSupport.length
      secondArgument.compact (by
        simpa [reducedChecked, secondArgument] using
          (reduced_second_node input payload position))
      Lambda.canonicalModel named env relEnv itemsDenote
  obtain ⟨firstWire, firstOccurs, firstGet⟩ :=
    ConcreteElaboration.resolvePort?_sound firstOutputResult
  obtain ⟨secondWire, secondOccurs, secondGet⟩ :=
    ConcreteElaboration.resolvePort?_sound secondOutputResult
  have firstWireEq : firstWire = reducedArgumentWire input payload position :=
    ConcreteElaboration.endpoint_wire_unique
      reducedWellFormed.wire_endpoints_are_disjoint firstOccurs
      (reduced_first_output_occurs input payload position)
  have secondWireEq : secondWire = reducedArgumentWire input payload position :=
    ConcreteElaboration.endpoint_wire_unique
      reducedWellFormed.wire_endpoints_are_disjoint secondOccurs
      (reduced_second_output_occurs input payload position)
  have outputIndexEq : firstOutput = secondOutput := by
    apply Fin.ext
    exact (List.getElem_inj exact.nodup).mp (by
      simpa only [List.get_eq_getElem] using
        firstGet.trans (firstWireEq.trans
          (secondWireEq.symm.trans secondGet.symm)))
  have firstFreeEnvironment : env ∘ firstFree =
      (common ∘ payload.firstPort) ∘ firstArgument.freeSupport.get := by
    funext port
    have resolved := sequenceFin_sound firstFreeResult port
    obtain ⟨wire, occurs, getWire⟩ :=
      ConcreteElaboration.resolvePort?_sound resolved
    have wireEq : wire = reducedFirstWire input payload
        (firstArgument.freeSupport.get port) :=
      ConcreteElaboration.endpoint_wire_unique
        reducedWellFormed.wire_endpoints_are_disjoint occurs
        (by simpa [firstArgument] using
          reduced_first_free_occurs input payload position port)
    exact firstCommon (firstArgument.freeSupport.get port) (firstFree port)
      (by simpa only [List.get_eq_getElem] using
        getWire.trans wireEq)
  have secondFreeEnvironment : env ∘ secondFree =
      (common ∘ payload.secondPort) ∘ secondArgument.freeSupport.get := by
    funext port
    have resolved := sequenceFin_sound secondFreeResult port
    obtain ⟨wire, occurs, getWire⟩ :=
      ConcreteElaboration.resolvePort?_sound resolved
    have wireEq : wire = reducedSecondWire input payload
        (secondArgument.freeSupport.get port) :=
      ConcreteElaboration.endpoint_wire_unique
        reducedWellFormed.wire_endpoints_are_disjoint occurs
        (by simpa [secondArgument] using
          reduced_second_free_occurs input payload position port)
    exact secondCommon (secondArgument.freeSupport.get port) (secondFree port)
      (by simpa only [List.get_eq_getElem] using
        getWire.trans wireEq)
  have firstFull : env firstOutput =
      Lambda.canonicalModel.eval
        (firstArgument.mapFree payload.firstPort) common := by
    rw [Lambda.LambdaModel.eval_mapFree]
    exact firstEquation.trans
      ((congrArg
        (fun environment =>
          Lambda.canonicalModel.eval firstArgument.compact environment)
        firstFreeEnvironment).trans
      (LambdaModel.eval_compact Lambda.canonicalModel firstArgument
        (common ∘ payload.firstPort)))
  have secondFull : env secondOutput =
      Lambda.canonicalModel.eval
        (secondArgument.mapFree payload.secondPort) common := by
    rw [Lambda.LambdaModel.eval_mapFree]
    exact secondEquation.trans
      ((congrArg
        (fun environment =>
          Lambda.canonicalModel.eval secondArgument.compact environment)
        secondFreeEnvironment).trans
      (LambdaModel.eval_compact Lambda.canonicalModel secondArgument
        (common ∘ payload.secondPort)))
  simpa [firstArgument, secondArgument] using
    firstFull.symm.trans ((congrArg env outputIndexEq).trans secondFull)

theorem reduced_original_argument_evaluations_equal
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (reducedWellFormed : (Reduced input payload).WellFormed signature)
    (context : ConcreteElaboration.WireContext (Reduced input payload))
    (binders : ConcreteElaboration.BinderContext
      (Reduced input payload) rels)
    (fuel : Nat)
    (items : ItemSeq signature context.length rels)
    (compiled : ConcreteElaboration.compileOccurrencesWith? signature
      (Reduced input payload)
      (ConcreteElaboration.compileRegion? signature (Reduced input payload) fuel)
      context binders
      (ConcreteElaboration.localOccurrences (Reduced input payload)
        payload.region) = some items)
    (exact : context.Exact payload.region)
    (named : NamedEnv Lambda.Individual signature)
    (env : Fin context.length → Lambda.Individual)
    (relEnv : RelEnv Lambda.Individual rels)
    (itemsDenote : denoteItemSeq Lambda.canonicalModel named env relEnv items)
    (common : Fin payload.commonPorts → Lambda.Individual)
    (firstCommon : ∀ port index,
      context.get index = reducedFirstWire input payload port →
        env index = common (payload.firstPort port))
    (secondCommon : ∀ port index,
      context.get index = reducedSecondWire input payload port →
        env index = common (payload.secondPort port))
    (index : Fin payload.firstOriginalSpine.args.length) :
    Lambda.canonicalModel.eval
        ((payload.firstArgument index).mapFree payload.firstPort) common =
      Lambda.canonicalModel.eval
        ((payload.secondArgument index).mapFree payload.secondPort) common := by
  by_cases same :
      (payload.firstArgument index).mapFree payload.firstPort =
        (payload.secondArgument index).mapFree payload.secondPort
  · exact congrArg (fun term => Lambda.canonicalModel.eval term common) same
  · have member : index ∈ payload.argumentIndices := by
      simp [HeadStripPayload.argumentIndices, same]
    obtain ⟨position, getPosition⟩ := List.mem_iff_get.mp member
    have positionEquality := reduced_position_evaluations_equal input payload
      reducedWellFormed context binders fuel items compiled exact named env
      relEnv itemsDenote common firstCommon secondCommon position
    rw [getPosition] at positionEquality
    exact positionEquality

theorem reduced_original_terms_equal_at
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (reducedWellFormed : (Reduced input payload).WellFormed signature)
    (context : ConcreteElaboration.WireContext (Reduced input payload))
    (binders : ConcreteElaboration.BinderContext
      (Reduced input payload) rels)
    (fuel : Nat)
    (items : ItemSeq signature context.length rels)
    (compiled : ConcreteElaboration.compileOccurrencesWith? signature
      (Reduced input payload)
      (ConcreteElaboration.compileRegion? signature (Reduced input payload) fuel)
      context binders
      (ConcreteElaboration.localOccurrences (Reduced input payload)
        payload.region) = some items)
    (exact : context.Exact payload.region)
    (named : NamedEnv Lambda.Individual signature)
    (env : Fin context.length → Lambda.Individual)
    (relEnv : RelEnv Lambda.Individual rels)
    (itemsDenote : denoteItemSeq Lambda.canonicalModel named env relEnv items)
    (common : Fin payload.commonPorts → Lambda.Individual)
    (firstCommon : ∀ port index,
      context.get index = reducedFirstWire input payload port →
        env index = common (payload.firstPort port))
    (secondCommon : ∀ port index,
      context.get index = reducedSecondWire input payload port →
        env index = common (payload.secondPort port)) :
    Lambda.canonicalModel.eval
        (payload.firstTerm.mapFree payload.firstPort) common =
      Lambda.canonicalModel.eval
        (payload.secondTerm.mapFree payload.secondPort) common := by
  apply headStrip_reflects payload.firstSpine_eq payload.secondSpine_eq
    payload.mappedSameBinders payload.headIndex payload.mappedFirstHead
    payload.mappedSecondHead payload.mappedSameArgumentCount common
  intro index valid
  let originalIndex : Fin payload.firstOriginalSpine.args.length :=
    ⟨index, by
      simpa [HeadStripPayload.firstSpine, HeadSpine.mapFree] using valid⟩
  have equality := reduced_original_argument_evaluations_equal input payload
    reducedWellFormed context binders fuel items compiled exact named env relEnv
    itemsDenote common firstCommon secondCommon originalIndex
  simpa [originalIndex, HeadStripPayload.firstSpine,
    HeadStripPayload.secondSpine, HeadSpine.mapFree,
    HeadStripPayload.firstArgument, HeadStripPayload.secondArgument,
    prefixClose_mapFree] using equality

theorem reduced_original_terms_equal
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (reducedWellFormed : (Reduced input payload).WellFormed signature)
    (context : ConcreteElaboration.WireContext (Reduced input payload))
    (binders : ConcreteElaboration.BinderContext
      (Reduced input payload) rels)
    (fuel : Nat)
    (items : ItemSeq signature context.length rels)
    (compiled : ConcreteElaboration.compileOccurrencesWith? signature
      (Reduced input payload)
      (ConcreteElaboration.compileRegion? signature (Reduced input payload) fuel)
      context binders
      (ConcreteElaboration.localOccurrences (Reduced input payload)
        payload.region) = some items)
    (exact : context.Exact payload.region)
    (named : NamedEnv Lambda.Individual signature)
    (env : Fin context.length → Lambda.Individual)
    (relEnv : RelEnv Lambda.Individual rels)
    (itemsDenote : denoteItemSeq Lambda.canonicalModel named env relEnv items) :
    ∃ common : Fin payload.commonPorts → Lambda.Individual,
      Lambda.canonicalModel.eval
          (payload.firstTerm.mapFree payload.firstPort) common =
        Lambda.canonicalModel.eval
          (payload.secondTerm.mapFree payload.secondPort) common ∧
      (∀ port index,
        context.get index = reducedFirstWire input payload port →
          env index = common (payload.firstPort port)) ∧
      (∀ port index,
        context.get index = reducedSecondWire input payload port →
          env index = common (payload.secondPort port)) := by
  obtain ⟨common, firstCommon, secondCommon⟩ :=
    reduced_common_environment input payload context exact env
  refine ⟨common, ?_, firstCommon, secondCommon⟩
  exact reduced_original_terms_equal_at input payload reducedWellFormed context
    binders fuel items compiled exact named env relEnv itemsDenote common
    firstCommon secondCommon

theorem expanded_first_original_denote
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (expandedWellFormed : (Expanded input payload).WellFormed signature)
    (context : ConcreteElaboration.WireContext (Expanded input payload))
    (binders : ConcreteElaboration.BinderContext
      (Expanded input payload) rels)
    (item : Item signature context.length rels)
    (compiled : ConcreteElaboration.compileNode? signature
      (Expanded input payload) context binders
      (Fin.castAdd (payload.argumentIndices.length +
        payload.argumentIndices.length) first) = some item)
    (common : Fin payload.commonPorts → Lambda.Individual)
    (env : Fin context.length → Lambda.Individual)
    (outputValue : ∀ index, context.get index =
        Fin.castAdd payload.argumentIndices.length payload.outputWire →
      env index = Lambda.canonicalModel.eval
        (payload.firstTerm.mapFree payload.firstPort) common)
    (freeValue : ∀ port index, context.get index =
        Fin.castAdd payload.argumentIndices.length (payload.firstWire port) →
      env index = common (payload.firstPort port))
    (named : NamedEnv Lambda.Individual signature)
    (relEnv : RelEnv Lambda.Individual rels) :
    denoteItem Lambda.canonicalModel named env relEnv item := by
  have nodeShape : (Expanded input payload).nodes
      (Fin.castAdd (payload.argumentIndices.length +
        payload.argumentIndices.length) first) =
      .term payload.region payload.firstFreePorts payload.firstTerm := by
    rw [HeadStripSoundness.headStripExpandedRaw_oldNode, payload.firstNode]
    rfl
  simp only [ConcreteElaboration.compileNode?, nodeShape] at compiled
  cases outputResult : ConcreteElaboration.resolvePort?
      (Expanded input payload) context
      (Fin.castAdd (payload.argumentIndices.length +
        payload.argumentIndices.length) first) .output with
  | none => simp [outputResult] at compiled
  | some output =>
      cases freeResult : ConcreteElaboration.resolvePorts?
          (Expanded input payload) context
          (Fin.castAdd (payload.argumentIndices.length +
            payload.argumentIndices.length) first)
          payload.firstFreePorts (fun port => .free port) with
      | none => simp [outputResult, freeResult] at compiled
      | some free =>
          simp [outputResult, freeResult] at compiled
          subst item
          obtain ⟨wire, occurs, getWire⟩ :=
            ConcreteElaboration.resolvePort?_sound outputResult
          have outputOccurs :=
            HeadStripSoundness.headStripExpandedRaw_oldEndpointOccurs_forward
              input payload payload.outputWire first .output payload.firstOutput
          have wireEq : wire =
              Fin.castAdd payload.argumentIndices.length payload.outputWire :=
            ConcreteElaboration.endpoint_wire_unique
              expandedWellFormed.wire_endpoints_are_disjoint occurs outputOccurs
          have outputEquation := outputValue output (by
            simpa only [List.get_eq_getElem] using getWire.trans wireEq)
          have freeEnvironment : env ∘ free = common ∘ payload.firstPort := by
            funext port
            have resolved := sequenceFin_sound freeResult port
            obtain ⟨freeWire, freeOccurs, freeGet⟩ :=
              ConcreteElaboration.resolvePort?_sound resolved
            have canonicalOccurs :=
              HeadStripSoundness.headStripExpandedRaw_oldEndpointOccurs_forward
                input payload (payload.firstWire port) first (.free port)
                (payload.firstWire_occurs port)
            have freeWireEq : freeWire = Fin.castAdd
                payload.argumentIndices.length (payload.firstWire port) :=
              ConcreteElaboration.endpoint_wire_unique
                expandedWellFormed.wire_endpoints_are_disjoint freeOccurs
                canonicalOccurs
            exact freeValue port (free port) (by
              simpa only [List.get_eq_getElem] using
                freeGet.trans freeWireEq)
          rw [denoteItem_equation, outputEquation,
            Lambda.LambdaModel.eval_mapFree,
            Lambda.LambdaModel.eval_mapFree]
          exact congrArg
            (fun environment =>
              Lambda.canonicalModel.eval payload.firstTerm environment)
            freeEnvironment.symm

theorem expanded_second_original_denote
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (expandedWellFormed : (Expanded input payload).WellFormed signature)
    (context : ConcreteElaboration.WireContext (Expanded input payload))
    (binders : ConcreteElaboration.BinderContext
      (Expanded input payload) rels)
    (item : Item signature context.length rels)
    (compiled : ConcreteElaboration.compileNode? signature
      (Expanded input payload) context binders
      (Fin.castAdd (payload.argumentIndices.length +
        payload.argumentIndices.length) second) = some item)
    (common : Fin payload.commonPorts → Lambda.Individual)
    (env : Fin context.length → Lambda.Individual)
    (outputValue : ∀ index, context.get index =
        Fin.castAdd payload.argumentIndices.length payload.outputWire →
      env index = Lambda.canonicalModel.eval
        (payload.secondTerm.mapFree payload.secondPort) common)
    (freeValue : ∀ port index, context.get index =
        Fin.castAdd payload.argumentIndices.length (payload.secondWire port) →
      env index = common (payload.secondPort port))
    (named : NamedEnv Lambda.Individual signature)
    (relEnv : RelEnv Lambda.Individual rels) :
    denoteItem Lambda.canonicalModel named env relEnv item := by
  have nodeShape : (Expanded input payload).nodes
      (Fin.castAdd (payload.argumentIndices.length +
        payload.argumentIndices.length) second) =
      .term payload.region payload.secondFreePorts payload.secondTerm := by
    rw [HeadStripSoundness.headStripExpandedRaw_oldNode, payload.secondNode]
    rfl
  simp only [ConcreteElaboration.compileNode?, nodeShape] at compiled
  cases outputResult : ConcreteElaboration.resolvePort?
      (Expanded input payload) context
      (Fin.castAdd (payload.argumentIndices.length +
        payload.argumentIndices.length) second) .output with
  | none => simp [outputResult] at compiled
  | some output =>
      cases freeResult : ConcreteElaboration.resolvePorts?
          (Expanded input payload) context
          (Fin.castAdd (payload.argumentIndices.length +
            payload.argumentIndices.length) second)
          payload.secondFreePorts (fun port => .free port) with
      | none => simp [outputResult, freeResult] at compiled
      | some free =>
          simp [outputResult, freeResult] at compiled
          subst item
          obtain ⟨wire, occurs, getWire⟩ :=
            ConcreteElaboration.resolvePort?_sound outputResult
          have outputOccurs :=
            HeadStripSoundness.headStripExpandedRaw_oldEndpointOccurs_forward
              input payload payload.outputWire second .output payload.secondOutput
          have wireEq : wire =
              Fin.castAdd payload.argumentIndices.length payload.outputWire :=
            ConcreteElaboration.endpoint_wire_unique
              expandedWellFormed.wire_endpoints_are_disjoint occurs outputOccurs
          have outputEquation := outputValue output (by
            simpa only [List.get_eq_getElem] using getWire.trans wireEq)
          have freeEnvironment : env ∘ free = common ∘ payload.secondPort := by
            funext port
            have resolved := sequenceFin_sound freeResult port
            obtain ⟨freeWire, freeOccurs, freeGet⟩ :=
              ConcreteElaboration.resolvePort?_sound resolved
            have canonicalOccurs :=
              HeadStripSoundness.headStripExpandedRaw_oldEndpointOccurs_forward
                input payload (payload.secondWire port) second (.free port)
                (payload.secondWire_occurs port)
            have freeWireEq : freeWire = Fin.castAdd
                payload.argumentIndices.length (payload.secondWire port) :=
              ConcreteElaboration.endpoint_wire_unique
                expandedWellFormed.wire_endpoints_are_disjoint freeOccurs
                canonicalOccurs
            exact freeValue port (free port) (by
              simpa only [List.get_eq_getElem] using
                freeGet.trans freeWireEq)
          rw [denoteItem_equation, outputEquation,
            Lambda.LambdaModel.eval_mapFree,
            Lambda.LambdaModel.eval_mapFree]
          exact congrArg
            (fun environment =>
              Lambda.canonicalModel.eval payload.secondTerm environment)
            freeEnvironment.symm

noncomputable def reducedCommonEnvironment
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (context : ConcreteElaboration.WireContext (Reduced input payload))
    (exact : context.Exact payload.region)
    (env : Fin context.length → Lambda.Individual) :
    Fin payload.commonPorts → Lambda.Individual :=
  Classical.choose (reduced_common_environment input payload context exact env)

theorem reducedCommonEnvironment_first
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (context : ConcreteElaboration.WireContext (Reduced input payload))
    (exact : context.Exact payload.region)
    (env : Fin context.length → Lambda.Individual) :
    ∀ port index, context.get index = reducedFirstWire input payload port →
      env index = (reducedCommonEnvironment input payload context exact env)
        (payload.firstPort port) :=
  (Classical.choose_spec
    (reduced_common_environment input payload context exact env)).1

theorem reducedCommonEnvironment_second
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (context : ConcreteElaboration.WireContext (Reduced input payload))
    (exact : context.Exact payload.region)
    (env : Fin context.length → Lambda.Individual) :
    ∀ port index, context.get index = reducedSecondWire input payload port →
      env index = (reducedCommonEnvironment input payload context exact env)
        (payload.secondPort port) :=
  (Classical.choose_spec
    (reduced_common_environment input payload context exact env)).2

theorem expanded_regular_localOccurrences
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (region : Fin input.val.regionCount) (regular : region ≠ payload.region) :
    ConcreteElaboration.localOccurrences (Expanded input payload) region =
      (ConcreteElaboration.localOccurrences (Reduced input payload) region).map
        (expandOccurrence input payload) := by
  rw [reduced_localOccurrences_map input payload region]
  symm
  apply List.filter_eq_self.mpr
  intro occurrence member
  cases occurrence with
  | child child => rfl
  | node node =>
      have nodeRegion :=
        (ConcreteElaboration.mem_localOccurrences_node
          (Expanded input payload) region node).mp member
      simp only [keepExpandedOccurrence, decide_eq_true_eq]
      constructor
      · intro equality
        subst node
        rw [HeadStripSoundness.headStripExpandedRaw_oldNode,
          payload.firstNode] at nodeRegion
        exact regular nodeRegion.symm
      · intro equality
        subst node
        rw [HeadStripSoundness.headStripExpandedRaw_oldNode,
          payload.secondNode] at nodeRegion
        exact regular nodeRegion.symm

private theorem compileOccurrencesWith_filter_exists
    (diagram : ConcreteDiagram)
    (recurse : ∀ {rels : RelCtx},
      Fin diagram.regionCount →
      (context : ConcreteElaboration.WireContext diagram) →
      ConcreteElaboration.BinderContext diagram rels →
      Option (Region signature context.length rels))
    (context : ConcreteElaboration.WireContext diagram)
    (binders : ConcreteElaboration.BinderContext diagram rels)
    (keep : ConcreteElaboration.LocalOccurrence diagram.regionCount
      diagram.nodeCount → Bool) :
    ∀ occurrences items,
      ConcreteElaboration.compileOccurrencesWith? signature diagram recurse
        context binders occurrences = some items →
      ∃ keptItems, ConcreteElaboration.compileOccurrencesWith? signature
        diagram recurse context binders (occurrences.filter keep) =
          some keptItems := by
  intro occurrences
  induction occurrences with
  | nil =>
      intro items compiled
      exact ⟨.nil, by simpa [ConcreteElaboration.compileOccurrencesWith?]⟩
  | cons occurrence rest induction =>
      intro items compiled
      simp only [ConcreteElaboration.compileOccurrencesWith?] at compiled
      cases headResult : ConcreteElaboration.compileOccurrenceWith? signature
          diagram recurse context binders occurrence with
      | none => simp [headResult] at compiled
      | some head =>
          cases tailResult : ConcreteElaboration.compileOccurrencesWith?
              signature diagram recurse context binders rest with
          | none => simp [headResult, tailResult] at compiled
          | some tail =>
              obtain ⟨keptTail, keptTailCompiled⟩ := induction tail tailResult
              cases kept : keep occurrence with
              | false =>
                  refine ⟨keptTail, ?_⟩
                  simp [kept, keptTailCompiled]
              | true =>
                  refine ⟨.cons head keptTail, ?_⟩
                  simp [List.filter_cons, kept,
                    ConcreteElaboration.compileOccurrencesWith?, headResult,
                    keptTailCompiled]

theorem childOccurrence_simulation
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (reducedWellFormed : (Reduced input payload).WellFormed signature)
    (expandedWellFormed : (Expanded input payload).WellFormed signature)
    (named : NamedEnv Lambda.Individual signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (sourceContext : ConcreteElaboration.WireContext (Reduced input payload))
    (targetContext : ConcreteElaboration.WireContext (Expanded input payload))
    (embedding : ContextEmbedding input payload targetContext sourceContext)
    (sourceBinders : ConcreteElaboration.BinderContext
      (Reduced input payload) sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (Expanded input payload) targetRels)
    (binderWitness : ConcreteElaboration.IdentityBinderWitness
      (Reduced input payload) (Expanded input payload)
      sourceBinders targetBinders)
    (sourceBindersCover : sourceBinders.Covers payload.region)
    (targetBindersCover : targetBinders.Covers payload.region)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (Reduced input payload) sourceBinders payload.region)
    (targetEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (Expanded input payload) targetBinders payload.region)
    (recurse : ∀ {childDirection : ConcreteElaboration.SimulationDirection}
      {child : Fin input.val.regionCount}
      {childSourceRels childTargetRels : RelCtx}
      {childSourceBinders : ConcreteElaboration.BinderContext
        (Reduced input payload) childSourceRels}
      {childTargetBinders : ConcreteElaboration.BinderContext
        (Expanded input payload) childTargetRels}
      {sourceBody : Region signature sourceContext.length childSourceRels}
      {targetBody : Region signature targetContext.length childTargetRels},
      ((Reduced input payload).regions child).parent? = some payload.region →
      ((Expanded input payload).regions child).parent? = some payload.region →
      True →
      (childBinderWitness : ConcreteElaboration.IdentityBinderWitness
        (Reduced input payload) (Expanded input payload)
        childSourceBinders childTargetBinders) →
      childSourceBinders.Covers child →
      childTargetBinders.Covers child →
      ConcreteElaboration.BinderContext.Enumeration
        (Reduced input payload) childSourceBinders child →
      ConcreteElaboration.BinderContext.Enumeration
        (Expanded input payload) childTargetBinders child →
      ConcreteElaboration.compileRegion? signature (Reduced input payload)
        fuelSource child sourceContext childSourceBinders = some sourceBody →
      ConcreteElaboration.compileRegion? signature (Expanded input payload)
        fuelTarget child targetContext childTargetBinders = some targetBody →
      ConcreteElaboration.RegionSimulation Lambda.canonicalModel named
        childDirection
        (ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index)
        (sourceBody.renameRelations
          (ConcreteElaboration.IdentityBinderWitness.relationMap
            childBinderWitness)) targetBody)
    (child : Fin input.val.regionCount)
    (parent : ((Reduced input payload).regions child).parent? =
      some payload.region)
    (sourceItem : Item signature sourceContext.length sourceRels)
    (targetItem : Item signature targetContext.length targetRels)
    (sourceCompiled : ConcreteElaboration.compileOccurrenceWith? signature
      (Reduced input payload)
      (ConcreteElaboration.compileRegion? signature (Reduced input payload)
        fuelSource) sourceContext sourceBinders (.child child) = some sourceItem)
    (targetCompiled : ConcreteElaboration.compileOccurrenceWith? signature
      (Expanded input payload)
      (ConcreteElaboration.compileRegion? signature (Expanded input payload)
        fuelTarget) targetContext targetBinders (.child child) = some targetItem) :
    ConcreteElaboration.ItemSimulation Lambda.canonicalModel named direction
      (ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index)
      (sourceItem.renameRelations
        (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness))
      targetItem := by
  have targetParent : ((Expanded input payload).regions child).parent? =
      some payload.region := parent
  cases sourceKind : (Reduced input payload).regions child with
  | sheet =>
      simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind]
        at sourceCompiled
  | cut actualParent =>
      have actualParentEq : actualParent = payload.region := by
        rw [sourceKind] at parent
        exact Option.some.inj parent
      subst actualParent
      have targetKind : (Expanded input payload).regions child =
          .cut payload.region := sourceKind
      cases sourceResult : ConcreteElaboration.compileRegion? signature
          (Reduced input payload) fuelSource child sourceContext sourceBinders with
      | none =>
          simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
            sourceResult] at sourceCompiled
      | some sourceBody =>
          simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
            sourceResult] at sourceCompiled
          subst sourceItem
          cases targetResult : ConcreteElaboration.compileRegion? signature
              (Expanded input payload) fuelTarget child targetContext
              targetBinders with
          | none =>
              simp [ConcreteElaboration.compileOccurrenceWith?, targetKind,
                targetResult] at targetCompiled
          | some targetBody =>
              simp [ConcreteElaboration.compileOccurrenceWith?, targetKind,
                targetResult] at targetCompiled
              subst targetItem
              have bodies := recurse (childDirection := direction.flip)
                parent targetParent True.intro binderWitness
                (ConcreteElaboration.BinderContext.covers_cut_child
                  sourceBindersCover sourceKind)
                (ConcreteElaboration.BinderContext.covers_cut_child
                  targetBindersCover targetKind)
                (sourceEnumeration.cutChild reducedWellFormed sourceKind)
                (targetEnumeration.cutChild expandedWellFormed targetKind)
                sourceResult targetResult
              intro sourceEnv targetEnv relEnv environments
              have bodyEntailment := bodies sourceEnv targetEnv relEnv environments
              simp only [Item.renameRelations, cut_denotes_negation]
              cases direction with
              | forward =>
                  exact fun sourceNot targetDenotes =>
                    sourceNot (bodyEntailment targetDenotes)
              | backward =>
                  exact fun targetNot sourceDenotes =>
                    targetNot (bodyEntailment sourceDenotes)
  | bubble actualParent arity =>
      have actualParentEq : actualParent = payload.region := by
        rw [sourceKind] at parent
        exact Option.some.inj parent
      subst actualParent
      have targetKind : (Expanded input payload).regions child =
          .bubble payload.region arity := sourceKind
      let sourcePushed := sourceBinders.push child arity
      let targetPushed := targetBinders.push child arity
      cases sourceResult : ConcreteElaboration.compileRegion? signature
          (Reduced input payload) fuelSource child sourceContext sourcePushed with
      | none =>
          simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
            sourcePushed, sourceResult] at sourceCompiled
      | some sourceBody =>
          simp [ConcreteElaboration.compileOccurrenceWith?, sourceKind,
            sourcePushed, sourceResult] at sourceCompiled
          subst sourceItem
          cases targetResult : ConcreteElaboration.compileRegion? signature
              (Expanded input payload) fuelTarget child targetContext
              targetPushed with
          | none =>
              simp [ConcreteElaboration.compileOccurrenceWith?, targetKind,
                targetPushed, targetResult] at targetCompiled
          | some targetBody =>
              simp [ConcreteElaboration.compileOccurrenceWith?, targetKind,
                targetPushed, targetResult] at targetCompiled
              subst targetItem
              let pushedWitness : ConcreteElaboration.IdentityBinderWitness
                  (Reduced input payload) (Expanded input payload)
                  sourcePushed targetPushed := by
                rcases binderWitness with ⟨relationContextsEq, bindersEq⟩
                subst targetRels
                cases bindersEq
                exact ⟨rfl, HEq.rfl⟩
              have bodies := recurse (childDirection := direction)
                parent targetParent True.intro pushedWitness
                (ConcreteElaboration.BinderContext.push_covers_bubble_child
                  sourceBindersCover sourceKind)
                (ConcreteElaboration.BinderContext.push_covers_bubble_child
                  targetBindersCover targetKind)
                (sourceEnumeration.bubbleChild reducedWellFormed sourceKind)
                (targetEnumeration.bubbleChild expandedWellFormed targetKind)
                sourceResult targetResult
              have pushedMap :
                  (ConcreteElaboration.IdentityBinderWitness.relationMap
                    pushedWitness : RelationRenaming (arity :: sourceRels)
                      (arity :: targetRels)) =
                    (RelationRenaming.lift
                      (ConcreteElaboration.IdentityBinderWitness.relationMap
                        binderWitness) arity :
                      RelationRenaming (arity :: sourceRels)
                        (arity :: targetRels)) := by
                cases binderWitness.relationContexts_eq
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
                  exact ⟨relationValue, bodies sourceEnv targetEnv
                    (relationValue, relEnv) environments sourceDenotes⟩
              | backward =>
                  rintro ⟨relationValue, targetDenotes⟩
                  exact ⟨relationValue, bodies sourceEnv targetEnv
                    (relationValue, relEnv) environments targetDenotes⟩

theorem keptItems_simulation
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (reducedWellFormed : (Reduced input payload).WellFormed signature)
    (expandedWellFormed : (Expanded input payload).WellFormed signature)
    (named : NamedEnv Lambda.Individual signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (sourceContext : ConcreteElaboration.WireContext (Reduced input payload))
    (targetContext : ConcreteElaboration.WireContext (Expanded input payload))
    (embedding : ContextEmbedding input payload targetContext sourceContext)
    (targetNodup : targetContext.Nodup)
    (sourceBinders : ConcreteElaboration.BinderContext
      (Reduced input payload) sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (Expanded input payload) targetRels)
    (binderWitness : ConcreteElaboration.IdentityBinderWitness
      (Reduced input payload) (Expanded input payload)
      sourceBinders targetBinders)
    (sourceBindersCover : sourceBinders.Covers payload.region)
    (targetBindersCover : targetBinders.Covers payload.region)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (Reduced input payload) sourceBinders payload.region)
    (targetEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (Expanded input payload) targetBinders payload.region)
    (recurse : ∀ {childDirection : ConcreteElaboration.SimulationDirection}
      {child : Fin input.val.regionCount}
      {childSourceRels childTargetRels : RelCtx}
      {childSourceBinders : ConcreteElaboration.BinderContext
        (Reduced input payload) childSourceRels}
      {childTargetBinders : ConcreteElaboration.BinderContext
        (Expanded input payload) childTargetRels}
      {sourceBody : Region signature sourceContext.length childSourceRels}
      {targetBody : Region signature targetContext.length childTargetRels},
      ((Reduced input payload).regions child).parent? = some payload.region →
      ((Expanded input payload).regions child).parent? = some payload.region →
      True →
      (childBinderWitness : ConcreteElaboration.IdentityBinderWitness
        (Reduced input payload) (Expanded input payload)
        childSourceBinders childTargetBinders) →
      childSourceBinders.Covers child → childTargetBinders.Covers child →
      ConcreteElaboration.BinderContext.Enumeration
        (Reduced input payload) childSourceBinders child →
      ConcreteElaboration.BinderContext.Enumeration
        (Expanded input payload) childTargetBinders child →
      ConcreteElaboration.compileRegion? signature (Reduced input payload)
        fuelSource child sourceContext childSourceBinders = some sourceBody →
      ConcreteElaboration.compileRegion? signature (Expanded input payload)
        fuelTarget child targetContext childTargetBinders = some targetBody →
      ConcreteElaboration.RegionSimulation Lambda.canonicalModel named
        childDirection
        (ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index)
        (sourceBody.renameRelations
          (ConcreteElaboration.IdentityBinderWitness.relationMap
            childBinderWitness)) targetBody)
    (sourceItems : ItemSeq signature sourceContext.length sourceRels)
    (targetItems : ItemSeq signature targetContext.length targetRels)
    (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (Reduced input payload)
      (ConcreteElaboration.compileRegion? signature (Reduced input payload)
        fuelSource) sourceContext sourceBinders
      (ConcreteElaboration.localOccurrences (Reduced input payload)
        payload.region) = some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (Expanded input payload)
      (ConcreteElaboration.compileRegion? signature (Expanded input payload)
        fuelTarget) targetContext targetBinders
      (ConcreteElaboration.localOccurrences (Expanded input payload)
        payload.region) = some targetItems) :
    ∃ keptItems : ItemSeq signature targetContext.length targetRels,
      ConcreteElaboration.compileOccurrencesWith? signature
        (Expanded input payload)
        (ConcreteElaboration.compileRegion? signature (Expanded input payload)
          fuelTarget) targetContext targetBinders
        ((ConcreteElaboration.localOccurrences (Expanded input payload)
          payload.region).filter (keepExpandedOccurrence input payload)) =
          some keptItems ∧
      ConcreteElaboration.ItemSeqSimulation Lambda.canonicalModel named direction
        (ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index)
        (sourceItems.renameRelations
          (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness))
        keptItems := by
  obtain ⟨keptItems, keptCompiled⟩ := compileOccurrencesWith_filter_exists
    (Expanded input payload)
    (ConcreteElaboration.compileRegion? signature (Expanded input payload)
      fuelTarget) targetContext targetBinders
    (keepExpandedOccurrence input payload)
    (ConcreteElaboration.localOccurrences (Expanded input payload)
      payload.region) targetItems targetCompiled
  refine ⟨keptItems, keptCompiled, ?_⟩
  have mappedCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (Expanded input payload)
      (ConcreteElaboration.compileRegion? signature (Expanded input payload)
        fuelTarget) targetContext targetBinders
      ((ConcreteElaboration.localOccurrences (Reduced input payload)
        payload.region).map (expandOccurrence input payload)) =
        some keptItems := by
    rw [reduced_localOccurrences_map input payload payload.region]
    exact keptCompiled
  apply ConcreteElaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
    Lambda.canonicalModel named direction
    (ConcreteElaboration.compileRegion? signature (Reduced input payload)
      fuelSource)
    (ConcreteElaboration.compileRegion? signature (Expanded input payload)
      fuelTarget)
    sourceContext targetContext sourceBinders targetBinders
    (ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index)
    (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness)
    (expandOccurrence input payload)
    (ConcreteElaboration.localOccurrences (Reduced input payload)
      payload.region) ?_ sourceItems keptItems sourceCompiled mappedCompiled
  intro occurrence member sourceItem targetItem sourceOccurrence targetOccurrence
  cases occurrence with
  | node node =>
      simp only [ConcreteElaboration.compileOccurrenceWith?, expandOccurrence]
        at sourceOccurrence targetOccurrence
      have mappedCompile := compileNode_expand input payload expandedWellFormed
        sourceContext targetContext embedding targetNodup
        sourceBinders targetBinders binderWitness node
      rw [sourceOccurrence] at mappedCompile
      simp only [Option.map_some] at mappedCompile
      rw [targetOccurrence] at mappedCompile
      have itemEq : targetItem =
          (sourceItem.renameWires embedding.index).renameRelations
            (ConcreteElaboration.IdentityBinderWitness.relationMap
              binderWitness) := Option.some.inj mappedCompile
      subst targetItem
      intro sourceEnv targetEnv relEnv environments
      have environmentEq : sourceEnv = targetEnv ∘ embedding.index :=
        (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
          embedding.index sourceEnv targetEnv).mp environments
      rw [environmentEq]
      have wireSemantic := denoteItem_renameWires Lambda.canonicalModel named
        embedding.index targetEnv relEnv
        (sourceItem.renameRelations
          (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness))
      cases direction with
      | forward =>
          simpa only [Item.renameWires_renameRelations] using wireSemantic.mpr
      | backward =>
          simpa only [Item.renameWires_renameRelations] using wireSemantic.mp
  | child child =>
      have parent :=
        (ConcreteElaboration.mem_localOccurrences_child
          (Reduced input payload) payload.region child).mp member
      exact childOccurrence_simulation input payload reducedWellFormed
        expandedWellFormed named direction fuelSource fuelTarget sourceContext
        targetContext embedding sourceBinders targetBinders binderWitness
        sourceBindersCover targetBindersCover sourceEnumeration targetEnumeration
        recurse child parent sourceItem targetItem sourceOccurrence
        (by simpa [expandOccurrence] using targetOccurrence)

noncomputable def focusedOutputExtendedIndex
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (context : ConcreteElaboration.WireContext (Expanded input payload)) :
    Fin (context.extend payload.region).length :=
  Fin.cast (ConcreteElaboration.WireContext.length_extend
      context payload.region).symm
    (Fin.natAdd context.length (focusedOutputIndex input payload))

theorem focusedOutputExtendedIndex_get
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (context : ConcreteElaboration.WireContext (Expanded input payload)) :
    (context.extend payload.region).get
        (focusedOutputExtendedIndex input payload context) =
      Fin.castAdd payload.argumentIndices.length payload.outputWire := by
  have localGet := ConcreteElaboration.WireContext.extend_local context
    payload.region (focusedOutputIndex input payload)
  rw [show (context.extend payload.region).get
      (focusedOutputExtendedIndex input payload context) =
        (ConcreteElaboration.exactScopeWires (Expanded input payload)
          payload.region).get (focusedOutputIndex input payload) by
    simpa [focusedOutputExtendedIndex] using localGet]
  exact focusedOutputIndex_get input payload

theorem focusedForward_output_value
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (context : ConcreteElaboration.WireContext (Expanded input payload))
    (outer : Fin context.length → D)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires
      (Reduced input payload) payload.region).length → D)
    (outputValue : D)
    (nodup : (context.extend payload.region).Nodup)
    (index : Fin (context.extend payload.region).length)
    (indexGet : (context.extend payload.region).get index =
      Fin.castAdd payload.argumentIndices.length payload.outputWire) :
    ConcreteElaboration.extendedEnvironment context payload.region outer
        (focusedForwardLocal input payload sourceLocal outputValue) index =
      outputValue := by
  have canonicalGet := focusedOutputExtendedIndex_get input payload context
  have indexEq : index = focusedOutputExtendedIndex input payload context := by
    apply Fin.ext
    exact (List.getElem_inj nodup).mp (by
      simpa only [List.get_eq_getElem] using indexGet.trans canonicalGet.symm)
  subst index
  simp [ConcreteElaboration.extendedEnvironment, focusedOutputExtendedIndex,
    Diagram.extendWireEnv, focusedForwardLocal_output]

theorem expandedOldValue_of_agreement
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (source : ConcreteElaboration.WireContext (Reduced input payload))
    (target : ConcreteElaboration.WireContext (Expanded input payload))
    (embedding : ContextEmbedding input payload target source)
    (sourceNodup : source.Nodup) (targetNodup : target.Nodup)
    (sourceEnv : Fin source.length → D)
    (targetEnv : Fin target.length → D)
    (agreement : ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
      (ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index)
      sourceEnv targetEnv)
    (wire : Fin (Reduced input payload).wireCount)
    (targetIndex : Fin target.length)
    (targetGet : target.get targetIndex = expandWire input payload wire) :
    ∃ sourceIndex : Fin source.length,
      source.get sourceIndex = wire ∧
      targetEnv targetIndex = sourceEnv sourceIndex := by
  have targetMember : expandWire input payload wire ∈ target := by
    rw [← targetGet]
    exact List.get_mem target targetIndex
  have sourceMember : wire ∈ source := (embedding.mem wire).mp targetMember
  obtain ⟨sourceIndex, sourceLookup⟩ :=
    ConcreteElaboration.WireContext.lookup?_complete sourceMember
  have sourceGet := ConcreteElaboration.WireContext.lookup?_sound sourceLookup
  have targetIndexEq : targetIndex = embedding.index sourceIndex := by
    apply Fin.ext
    exact (List.getElem_inj targetNodup).mp (by
      simpa only [List.get_eq_getElem] using targetGet.trans
        ((embedding.get sourceIndex).trans
          (congrArg (expandWire input payload) sourceGet)).symm)
  refine ⟨sourceIndex, sourceGet, ?_⟩
  rw [targetIndexEq]
  have environmentEq :=
    (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
      embedding.index sourceEnv targetEnv).mp agreement
  exact (congrFun environmentEq sourceIndex).symm

theorem focusedLocalTransport
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (reducedWellFormed : (Reduced input payload).WellFormed signature)
    (expandedWellFormed : (Expanded input payload).WellFormed signature)
    (named : NamedEnv Lambda.Individual signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (source : ConcreteElaboration.WireContext (Reduced input payload))
    (target : ConcreteElaboration.WireContext (Expanded input payload))
    (embedding : ContextEmbedding input payload target source)
    (sourceBinders : ConcreteElaboration.BinderContext
      (Reduced input payload) sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (Expanded input payload) targetRels)
    (binderWitness : ConcreteElaboration.IdentityBinderWitness
      (Reduced input payload) (Expanded input payload)
      sourceBinders targetBinders)
    (sourceExact : (source.extend payload.region).Exact payload.region)
    (targetExact : (target.extend payload.region).Exact payload.region)
    (sourceBindersCover : sourceBinders.Covers payload.region)
    (targetBindersCover : targetBinders.Covers payload.region)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (Reduced input payload) sourceBinders payload.region)
    (targetEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (Expanded input payload) targetBinders payload.region)
    (recurse : ∀ {childDirection : ConcreteElaboration.SimulationDirection}
      {child : Fin input.val.regionCount}
      {childSourceRels childTargetRels : RelCtx}
      {childSourceBinders : ConcreteElaboration.BinderContext
        (Reduced input payload) childSourceRels}
      {childTargetBinders : ConcreteElaboration.BinderContext
        (Expanded input payload) childTargetRels}
      {sourceBody : Region signature
        (source.extend payload.region).length childSourceRels}
      {targetBody : Region signature
        (target.extend payload.region).length childTargetRels},
      ((Reduced input payload).regions child).parent? = some payload.region →
      ((Expanded input payload).regions child).parent? = some payload.region →
      True →
      (childBinderWitness : ConcreteElaboration.IdentityBinderWitness
        (Reduced input payload) (Expanded input payload)
        childSourceBinders childTargetBinders) →
      childSourceBinders.Covers child → childTargetBinders.Covers child →
      ConcreteElaboration.BinderContext.Enumeration
        (Reduced input payload) childSourceBinders child →
      ConcreteElaboration.BinderContext.Enumeration
        (Expanded input payload) childTargetBinders child →
      ConcreteElaboration.compileRegion? signature (Reduced input payload)
        fuelSource child (source.extend payload.region) childSourceBinders =
          some sourceBody →
      ConcreteElaboration.compileRegion? signature (Expanded input payload)
        fuelTarget child (target.extend payload.region) childTargetBinders =
          some targetBody →
      ConcreteElaboration.RegionSimulation Lambda.canonicalModel named
        childDirection
        (ConcreteElaboration.ContextIndexRelation.forwardMap
          (embedding.extend payload.region).index)
        (sourceBody.renameRelations
          (ConcreteElaboration.IdentityBinderWitness.relationMap
            childBinderWitness)) targetBody)
    (sourceItems : ItemSeq signature
      (source.extend payload.region).length sourceRels)
    (targetItems : ItemSeq signature
      (target.extend payload.region).length targetRels)
    (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (Reduced input payload)
      (ConcreteElaboration.compileRegion? signature (Reduced input payload)
        fuelSource) (source.extend payload.region) sourceBinders
      (ConcreteElaboration.localOccurrences (Reduced input payload)
        payload.region) = some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (Expanded input payload)
      (ConcreteElaboration.compileRegion? signature (Expanded input payload)
        fuelTarget) (target.extend payload.region) targetBinders
      (ConcreteElaboration.localOccurrences (Expanded input payload)
        payload.region) = some targetItems) :
    ∀ relEnv, ConcreteElaboration.DirectionalLocalTransport direction
      source target payload.region payload.region
      (ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index)
      Lambda.canonicalModel named relEnv
      (sourceItems.renameRelations
        (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness))
      targetItems := by
  have targetRelsEq : targetRels = sourceRels :=
    binderWitness.relationContexts_eq.symm
  subst targetRels
  have relationMapEq :
      (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness :
        RelationRenaming sourceRels sourceRels) =
      (ConcreteElaboration.identityRelationRenaming sourceRels :
        RelationRenaming sourceRels sourceRels) := by
    exact HeadStripSoundness.identityBinderWitness_relationMap_eq_identity
      binderWitness
  have sourceRename : sourceItems.renameRelations
      (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness) =
      sourceItems := by
    rw [relationMapEq]
    exact HeadStripSoundness.renameRelations_identityRelationRenaming sourceItems
  rw [sourceRename]
  obtain ⟨keptItems, keptCompiled, keptSimulation⟩ := keptItems_simulation
    input payload reducedWellFormed expandedWellFormed named direction fuelSource
    fuelTarget (source.extend payload.region) (target.extend payload.region)
    (embedding.extend payload.region) targetExact.nodup sourceBinders
    targetBinders binderWitness sourceBindersCover targetBindersCover
    sourceEnumeration targetEnumeration recurse sourceItems targetItems
    sourceCompiled targetCompiled
  have keptSimulation' : ConcreteElaboration.ItemSeqSimulation
      Lambda.canonicalModel named direction
      (ConcreteElaboration.ContextIndexRelation.forwardMap
        (embedding.extend payload.region).index)
      sourceItems keptItems := by
    simpa [sourceRename] using keptSimulation
  intro relEnv sourceOuter targetOuter outerAgreement
  have outerEq : sourceOuter = targetOuter ∘ embedding.index :=
    (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
      embedding.index sourceOuter targetOuter).mp outerAgreement
  cases direction with
  | forward =>
      intro sourceLocal sourceDenotes
      let sourceEnv := ConcreteElaboration.extendedEnvironment source
        payload.region sourceOuter sourceLocal
      let common := reducedCommonEnvironment input payload
        (source.extend payload.region) sourceExact sourceEnv
      let outputValue := Lambda.canonicalModel.eval
        (payload.firstTerm.mapFree payload.firstPort) common
      let targetLocal := focusedForwardLocal input payload sourceLocal outputValue
      let targetEnv := ConcreteElaboration.extendedEnvironment target
        payload.region targetOuter targetLocal
      have extendedAgreement :
          ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
            (ConcreteElaboration.ContextIndexRelation.forwardMap
              (embedding.extend payload.region).index) sourceEnv targetEnv := by
        apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
          (embedding.extend payload.region).index _ _).mpr
        exact extendedEnvironments_agree input payload target source embedding
          payload.region targetExact.nodup sourceOuter targetOuter outerEq
          sourceLocal targetLocal
          (focusedForwardLocal_agrees input payload sourceLocal outputValue)
      have keptDenotes := keptSimulation' sourceEnv targetEnv relEnv
        extendedAgreement (by simpa [sourceEnv] using sourceDenotes)
      have firstCommon := reducedCommonEnvironment_first input payload
        (source.extend payload.region) sourceExact sourceEnv
      have secondCommon := reducedCommonEnvironment_second input payload
        (source.extend payload.region) sourceExact sourceEnv
      have originalTermsEqual := reduced_original_terms_equal_at input payload
        reducedWellFormed (source.extend payload.region) sourceBinders
        fuelSource sourceItems
        sourceCompiled sourceExact named sourceEnv relEnv sourceDenotes common
        firstCommon secondCommon
      have outputFirst : ∀ index, (target.extend payload.region).get index =
          Fin.castAdd payload.argumentIndices.length payload.outputWire →
        targetEnv index = Lambda.canonicalModel.eval
          (payload.firstTerm.mapFree payload.firstPort) common := by
        intro index get
        exact focusedForward_output_value input payload target targetOuter
          sourceLocal outputValue targetExact.nodup index get
      have outputSecond : ∀ index,
          (target.extend payload.region).get index =
          Fin.castAdd payload.argumentIndices.length payload.outputWire →
        targetEnv index = Lambda.canonicalModel.eval
          (payload.secondTerm.mapFree payload.secondPort) common := by
        intro index get
        exact (outputFirst index get).trans originalTermsEqual
      have firstFree : ∀ port index,
          (target.extend payload.region).get index =
          Fin.castAdd payload.argumentIndices.length (payload.firstWire port) →
        targetEnv index = common (payload.firstPort port) := by
        intro port index get
        have mapped : expandWire input payload
            (reducedFirstWire input payload port) =
            Fin.castAdd payload.argumentIndices.length
              (payload.firstWire port) := by
          unfold reducedFirstWire
          exact expandWire_reducedOldWire input payload _ _
        obtain ⟨sourceIndex, sourceGet, valueEq⟩ :=
          expandedOldValue_of_agreement input payload
            (source.extend payload.region) (target.extend payload.region)
            (embedding.extend payload.region)
            sourceExact.nodup targetExact.nodup sourceEnv targetEnv
            extendedAgreement (reducedFirstWire input payload port) index
            (get.trans mapped.symm)
        exact valueEq.trans (firstCommon port sourceIndex sourceGet)
      have secondFree : ∀ port index,
          (target.extend payload.region).get index =
          Fin.castAdd payload.argumentIndices.length (payload.secondWire port) →
        targetEnv index = common (payload.secondPort port) := by
        intro port index get
        have mapped : expandWire input payload
            (reducedSecondWire input payload port) =
            Fin.castAdd payload.argumentIndices.length
              (payload.secondWire port) := by
          unfold reducedSecondWire
          exact expandWire_reducedOldWire input payload _ _
        obtain ⟨sourceIndex, sourceGet, valueEq⟩ :=
          expandedOldValue_of_agreement input payload
            (source.extend payload.region) (target.extend payload.region)
            (embedding.extend payload.region)
            sourceExact.nodup targetExact.nodup sourceEnv targetEnv
            extendedAgreement (reducedSecondWire input payload port) index
            (get.trans mapped.symm)
        exact valueEq.trans (secondCommon port sourceIndex sourceGet)
      refine ⟨targetLocal, ?_⟩
      apply InstantiationSemantic.compileOccurrencesWith_filter_denotes
        (Expanded input payload)
        (ConcreteElaboration.compileRegion? signature (Expanded input payload)
          fuelTarget) (target.extend payload.region) targetBinders
        (keepExpandedOccurrence input payload) Lambda.canonicalModel named
        targetEnv relEnv
        (ConcreteElaboration.localOccurrences (Expanded input payload)
          payload.region) targetItems keptItems targetCompiled keptCompiled
        ?_ keptDenotes
      intro occurrence member rejected item compiledOccurrence
      cases occurrence with
      | child child => simp [keepExpandedOccurrence] at rejected
      | node node =>
          simp only [keepExpandedOccurrence, decide_eq_false_iff_not,
            Bool.false_eq_true] at rejected
          have selected : node = Fin.castAdd
                (payload.argumentIndices.length +
                  payload.argumentIndices.length) first ∨
              node = Fin.castAdd
                (payload.argumentIndices.length +
                  payload.argumentIndices.length) second := by
            by_cases firstSelected : node = Fin.castAdd
                (payload.argumentIndices.length +
                  payload.argumentIndices.length) first
            · exact Or.inl firstSelected
            · by_cases secondSelected : node = Fin.castAdd
                  (payload.argumentIndices.length +
                    payload.argumentIndices.length) second
              · exact Or.inr secondSelected
              · exact False.elim (rejected ⟨firstSelected, secondSelected⟩)
          rcases selected with firstEq | secondEq
          · subst node
            exact expanded_first_original_denote input payload
              expandedWellFormed (target.extend payload.region) targetBinders item
              (by simpa [ConcreteElaboration.compileOccurrenceWith?] using
                compiledOccurrence)
              common targetEnv outputFirst firstFree named relEnv
          · subst node
            exact expanded_second_original_denote input payload
              expandedWellFormed (target.extend payload.region) targetBinders item
              (by simpa [ConcreteElaboration.compileOccurrenceWith?] using
                compiledOccurrence)
              common targetEnv outputSecond secondFree named relEnv
  | backward =>
      intro targetLocal targetDenotes
      let sourceLocal := targetLocal ∘
        (localEmbedding input payload payload.region).index
      let sourceEnv := ConcreteElaboration.extendedEnvironment source
        payload.region sourceOuter sourceLocal
      let targetEnv := ConcreteElaboration.extendedEnvironment target
        payload.region targetOuter targetLocal
      have extendedAgreement :
          ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
            (ConcreteElaboration.ContextIndexRelation.forwardMap
              (embedding.extend payload.region).index) sourceEnv targetEnv := by
        apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
          (embedding.extend payload.region).index _ _).mpr
        exact extendedEnvironments_agree input payload target source embedding
          payload.region targetExact.nodup sourceOuter targetOuter outerEq
          sourceLocal targetLocal rfl
      have keptDenotes :=
        InstantiationSemantic.compileOccurrencesWith_filter_denotes_of_all
          (Expanded input payload)
          (ConcreteElaboration.compileRegion? signature
            (Expanded input payload) fuelTarget)
          (target.extend payload.region) targetBinders
          (keepExpandedOccurrence input payload) Lambda.canonicalModel named
          targetEnv relEnv
          (ConcreteElaboration.localOccurrences (Expanded input payload)
            payload.region) targetItems keptItems targetCompiled keptCompiled
          targetDenotes
      refine ⟨sourceLocal, ?_⟩
      simpa [sourceEnv] using
        (keptSimulation' sourceEnv targetEnv relEnv extendedAgreement
          keptDenotes)

noncomputable def semanticSimulation
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (reducedWellFormed : (Reduced input payload).WellFormed signature)
    (expandedWellFormed : (Expanded input payload).WellFormed signature)
    (named : NamedEnv Lambda.Individual signature) :
    ConcreteElaboration.ConcreteSemanticSimulation signature
      (Reduced input payload) (Expanded input payload)
      Lambda.canonicalModel named where
  source_wellFormed := reducedWellFormed
  target_wellFormed := expandedWellFormed
  regionMap := id
  binderMap := id
  Distinguished := fun region => region = payload.region
  occurrenceMap := fun _ _ occurrence => expandOccurrence input payload occurrence
  occurrenceMap_node := by
    intro region regular node nodeRegion
    exact ⟨expandNode input payload node, rfl⟩
  occurrenceMap_child := by simp [expandOccurrence]
  root_eq := rfl
  region_shape := by
    intro parent regular child childParent
    cases kind : (Reduced input payload).regions child <;>
      simpa [Reduced, Expanded, headStripRaw, headStripExpandedRaw, kind]
  localOccurrences_map := by
    intro region regular
    exact expanded_regular_localOccurrences input payload region regular
  BinderWitness := fun {sourceRels targetRels} sourceBinders targetBinders =>
    ConcreteElaboration.IdentityBinderWitness
      (Reduced input payload) (Expanded input payload)
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
  ContextWitness := fun source target =>
    ContextEmbedding input payload target source
  AtRegion := fun _ _ => True
  indexRelation := fun embedding =>
    ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index
  extendContext := by
    intro source target embedding region regular sourceExact targetExact
    exact embedding.extend region
  extendFocusedContext := by
    intro source target embedding region atRegion focused sourceExact targetExact
    exact embedding.extend region
  at_child := by simp
  at_extended := by simp
  at_focused_child := by simp
  localTransport := by
    intro sourceRels targetRels direction fuelSource fuelTarget source target
      embedding sourceBinders targetBinders binderWitness region atRegion regular
      allowed sourceExact targetExact sourceBindersCover targetBindersCover
      sourceEnumeration targetEnumeration sourceItems targetItems sourceCompiled
      targetCompiled itemSemantics
    exact ConcreteElaboration.directionalLocalTransport_of_agreement direction
      source target region region
      (ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index)
      (ConcreteElaboration.ContextIndexRelation.forwardMap
        (embedding.extend region).index)
      Lambda.canonicalModel named
      (sourceItems.renameRelations
        (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness))
      targetItems
      (regularLocalSelection input payload direction target source embedding
        region regular targetExact Lambda.canonicalModel)
      itemSemantics
  nodeSemantic := by
    intro sourceRels targetRels direction region source target embedding atRegion
      sourceNodup targetNodup sourceBinders targetBinders allowed binderWitness
      sourceNode targetNode regular mapped nodeRegion sourceItem targetItem
      sourceCompiled targetCompiled
    have targetNodeEq : targetNode = expandNode input payload sourceNode :=
      ConcreteElaboration.LocalOccurrence.node.inj mapped.symm
    subst targetNode
    have mappedCompile := compileNode_expand input payload expandedWellFormed
      source target embedding targetNodup sourceBinders targetBinders
      binderWitness sourceNode
    rw [sourceCompiled] at mappedCompile
    simp only [Option.map_some] at mappedCompile
    rw [targetCompiled] at mappedCompile
    have itemEq : targetItem =
        (sourceItem.renameWires embedding.index).renameRelations
          (ConcreteElaboration.IdentityBinderWitness.relationMap
            binderWitness) := Option.some.inj mappedCompile
    subst targetItem
    intro sourceEnv targetEnv relEnv environments
    have environmentEq : sourceEnv = targetEnv ∘ embedding.index :=
      (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
        embedding.index sourceEnv targetEnv).mp environments
    rw [environmentEq]
    have wireSemantic := denoteItem_renameWires Lambda.canonicalModel named
      embedding.index targetEnv relEnv
      (sourceItem.renameRelations
        (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness))
    cases direction with
    | forward =>
        simpa only [Item.renameWires_renameRelations] using wireSemantic.mpr
    | backward =>
        simpa only [Item.renameWires_renameRelations] using wireSemantic.mp
  focusedRegionKernel := by
    intro sourceRels targetRels direction fuelSource fuelTarget region source
      target embedding sourceBinders targetBinders atRegion focused allowed
      binderWitness sourceExact targetExact sourceBindersCover
      targetBindersCover sourceEnumeration targetEnumeration recurse recurseAt
      sourceItems targetItems sourceCompiled targetCompiled
    subst region
    rw [ConcreteElaboration.finishRegion_renameRelations source payload.region
      (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness)
      sourceItems]
    apply ConcreteElaboration.finishRegion_denote direction source target
      payload.region payload.region
      (ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index)
      Lambda.canonicalModel named
      (sourceItems.renameRelations
        (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness))
      targetItems
    exact focusedLocalTransport input payload reducedWellFormed
      expandedWellFormed named direction fuelSource fuelTarget source target
      embedding sourceBinders targetBinders binderWitness sourceExact targetExact
      sourceBindersCover targetBindersCover sourceEnumeration targetEnumeration
      recurse sourceItems targetItems sourceCompiled targetCompiled

end HeadStripCompaction

end VisualProof.Rule
