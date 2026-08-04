import VisualProof.Rule.Soundness.Equational.HeadStripCompaction.LocalSemantic

namespace VisualProof.Rule

open VisualProof
open Lambda
open VisualProof.Data.Finite
open Diagram
open Theory

namespace HeadStripCompaction

def reducedOpen
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (boundary : List (Fin (Reduced input payload).wireCount)) :
    OpenConcreteDiagram where
  diagram := Reduced input payload
  boundary := boundary

def expandedOpen
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (boundary : List (Fin (Reduced input payload).wireCount)) :
    OpenConcreteDiagram where
  diagram := Expanded input payload
  boundary := boundary.map (expandWire input payload)

def reducedCheckedOpen
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (reducedWellFormed : (Reduced input payload).WellFormed signature)
    (boundary : List (Fin (Reduced input payload).wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      ((Reduced input payload).wires wire).scope =
        (Reduced input payload).root) : CheckedOpenDiagram signature :=
  ⟨reducedOpen input payload boundary, reducedWellFormed, boundaryRoot⟩

def expandedCheckedOpen
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (expandedWellFormed : (Expanded input payload).WellFormed signature)
    (boundary : List (Fin (Reduced input payload).wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      ((Reduced input payload).wires wire).scope =
        (Reduced input payload).root) : CheckedOpenDiagram signature :=
  ⟨expandedOpen input payload boundary, expandedWellFormed, by
    intro wire member
    obtain ⟨raw, rawMember, rfl⟩ := List.mem_map.mp member
    exact (expandWire_scope input payload raw).trans
      (boundaryRoot raw rawMember)⟩

noncomputable def exposedEmbedding
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (boundary : List (Fin (Reduced input payload).wireCount)) :
    ContextEmbedding input payload
      (expandedOpen input payload boundary).exposedWires
      (reducedOpen input payload boundary).exposedWires :=
  ContextEmbedding.ofMem (by
    intro wire
    constructor
    · intro member
      have boundaryMember :=
        (OpenConcreteDiagram.mem_exposedWires
          (expandedOpen input payload boundary)
          (expandWire input payload wire)).mp member
      change expandWire input payload wire ∈
        boundary.map (expandWire input payload) at boundaryMember
      obtain ⟨raw, rawMember, equality⟩ := List.mem_map.mp boundaryMember
      apply (OpenConcreteDiagram.mem_exposedWires
        (reducedOpen input payload boundary) wire).mpr
      exact (expandWire_injective input payload equality).symm ▸ rawMember
    · intro member
      have boundaryMember := (OpenConcreteDiagram.mem_exposedWires
        (reducedOpen input payload boundary) wire).mp member
      apply (OpenConcreteDiagram.mem_exposedWires
        (expandedOpen input payload boundary)
        (expandWire input payload wire)).mpr
      exact List.mem_map.mpr ⟨wire, boundaryMember, rfl⟩)

noncomputable def hiddenEmbedding
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (boundary : List (Fin (Reduced input payload).wireCount)) :
    ContextEmbedding input payload
      (expandedOpen input payload boundary).hiddenWires
      (reducedOpen input payload boundary).hiddenWires :=
  ContextEmbedding.ofMem (by
    intro wire
    constructor
    · intro member
      obtain ⟨scope, notExposed⟩ :=
        (OpenConcreteDiagram.mem_hiddenWires
          (expandedOpen input payload boundary)
          (expandWire input payload wire)).mp member
      apply (OpenConcreteDiagram.mem_hiddenWires
        (reducedOpen input payload boundary) wire).mpr
      refine ⟨(expandWire_scope input payload wire).symm.trans scope, ?_⟩
      intro exposed
      exact notExposed ((exposedEmbedding input payload boundary).mem wire |>.2
        exposed)
    · intro member
      obtain ⟨scope, notExposed⟩ :=
        (OpenConcreteDiagram.mem_hiddenWires
          (reducedOpen input payload boundary) wire).mp member
      apply (OpenConcreteDiagram.mem_hiddenWires
        (expandedOpen input payload boundary)
        (expandWire input payload wire)).mpr
      refine ⟨(expandWire_scope input payload wire).trans scope, ?_⟩
      intro exposed
      exact notExposed ((exposedEmbedding input payload boundary).mem wire |>.1
        exposed))

noncomputable def rootEmbedding
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (reducedWellFormed : (Reduced input payload).WellFormed signature)
    (expandedWellFormed : (Expanded input payload).WellFormed signature)
    (boundary : List (Fin (Reduced input payload).wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      ((Reduced input payload).wires wire).scope =
        (Reduced input payload).root) :
    ContextEmbedding input payload
      (expandedOpen input payload boundary).rootWires
      (reducedOpen input payload boundary).rootWires :=
  ContextEmbedding.ofMem (by
      intro wire
      constructor
      · intro member
        have scope := (OpenConcreteDiagram.mem_rootWires_iff
          (expandedCheckedOpen input payload expandedWellFormed boundary
            boundaryRoot).val
          (expandedCheckedOpen input payload expandedWellFormed boundary
            boundaryRoot).property (expandWire input payload wire)).mp
            (by simpa using member)
        apply (OpenConcreteDiagram.mem_rootWires_iff
          (reducedCheckedOpen input payload reducedWellFormed boundary
            boundaryRoot).val
          (reducedCheckedOpen input payload reducedWellFormed boundary
            boundaryRoot).property wire).mpr
        exact (expandWire_scope input payload wire).symm.trans scope
      · intro member
        have scope := (OpenConcreteDiagram.mem_rootWires_iff
          (reducedCheckedOpen input payload reducedWellFormed boundary
            boundaryRoot).val
          (reducedCheckedOpen input payload reducedWellFormed boundary
            boundaryRoot).property wire).mp (by simpa using member)
        apply (OpenConcreteDiagram.mem_rootWires_iff
          (expandedCheckedOpen input payload expandedWellFormed boundary
            boundaryRoot).val
          (expandedCheckedOpen input payload expandedWellFormed boundary
            boundaryRoot).property (expandWire input payload wire)).mpr
        exact (expandWire_scope input payload wire).trans scope)

def rootExposedPosition (openDiagram : OpenConcreteDiagram)
    (index : Fin openDiagram.exposedWires.length) :
    Fin openDiagram.rootWires.length :=
  Fin.cast (by
    unfold OpenConcreteDiagram.rootWires
    exact List.length_append.symm)
    (Fin.castAdd openDiagram.hiddenWires.length index)

def rootHiddenPosition (openDiagram : OpenConcreteDiagram)
    (index : Fin openDiagram.hiddenWires.length) :
    Fin openDiagram.rootWires.length :=
  Fin.cast (by
    unfold OpenConcreteDiagram.rootWires
    exact List.length_append.symm)
    (Fin.natAdd openDiagram.exposedWires.length index)

@[simp] theorem rootExposedPosition_get (openDiagram : OpenConcreteDiagram)
    (index : Fin openDiagram.exposedWires.length) :
    openDiagram.rootWires.get (rootExposedPosition openDiagram index) =
      openDiagram.exposedWires.get index := by
  simp [rootExposedPosition, OpenConcreteDiagram.rootWires,
    List.get_eq_getElem, List.getElem_append_left]

@[simp] theorem rootHiddenPosition_get (openDiagram : OpenConcreteDiagram)
    (index : Fin openDiagram.hiddenWires.length) :
    openDiagram.rootWires.get (rootHiddenPosition openDiagram index) =
      openDiagram.hiddenWires.get index := by
  simp [rootHiddenPosition, OpenConcreteDiagram.rootWires,
    List.get_eq_getElem, List.getElem_append_right]

@[simp] theorem rootEnvironment_exposed
    (openDiagram : OpenConcreteDiagram)
    (outer : Fin openDiagram.exposedWires.length → D)
    (locals : Fin openDiagram.hiddenWires.length → D)
    (index : Fin openDiagram.exposedWires.length) :
    ConcreteElaboration.rootEnvironment openDiagram.exposedWires
        openDiagram.hiddenWires outer locals
        (rootExposedPosition openDiagram index) = outer index := by
  unfold ConcreteElaboration.rootEnvironment
  simp only [Function.comp_apply]
  have position : Fin.cast (by exact List.length_append)
      (rootExposedPosition openDiagram index) =
      Fin.castAdd openDiagram.hiddenWires.length index := by
    apply Fin.ext
    rfl
  calc
    Diagram.extendWireEnv outer locals
        (Fin.cast (by exact List.length_append)
          (rootExposedPosition openDiagram index)) =
        Diagram.extendWireEnv outer locals
          (Fin.castAdd openDiagram.hiddenWires.length index) :=
      congrArg (Diagram.extendWireEnv outer locals) position
    _ = outer index := by simp [Diagram.extendWireEnv]

@[simp] theorem rootEnvironment_hidden
    (openDiagram : OpenConcreteDiagram)
    (outer : Fin openDiagram.exposedWires.length → D)
    (locals : Fin openDiagram.hiddenWires.length → D)
    (index : Fin openDiagram.hiddenWires.length) :
    ConcreteElaboration.rootEnvironment openDiagram.exposedWires
        openDiagram.hiddenWires outer locals
        (rootHiddenPosition openDiagram index) = locals index := by
  unfold ConcreteElaboration.rootEnvironment
  simp only [Function.comp_apply]
  have position : Fin.cast (by exact List.length_append)
      (rootHiddenPosition openDiagram index) =
      Fin.natAdd openDiagram.exposedWires.length index := by
    apply Fin.ext
    rfl
  calc
    Diagram.extendWireEnv outer locals
        (Fin.cast (by exact List.length_append)
          (rootHiddenPosition openDiagram index)) =
        Diagram.extendWireEnv outer locals
          (Fin.natAdd openDiagram.exposedWires.length index) :=
      congrArg (Diagram.extendWireEnv outer locals) position
    _ = locals index := by simp [Diagram.extendWireEnv]

theorem rootEmbedding_index_exposed
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (reducedWellFormed : (Reduced input payload).WellFormed signature)
    (expandedWellFormed : (Expanded input payload).WellFormed signature)
    (boundary : List (Fin (Reduced input payload).wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      ((Reduced input payload).wires wire).scope =
        (Reduced input payload).root)
    (index : Fin (reducedOpen input payload boundary).exposedWires.length) :
    (rootEmbedding input payload reducedWellFormed expandedWellFormed boundary
        boundaryRoot).index
        (rootExposedPosition (reducedOpen input payload boundary) index) =
      rootExposedPosition (expandedOpen input payload boundary)
        ((exposedEmbedding input payload boundary).index index) := by
  let embedding := rootEmbedding input payload reducedWellFormed
    expandedWellFormed boundary boundaryRoot
  apply Fin.ext
  apply (List.getElem_inj
    (i := (embedding.index
      (rootExposedPosition (reducedOpen input payload boundary) index)).val)
    (j := (rootExposedPosition (expandedOpen input payload boundary)
      ((exposedEmbedding input payload boundary).index index)).val)
    (expandedOpen input payload boundary).rootWires_nodup).mp
  have mapped := embedding.get
    (rootExposedPosition (reducedOpen input payload boundary) index)
  have exposedMapped := (exposedEmbedding input payload boundary).get index
  have sourceGet := rootExposedPosition_get
    (reducedOpen input payload boundary) index
  have targetGet := rootExposedPosition_get
    (expandedOpen input payload boundary)
    ((exposedEmbedding input payload boundary).index index)
  have wireEq := mapped.trans
    ((congrArg (expandWire input payload) sourceGet).trans
      (exposedMapped.symm.trans targetGet.symm))
  simpa only [List.get_eq_getElem] using wireEq

theorem rootEmbedding_index_hidden
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (reducedWellFormed : (Reduced input payload).WellFormed signature)
    (expandedWellFormed : (Expanded input payload).WellFormed signature)
    (boundary : List (Fin (Reduced input payload).wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      ((Reduced input payload).wires wire).scope =
        (Reduced input payload).root)
    (index : Fin (reducedOpen input payload boundary).hiddenWires.length) :
    (rootEmbedding input payload reducedWellFormed expandedWellFormed boundary
        boundaryRoot).index
        (rootHiddenPosition (reducedOpen input payload boundary) index) =
      rootHiddenPosition (expandedOpen input payload boundary)
        ((hiddenEmbedding input payload boundary).index index) := by
  let embedding := rootEmbedding input payload reducedWellFormed
    expandedWellFormed boundary boundaryRoot
  apply Fin.ext
  apply (List.getElem_inj
    (i := (embedding.index
      (rootHiddenPosition (reducedOpen input payload boundary) index)).val)
    (j := (rootHiddenPosition (expandedOpen input payload boundary)
      ((hiddenEmbedding input payload boundary).index index)).val)
    (expandedOpen input payload boundary).rootWires_nodup).mp
  have mapped := embedding.get
    (rootHiddenPosition (reducedOpen input payload boundary) index)
  have hiddenMapped := (hiddenEmbedding input payload boundary).get index
  have sourceGet := rootHiddenPosition_get
    (reducedOpen input payload boundary) index
  have targetGet := rootHiddenPosition_get
    (expandedOpen input payload boundary)
    ((hiddenEmbedding input payload boundary).index index)
  have wireEq := mapped.trans
    ((congrArg (expandWire input payload) sourceGet).trans
      (hiddenMapped.symm.trans targetGet.symm))
  simpa only [List.get_eq_getElem] using wireEq

theorem rootEnvironments_agree
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (reducedWellFormed : (Reduced input payload).WellFormed signature)
    (expandedWellFormed : (Expanded input payload).WellFormed signature)
    (boundary : List (Fin (Reduced input payload).wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      ((Reduced input payload).wires wire).scope =
        (Reduced input payload).root)
    (sourceOuter : Fin
      (reducedOpen input payload boundary).exposedWires.length → D)
    (targetOuter : Fin
      (expandedOpen input payload boundary).exposedWires.length → D)
    (sourceLocal : Fin
      (reducedOpen input payload boundary).hiddenWires.length → D)
    (targetLocal : Fin
      (expandedOpen input payload boundary).hiddenWires.length → D)
    (outerEq : sourceOuter = targetOuter ∘
      (exposedEmbedding input payload boundary).index)
    (localEq : sourceLocal = targetLocal ∘
      (hiddenEmbedding input payload boundary).index) :
    ConcreteElaboration.rootEnvironment
        (reducedOpen input payload boundary).exposedWires
        (reducedOpen input payload boundary).hiddenWires sourceOuter sourceLocal =
      ConcreteElaboration.rootEnvironment
          (expandedOpen input payload boundary).exposedWires
          (expandedOpen input payload boundary).hiddenWires targetOuter targetLocal ∘
        (rootEmbedding input payload reducedWellFormed expandedWellFormed
          boundary boundaryRoot).index := by
  funext index
  let split := Fin.cast (by exact List.length_append) index
  have recover : Fin.cast (by exact List.length_append.symm) split = index := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (motive := fun current =>
      ConcreteElaboration.rootEnvironment
          (reducedOpen input payload boundary).exposedWires
          (reducedOpen input payload boundary).hiddenWires sourceOuter sourceLocal
          (Fin.cast (by exact List.length_append.symm) current) =
        (ConcreteElaboration.rootEnvironment
            (expandedOpen input payload boundary).exposedWires
            (expandedOpen input payload boundary).hiddenWires targetOuter targetLocal ∘
          (rootEmbedding input payload reducedWellFormed expandedWellFormed
            boundary boundaryRoot).index)
          (Fin.cast (by exact List.length_append.symm) current))
    (fun exposedIndex => ?_) (fun hiddenIndex => ?_) split
  · change ConcreteElaboration.rootEnvironment
        (reducedOpen input payload boundary).exposedWires
        (reducedOpen input payload boundary).hiddenWires sourceOuter sourceLocal
        (rootExposedPosition (reducedOpen input payload boundary) exposedIndex) =
      ConcreteElaboration.rootEnvironment
        (expandedOpen input payload boundary).exposedWires
        (expandedOpen input payload boundary).hiddenWires targetOuter targetLocal
        ((rootEmbedding input payload reducedWellFormed expandedWellFormed
          boundary boundaryRoot).index
          (rootExposedPosition (reducedOpen input payload boundary) exposedIndex))
    rw [rootEmbedding_index_exposed input payload reducedWellFormed
      expandedWellFormed boundary boundaryRoot exposedIndex]
    simp only [Function.comp_apply, rootEnvironment_exposed]
    exact congrFun outerEq exposedIndex
  · change ConcreteElaboration.rootEnvironment
        (reducedOpen input payload boundary).exposedWires
        (reducedOpen input payload boundary).hiddenWires sourceOuter sourceLocal
        (rootHiddenPosition (reducedOpen input payload boundary) hiddenIndex) =
      ConcreteElaboration.rootEnvironment
        (expandedOpen input payload boundary).exposedWires
        (expandedOpen input payload boundary).hiddenWires targetOuter targetLocal
        ((rootEmbedding input payload reducedWellFormed expandedWellFormed
          boundary boundaryRoot).index
          (rootHiddenPosition (reducedOpen input payload boundary) hiddenIndex))
    rw [rootEmbedding_index_hidden input payload reducedWellFormed
      expandedWellFormed boundary boundaryRoot hiddenIndex]
    simp only [Function.comp_apply, rootEnvironment_hidden]
    exact congrFun localEq hiddenIndex

theorem hiddenEmbedding_preimage_of_not_output
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (boundary : List (Fin (Reduced input payload).wireCount))
    (index : Fin (expandedOpen input payload boundary).hiddenWires.length)
    (notOutput : (expandedOpen input payload boundary).hiddenWires.get index ≠
      Fin.castAdd payload.argumentIndices.length payload.outputWire) :
    ∃ reducedIndex,
      (hiddenEmbedding input payload boundary).index reducedIndex = index := by
  let expandedWire :=
    (expandedOpen input payload boundary).hiddenWires.get index
  obtain ⟨reducedWire, expandedEq⟩ :=
    expandedWire_preimage input payload expandedWire notOutput
  have expandedMember : expandWire input payload reducedWire ∈
      (expandedOpen input payload boundary).hiddenWires := by
    rw [expandedEq]
    exact List.get_mem _ index
  have reducedMember : reducedWire ∈
      (reducedOpen input payload boundary).hiddenWires :=
    ((hiddenEmbedding input payload boundary).mem reducedWire).mp expandedMember
  obtain ⟨reducedIndex, reducedLookup⟩ :=
    ConcreteElaboration.WireContext.lookup?_complete reducedMember
  have reducedGet := ConcreteElaboration.WireContext.lookup?_sound reducedLookup
  refine ⟨reducedIndex, ?_⟩
  apply Fin.ext
  exact (List.getElem_inj
    (expandedOpen input payload boundary).hiddenWires_nodup).mp (by
      simpa only [List.get_eq_getElem] using
        ((hiddenEmbedding input payload boundary).get reducedIndex).trans
          ((congrArg (expandWire input payload) reducedGet).trans expandedEq))

noncomputable def rootFocusedInverseIndex
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (boundary : List (Fin (Reduced input payload).wireCount))
    (index : Fin (expandedOpen input payload boundary).hiddenWires.length)
    (notOutput : (expandedOpen input payload boundary).hiddenWires.get index ≠
      Fin.castAdd payload.argumentIndices.length payload.outputWire) :
    Fin (reducedOpen input payload boundary).hiddenWires.length :=
  Classical.choose
    (hiddenEmbedding_preimage_of_not_output input payload boundary index notOutput)

theorem rootFocusedInverseIndex_spec
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (boundary : List (Fin (Reduced input payload).wireCount))
    (index : Fin (expandedOpen input payload boundary).hiddenWires.length)
    (notOutput : (expandedOpen input payload boundary).hiddenWires.get index ≠
      Fin.castAdd payload.argumentIndices.length payload.outputWire) :
    (hiddenEmbedding input payload boundary).index
        (rootFocusedInverseIndex input payload boundary index notOutput) = index :=
  Classical.choose_spec
    (hiddenEmbedding_preimage_of_not_output input payload boundary index notOutput)

noncomputable def rootFocusedForwardLocal
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (boundary : List (Fin (Reduced input payload).wireCount))
    (sourceLocal : Fin
      (reducedOpen input payload boundary).hiddenWires.length → D)
    (outputValue : D) : Fin
      (expandedOpen input payload boundary).hiddenWires.length → D :=
  fun index =>
    if output : (expandedOpen input payload boundary).hiddenWires.get index =
        Fin.castAdd payload.argumentIndices.length payload.outputWire then
      outputValue
    else
      sourceLocal
        (rootFocusedInverseIndex input payload boundary index output)

theorem rootFocusedForwardLocal_agrees
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (boundary : List (Fin (Reduced input payload).wireCount))
    (sourceLocal : Fin
      (reducedOpen input payload boundary).hiddenWires.length → D)
    (outputValue : D) :
    sourceLocal = rootFocusedForwardLocal input payload boundary sourceLocal
      outputValue ∘ (hiddenEmbedding input payload boundary).index := by
  funext index
  have mappedGet := (hiddenEmbedding input payload boundary).get index
  have notOutput : (expandedOpen input payload boundary).hiddenWires.get
        ((hiddenEmbedding input payload boundary).index index) ≠
      Fin.castAdd payload.argumentIndices.length payload.outputWire := by
    intro equality
    exact expandWire_not_output input payload _
      (mappedGet.symm.trans equality)
  have recovered := ContextEmbedding.index_injective
    (hiddenEmbedding input payload boundary)
    (reducedOpen input payload boundary).hiddenWires_nodup
    (rootFocusedInverseIndex_spec input payload boundary
      ((hiddenEmbedding input payload boundary).index index) notOutput)
  change sourceLocal index = rootFocusedForwardLocal input payload boundary
    sourceLocal outputValue ((hiddenEmbedding input payload boundary).index index)
  unfold rootFocusedForwardLocal
  rw [dif_neg notOutput]
  exact congrArg sourceLocal recovered.symm

noncomputable def rootFocusedOutputIndex
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (boundary : List (Fin (Reduced input payload).wireCount))
    (rootSite : input.val.root = payload.region) :
    Fin (expandedOpen input payload boundary).hiddenWires.length :=
  Classical.choose (ConcreteElaboration.WireContext.lookup?_complete (by
    apply (OpenConcreteDiagram.mem_hiddenWires
      (expandedOpen input payload boundary) _).mpr
    constructor
    · change ((Expanded input payload).wires
          (Fin.castAdd payload.argumentIndices.length payload.outputWire)).scope =
        (Expanded input payload).root
      simpa [Expanded, headStripExpandedRaw, rootSite] using
        payload.noAdditionalExistentialAttachment
    · intro exposed
      have boundaryMember := (OpenConcreteDiagram.mem_exposedWires
        (expandedOpen input payload boundary) _).mp exposed
      change Fin.castAdd payload.argumentIndices.length payload.outputWire ∈
        boundary.map (expandWire input payload) at boundaryMember
      obtain ⟨wire, _, equality⟩ := List.mem_map.mp boundaryMember
      exact expandWire_not_output input payload wire equality))

theorem rootFocusedOutputIndex_get
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (boundary : List (Fin (Reduced input payload).wireCount))
    (rootSite : input.val.root = payload.region) :
    (expandedOpen input payload boundary).hiddenWires.get
        (rootFocusedOutputIndex input payload boundary rootSite) =
      Fin.castAdd payload.argumentIndices.length payload.outputWire :=
  ConcreteElaboration.WireContext.lookup?_sound (Classical.choose_spec
    (ConcreteElaboration.WireContext.lookup?_complete (by
      apply (OpenConcreteDiagram.mem_hiddenWires
        (expandedOpen input payload boundary) _).mpr
      constructor
      · change ((Expanded input payload).wires
            (Fin.castAdd payload.argumentIndices.length payload.outputWire)).scope =
          (Expanded input payload).root
        simpa [Expanded, headStripExpandedRaw, rootSite] using
          payload.noAdditionalExistentialAttachment
      · intro exposed
        have boundaryMember := (OpenConcreteDiagram.mem_exposedWires
          (expandedOpen input payload boundary) _).mp exposed
        change Fin.castAdd payload.argumentIndices.length payload.outputWire ∈
          boundary.map (expandWire input payload) at boundaryMember
        obtain ⟨wire, _, equality⟩ := List.mem_map.mp boundaryMember
        exact expandWire_not_output input payload wire equality)))

@[simp] theorem rootFocusedForwardLocal_output
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (boundary : List (Fin (Reduced input payload).wireCount))
    (rootSite : input.val.root = payload.region)
    (sourceLocal : Fin
      (reducedOpen input payload boundary).hiddenWires.length → D)
    (outputValue : D) :
    rootFocusedForwardLocal input payload boundary sourceLocal outputValue
        (rootFocusedOutputIndex input payload boundary rootSite) = outputValue := by
  unfold rootFocusedForwardLocal
  rw [dif_pos (rootFocusedOutputIndex_get input payload boundary rootSite)]

theorem hiddenEmbedding_surjective_regular
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (boundary : List (Fin (Reduced input payload).wireCount))
    (regular : input.val.root ≠ payload.region)
    (index : Fin (expandedOpen input payload boundary).hiddenWires.length) :
    ∃ reducedIndex,
      (hiddenEmbedding input payload boundary).index reducedIndex = index := by
  have hiddenMember := (OpenConcreteDiagram.mem_hiddenWires
    (expandedOpen input payload boundary)
    ((expandedOpen input payload boundary).hiddenWires.get index)).mp
      (List.get_mem _ index)
  have notOutput : (expandedOpen input payload boundary).hiddenWires.get index ≠
      Fin.castAdd payload.argumentIndices.length payload.outputWire := by
    intro equality
    have scopeEq := congrArg
      (fun wire => ((Expanded input payload).wires wire).scope) equality
    have outputScope : ((Expanded input payload).wires
        (Fin.castAdd payload.argumentIndices.length payload.outputWire)).scope =
        payload.region := by
      simpa [Expanded, headStripExpandedRaw] using
        payload.noAdditionalExistentialAttachment
    have hiddenMemberScope := hiddenMember.1
    change ((Expanded input payload).wires
        ((expandedOpen input payload boundary).hiddenWires.get index)).scope =
      (Expanded input payload).root at hiddenMemberScope
    have hiddenScope : ((Expanded input payload).wires
        ((expandedOpen input payload boundary).hiddenWires.get index)).scope =
        input.val.root := by
      simpa [Expanded, headStripExpandedRaw] using hiddenMemberScope
    exact regular (hiddenScope.symm.trans (scopeEq.trans outputScope))
  exact hiddenEmbedding_preimage_of_not_output input payload boundary index notOutput

noncomputable def rootRegularInverseIndex
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (boundary : List (Fin (Reduced input payload).wireCount))
    (regular : input.val.root ≠ payload.region)
    (index : Fin (expandedOpen input payload boundary).hiddenWires.length) :
    Fin (reducedOpen input payload boundary).hiddenWires.length :=
  Classical.choose
    (hiddenEmbedding_surjective_regular input payload boundary regular index)

theorem rootRegularInverseIndex_spec
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (boundary : List (Fin (Reduced input payload).wireCount))
    (regular : input.val.root ≠ payload.region)
    (index : Fin (expandedOpen input payload boundary).hiddenWires.length) :
    (hiddenEmbedding input payload boundary).index
        (rootRegularInverseIndex input payload boundary regular index) = index :=
  Classical.choose_spec
    (hiddenEmbedding_surjective_regular input payload boundary regular index)

theorem regularRootSelection
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (reducedWellFormed : (Reduced input payload).WellFormed signature)
    (expandedWellFormed : (Expanded input payload).WellFormed signature)
    (boundary : List (Fin (Reduced input payload).wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      ((Reduced input payload).wires wire).scope =
        (Reduced input payload).root)
    (regular : input.val.root ≠ payload.region)
    (direction : ConcreteElaboration.SimulationDirection) :
    ∀ (sourceOuter : Fin
        (reducedOpen input payload boundary).exposedWires.length → D)
      (targetOuter : Fin
        (expandedOpen input payload boundary).exposedWires.length → D),
      ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
        (ConcreteElaboration.ContextIndexRelation.forwardMap
          (exposedEmbedding input payload boundary).index)
        sourceOuter targetOuter →
      match direction with
      | .forward => ∀ sourceLocal,
          ∃ targetLocal,
            ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
              (ConcreteElaboration.ContextIndexRelation.forwardMap
                (rootEmbedding input payload reducedWellFormed expandedWellFormed
                  boundary boundaryRoot).index)
              (ConcreteElaboration.rootEnvironment
                (reducedOpen input payload boundary).exposedWires
                (reducedOpen input payload boundary).hiddenWires
                sourceOuter sourceLocal)
              (ConcreteElaboration.rootEnvironment
                (expandedOpen input payload boundary).exposedWires
                (expandedOpen input payload boundary).hiddenWires
                targetOuter targetLocal)
      | .backward => ∀ targetLocal,
          ∃ sourceLocal,
            ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
              (ConcreteElaboration.ContextIndexRelation.forwardMap
                (rootEmbedding input payload reducedWellFormed expandedWellFormed
                  boundary boundaryRoot).index)
              (ConcreteElaboration.rootEnvironment
                (reducedOpen input payload boundary).exposedWires
                (reducedOpen input payload boundary).hiddenWires
                sourceOuter sourceLocal)
              (ConcreteElaboration.rootEnvironment
                (expandedOpen input payload boundary).exposedWires
                (expandedOpen input payload boundary).hiddenWires
                targetOuter targetLocal) := by
  intro sourceOuter targetOuter outerAgreement
  have outerEq : sourceOuter = targetOuter ∘
      (exposedEmbedding input payload boundary).index :=
    (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
      _ _ _).mp outerAgreement
  cases direction with
  | forward =>
      intro sourceLocal
      let targetLocal := fun index => sourceLocal
        (rootRegularInverseIndex input payload boundary regular index)
      have localEq : sourceLocal = targetLocal ∘
          (hiddenEmbedding input payload boundary).index := by
        funext index
        have mapped := rootRegularInverseIndex_spec input payload boundary regular
          ((hiddenEmbedding input payload boundary).index index)
        have recovered := ContextEmbedding.index_injective
          (hiddenEmbedding input payload boundary)
          (reducedOpen input payload boundary).hiddenWires_nodup mapped
        simp [targetLocal, recovered]
      refine ⟨targetLocal, ?_⟩
      apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
        _ _ _).mpr
      exact rootEnvironments_agree input payload reducedWellFormed
        expandedWellFormed boundary boundaryRoot sourceOuter targetOuter
        sourceLocal targetLocal outerEq localEq
  | backward =>
      intro targetLocal
      let sourceLocal := targetLocal ∘
        (hiddenEmbedding input payload boundary).index
      refine ⟨sourceLocal, ?_⟩
      apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
        _ _ _).mpr
      exact rootEnvironments_agree input payload reducedWellFormed
        expandedWellFormed boundary boundaryRoot sourceOuter targetOuter
        sourceLocal targetLocal outerEq rfl

theorem rootFocused_output_value
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (expandedWellFormed : (Expanded input payload).WellFormed signature)
    (boundary : List (Fin (Reduced input payload).wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      ((Reduced input payload).wires wire).scope =
        (Reduced input payload).root)
    (rootSite : input.val.root = payload.region)
    (targetOuter : Fin
      (expandedOpen input payload boundary).exposedWires.length → D)
    (sourceLocal : Fin
      (reducedOpen input payload boundary).hiddenWires.length → D)
    (outputValue : D)
    (index : Fin (expandedOpen input payload boundary).rootWires.length)
    (indexGet : (expandedOpen input payload boundary).rootWires.get index =
      Fin.castAdd payload.argumentIndices.length payload.outputWire) :
    ConcreteElaboration.rootEnvironment
        (expandedOpen input payload boundary).exposedWires
        (expandedOpen input payload boundary).hiddenWires targetOuter
        (rootFocusedForwardLocal input payload boundary sourceLocal outputValue)
        index = outputValue := by
  let outputIndex := rootFocusedOutputIndex input payload boundary rootSite
  have canonicalGet : (expandedOpen input payload boundary).rootWires.get
      (rootHiddenPosition (expandedOpen input payload boundary) outputIndex) =
      Fin.castAdd payload.argumentIndices.length payload.outputWire := by
    rw [rootHiddenPosition_get]
    exact rootFocusedOutputIndex_get input payload boundary rootSite
  have indexEq : index = rootHiddenPosition
      (expandedOpen input payload boundary) outputIndex := by
    apply Fin.ext
    exact (List.getElem_inj
      (expandedCheckedOpen input payload expandedWellFormed boundary
        boundaryRoot).val.rootWires_nodup).mp (by
          simpa only [List.get_eq_getElem] using indexGet.trans canonicalGet.symm)
  subst index
  simp [outputIndex]

theorem focusedRootTransport
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (reducedWellFormed : (Reduced input payload).WellFormed signature)
    (expandedWellFormed : (Expanded input payload).WellFormed signature)
    (boundary : List (Fin (Reduced input payload).wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      ((Reduced input payload).wires wire).scope =
        (Reduced input payload).root)
    (named : NamedEnv Lambda.Individual signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (rootSite : input.val.root = payload.region)
    (recurse : ∀ {childDirection : ConcreteElaboration.SimulationDirection}
      {child : Fin input.val.regionCount}
      {childSourceRels childTargetRels : RelCtx}
      {childSourceBinders : ConcreteElaboration.BinderContext
        (Reduced input payload) childSourceRels}
      {childTargetBinders : ConcreteElaboration.BinderContext
        (Expanded input payload) childTargetRels}
      {sourceBody : Region signature
        (reducedOpen input payload boundary).rootWires.length childSourceRels}
      {targetBody : Region signature
        (expandedOpen input payload boundary).rootWires.length childTargetRels},
      ((Reduced input payload).regions child).parent? = some input.val.root →
      ((Expanded input payload).regions child).parent? = some input.val.root →
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
          (Reduced input payload).regionCount child
          (reducedOpen input payload boundary).rootWires childSourceBinders =
        some sourceBody →
      ConcreteElaboration.compileRegion? signature (Expanded input payload)
          (Expanded input payload).regionCount child
          (expandedOpen input payload boundary).rootWires childTargetBinders =
        some targetBody →
      ConcreteElaboration.RegionSimulation Lambda.canonicalModel named
        childDirection
        (ConcreteElaboration.ContextIndexRelation.forwardMap
          (rootEmbedding input payload reducedWellFormed expandedWellFormed
            boundary boundaryRoot).index)
        (sourceBody.renameRelations
          (ConcreteElaboration.IdentityBinderWitness.relationMap
            childBinderWitness)) targetBody)
    (sourceItems : ItemSeq signature
      (reducedOpen input payload boundary).rootWires.length [])
    (targetItems : ItemSeq signature
      (expandedOpen input payload boundary).rootWires.length [])
    (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (Reduced input payload)
      (ConcreteElaboration.compileRegion? signature (Reduced input payload)
        (Reduced input payload).regionCount)
      (reducedOpen input payload boundary).rootWires
      ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences (Reduced input payload)
        input.val.root) = some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (Expanded input payload)
      (ConcreteElaboration.compileRegion? signature (Expanded input payload)
        (Expanded input payload).regionCount)
      (expandedOpen input payload boundary).rootWires
      ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences (Expanded input payload)
        input.val.root) = some targetItems) :
    ConcreteElaboration.DirectionalRootTransport direction
      (reducedOpen input payload boundary).exposedWires
      (reducedOpen input payload boundary).hiddenWires
      (expandedOpen input payload boundary).exposedWires
      (expandedOpen input payload boundary).hiddenWires
      (ConcreteElaboration.ContextIndexRelation.forwardMap
        (exposedEmbedding input payload boundary).index)
      Lambda.canonicalModel named sourceItems targetItems := by
  let sourceContext := (reducedOpen input payload boundary).rootWires
  let targetContext := (expandedOpen input payload boundary).rootWires
  let embedding := rootEmbedding input payload reducedWellFormed
    expandedWellFormed boundary boundaryRoot
  have sourceCompiledFocus : ConcreteElaboration.compileOccurrencesWith? signature
      (Reduced input payload)
      (ConcreteElaboration.compileRegion? signature (Reduced input payload)
        (Reduced input payload).regionCount) sourceContext
      ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences (Reduced input payload)
        payload.region) = some sourceItems := by
    simpa [sourceContext, rootSite] using sourceCompiled
  have targetCompiledFocus : ConcreteElaboration.compileOccurrencesWith? signature
      (Expanded input payload)
      (ConcreteElaboration.compileRegion? signature (Expanded input payload)
        (Expanded input payload).regionCount) targetContext
      ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences (Expanded input payload)
        payload.region) = some targetItems := by
    simpa [targetContext, rootSite] using targetCompiled
  have sourceExact : ConcreteElaboration.WireContext.Exact sourceContext
      payload.region := by
    rw [← rootSite]
    exact ConcreteElaboration.openRootWires_exact
      (reducedCheckedOpen input payload reducedWellFormed boundary
        boundaryRoot).property
  have targetExact : ConcreteElaboration.WireContext.Exact targetContext
      payload.region := by
    rw [← rootSite]
    exact ConcreteElaboration.openRootWires_exact
      (expandedCheckedOpen input payload expandedWellFormed boundary
        boundaryRoot).property
  have sourceCover :
      (ConcreteElaboration.BinderContext.empty :
        ConcreteElaboration.BinderContext (Reduced input payload) []).Covers
          payload.region := by
    rw [← rootSite]
    exact ConcreteElaboration.BinderContext.empty_covers_root reducedWellFormed
  have targetCover :
      (ConcreteElaboration.BinderContext.empty :
        ConcreteElaboration.BinderContext (Expanded input payload) []).Covers
          payload.region := by
    rw [← rootSite]
    exact ConcreteElaboration.BinderContext.empty_covers_root expandedWellFormed
  have sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (Reduced input payload) ConcreteElaboration.BinderContext.empty
      payload.region := by
    rw [← rootSite]
    exact ConcreteElaboration.BinderContext.Enumeration.empty _
  have targetEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (Expanded input payload) ConcreteElaboration.BinderContext.empty
      payload.region := by
    rw [← rootSite]
    exact ConcreteElaboration.BinderContext.Enumeration.empty _
  obtain ⟨keptItems, keptCompiled, keptSimulation⟩ := keptItems_simulation
    input payload reducedWellFormed expandedWellFormed named direction
    (Reduced input payload).regionCount (Expanded input payload).regionCount
    sourceContext targetContext embedding targetExact.nodup
    ConcreteElaboration.BinderContext.empty
    ConcreteElaboration.BinderContext.empty ⟨rfl, HEq.rfl⟩
    sourceCover targetCover sourceEnumeration targetEnumeration
    (by
      intro childDirection child childSourceRels childTargetRels
        childSourceBinders childTargetBinders sourceBody targetBody
        sourceParent targetParent allowed childWitness sourceCovers targetCovers
        sourceEnum targetEnum sourceResult targetResult
      exact recurse (by simpa [rootSite] using sourceParent)
        (by simpa [rootSite] using targetParent) allowed childWitness
        sourceCovers targetCovers sourceEnum targetEnum sourceResult targetResult)
    sourceItems targetItems sourceCompiledFocus targetCompiledFocus
  have keptSimulation' : ConcreteElaboration.ItemSeqSimulation
      Lambda.canonicalModel named direction
      (ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index)
      sourceItems keptItems := by
    simpa [ConcreteElaboration.IdentityBinderWitness.relationMap,
      ConcreteElaboration.identityRelationRenaming,
      HeadStripSoundness.renameRelations_identityRelationRenaming] using
        keptSimulation
  intro sourceOuter targetOuter relEnv outerAgreement
  have outerEq : sourceOuter = targetOuter ∘
      (exposedEmbedding input payload boundary).index :=
    (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
      _ _ _).mp outerAgreement
  cases direction with
  | backward =>
      intro targetLocal targetDenotes
      let sourceLocal := targetLocal ∘
        (hiddenEmbedding input payload boundary).index
      let sourceEnv := ConcreteElaboration.rootEnvironment
        (reducedOpen input payload boundary).exposedWires
        (reducedOpen input payload boundary).hiddenWires sourceOuter sourceLocal
      let targetEnv := ConcreteElaboration.rootEnvironment
        (expandedOpen input payload boundary).exposedWires
        (expandedOpen input payload boundary).hiddenWires targetOuter targetLocal
      have completeEq := rootEnvironments_agree input payload reducedWellFormed
        expandedWellFormed boundary boundaryRoot sourceOuter targetOuter
        sourceLocal targetLocal outerEq rfl
      have completeAgrees :
          ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
            (ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index)
            sourceEnv targetEnv := by
        rw [ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
        simpa [sourceEnv, targetEnv] using completeEq
      have keptDenotes :=
        InstantiationSemantic.compileOccurrencesWith_filter_denotes_of_all
          (Expanded input payload)
          (ConcreteElaboration.compileRegion? signature (Expanded input payload)
            (Expanded input payload).regionCount)
          targetContext ConcreteElaboration.BinderContext.empty
          (keepExpandedOccurrence input payload) Lambda.canonicalModel named
          targetEnv relEnv
          (ConcreteElaboration.localOccurrences (Expanded input payload)
            payload.region) targetItems keptItems targetCompiledFocus keptCompiled
          (by simpa [targetEnv] using targetDenotes)
      refine ⟨sourceLocal, ?_⟩
      simpa [sourceEnv] using
        (keptSimulation' sourceEnv targetEnv relEnv completeAgrees keptDenotes)
  | forward =>
      intro sourceLocal sourceDenotes
      let sourceEnv := ConcreteElaboration.rootEnvironment
        (reducedOpen input payload boundary).exposedWires
        (reducedOpen input payload boundary).hiddenWires sourceOuter sourceLocal
      let common := reducedCommonEnvironment input payload sourceContext
        sourceExact sourceEnv
      let outputValue := Lambda.canonicalModel.eval
        (payload.firstTerm.mapFree payload.firstPort) common
      let targetLocal := rootFocusedForwardLocal input payload boundary
        sourceLocal outputValue
      let targetEnv := ConcreteElaboration.rootEnvironment
        (expandedOpen input payload boundary).exposedWires
        (expandedOpen input payload boundary).hiddenWires targetOuter targetLocal
      have localEq := rootFocusedForwardLocal_agrees input payload boundary
        sourceLocal outputValue
      have completeEq := rootEnvironments_agree input payload reducedWellFormed
        expandedWellFormed boundary boundaryRoot sourceOuter targetOuter
        sourceLocal targetLocal outerEq localEq
      have completeAgrees :
          ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
            (ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index)
            sourceEnv targetEnv := by
        rw [ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
        simpa [sourceEnv, targetEnv] using completeEq
      have keptDenotes := keptSimulation' sourceEnv targetEnv relEnv
        completeAgrees (by simpa [sourceEnv] using sourceDenotes)
      have firstCommon := reducedCommonEnvironment_first input payload
        sourceContext sourceExact sourceEnv
      have secondCommon := reducedCommonEnvironment_second input payload
        sourceContext sourceExact sourceEnv
      have originalTermsEqual := reduced_original_terms_equal_at input payload
        reducedWellFormed sourceContext ConcreteElaboration.BinderContext.empty
        (Reduced input payload).regionCount sourceItems sourceCompiledFocus
        sourceExact named sourceEnv relEnv (by simpa [sourceEnv] using sourceDenotes)
        common firstCommon secondCommon
      have outputFirst : ∀ index, targetContext.get index =
          Fin.castAdd payload.argumentIndices.length payload.outputWire →
        targetEnv index = Lambda.canonicalModel.eval
          (payload.firstTerm.mapFree payload.firstPort) common := by
        intro index get
        exact rootFocused_output_value input payload expandedWellFormed boundary
          boundaryRoot rootSite targetOuter sourceLocal outputValue index get
      have outputSecond : ∀ index, targetContext.get index =
          Fin.castAdd payload.argumentIndices.length payload.outputWire →
        targetEnv index = Lambda.canonicalModel.eval
          (payload.secondTerm.mapFree payload.secondPort) common := by
        intro index get
        exact (outputFirst index get).trans originalTermsEqual
      have firstFree : ∀ port index, targetContext.get index =
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
          expandedOldValue_of_agreement input payload sourceContext targetContext
            embedding sourceExact.nodup targetExact.nodup sourceEnv targetEnv
            completeAgrees (reducedFirstWire input payload port) index
            (get.trans mapped.symm)
        exact valueEq.trans (firstCommon port sourceIndex sourceGet)
      have secondFree : ∀ port index, targetContext.get index =
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
          expandedOldValue_of_agreement input payload sourceContext targetContext
            embedding sourceExact.nodup targetExact.nodup sourceEnv targetEnv
            completeAgrees (reducedSecondWire input payload port) index
            (get.trans mapped.symm)
        exact valueEq.trans (secondCommon port sourceIndex sourceGet)
      refine ⟨targetLocal, ?_⟩
      apply InstantiationSemantic.compileOccurrencesWith_filter_denotes
        (Expanded input payload)
        (ConcreteElaboration.compileRegion? signature (Expanded input payload)
          (Expanded input payload).regionCount)
        targetContext ConcreteElaboration.BinderContext.empty
        (keepExpandedOccurrence input payload) Lambda.canonicalModel named
        targetEnv relEnv
        (ConcreteElaboration.localOccurrences (Expanded input payload)
          payload.region) targetItems keptItems targetCompiledFocus keptCompiled
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
              expandedWellFormed targetContext
              ConcreteElaboration.BinderContext.empty item
              (by simpa [ConcreteElaboration.compileOccurrenceWith?] using
                compiledOccurrence)
              common targetEnv outputFirst firstFree named relEnv
          · subst node
            exact expanded_second_original_denote input payload
              expandedWellFormed targetContext
              ConcreteElaboration.BinderContext.empty item
              (by simpa [ConcreteElaboration.compileOccurrenceWith?] using
                compiledOccurrence)
              common targetEnv outputSecond secondFree named relEnv

noncomputable def rootContext
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (reducedWellFormed : (Reduced input payload).WellFormed signature)
    (expandedWellFormed : (Expanded input payload).WellFormed signature)
    (boundary : List (Fin (Reduced input payload).wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      ((Reduced input payload).wires wire).scope =
        (Reduced input payload).root)
    (named : NamedEnv Lambda.Individual signature)
    (direction : ConcreteElaboration.SimulationDirection) :
    let simulation := semanticSimulation input payload reducedWellFormed
      expandedWellFormed named
    ConcreteElaboration.ConcreteSemanticSimulation.RootContextSimulation
      simulation direction
      (reducedOpen input payload boundary).exposedWires
      (reducedOpen input payload boundary).hiddenWires
      (expandedOpen input payload boundary).exposedWires
      (expandedOpen input payload boundary).hiddenWires := by
  let simulation := semanticSimulation input payload reducedWellFormed
    expandedWellFormed named
  let embedding := rootEmbedding input payload reducedWellFormed
    expandedWellFormed boundary boundaryRoot
  refine {
    outer := ConcreteElaboration.ContextIndexRelation.forwardMap
      (exposedEmbedding input payload boundary).index
    context := ?_
    atRoot := True.intro
    atRootChild := by intros; trivial
    atFocusedRootChild := by intros; trivial
    transport := ?_
    focusedRootKernel := ?_
  }
  · simpa only [OpenConcreteDiagram.rootWires] using embedding
  · intro regular allowed sourceItems targetItems sourceCompiled targetCompiled
      itemSemantics
    refine ConcreteElaboration.directionalRootTransport_of_agreement direction
      (reducedOpen input payload boundary).exposedWires
      (reducedOpen input payload boundary).hiddenWires
      (expandedOpen input payload boundary).exposedWires
      (expandedOpen input payload boundary).hiddenWires
      (ConcreteElaboration.ContextIndexRelation.forwardMap
        (exposedEmbedding input payload boundary).index)
      (ConcreteElaboration.ContextIndexRelation.forwardMap embedding.index)
      Lambda.canonicalModel named
      (sourceItems.renameRelations
        (simulation.relationMap simulation.binders_empty))
      targetItems
      (regularRootSelection input payload reducedWellFormed expandedWellFormed
        boundary boundaryRoot regular direction) itemSemantics
  · intro atRoot distinguished allowed recurse recurseAt sourceItems targetItems
      sourceCompiled targetCompiled
    have rootSite : input.val.root = payload.region := distinguished
    have sourceCompiled' : ConcreteElaboration.compileOccurrencesWith? signature
        (Reduced input payload)
        (ConcreteElaboration.compileRegion? signature (Reduced input payload)
          (Reduced input payload).regionCount)
        (reducedOpen input payload boundary).rootWires
        ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences (Reduced input payload)
          input.val.root) = some sourceItems := by
      simpa only [OpenConcreteDiagram.rootWires] using sourceCompiled
    have targetCompiled' : ConcreteElaboration.compileOccurrencesWith? signature
        (Expanded input payload)
        (ConcreteElaboration.compileRegion? signature (Expanded input payload)
          (Expanded input payload).regionCount)
        (expandedOpen input payload boundary).rootWires
        ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences (Expanded input payload)
          input.val.root) = some targetItems := by
      simpa only [OpenConcreteDiagram.rootWires] using targetCompiled
    have relationMapEq :
        (fun {arity} =>
          (semanticSimulation input payload reducedWellFormed expandedWellFormed
            named).relationMap
            (semanticSimulation input payload reducedWellFormed expandedWellFormed
              named).binders_empty : RelationRenaming [] []) =
          fun {arity} relation => relation := by
      rfl
    rw [relationMapEq, Region.renameRelations_id]
    apply ConcreteElaboration.finishRoot_denote direction
      (reducedOpen input payload boundary).exposedWires
      (reducedOpen input payload boundary).hiddenWires
      (expandedOpen input payload boundary).exposedWires
      (expandedOpen input payload boundary).hiddenWires
      (ConcreteElaboration.ContextIndexRelation.forwardMap
        (exposedEmbedding input payload boundary).index)
      Lambda.canonicalModel named sourceItems targetItems
    exact focusedRootTransport input payload reducedWellFormed expandedWellFormed
      boundary boundaryRoot named direction rootSite recurse sourceItems
      targetItems sourceCompiled' targetCompiled'

theorem exposedEmbedding_surjective
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (boundary : List (Fin (Reduced input payload).wireCount)) :
    Function.Surjective (exposedEmbedding input payload boundary).index := by
  intro targetIndex
  let expandedWire :=
    (expandedOpen input payload boundary).exposedWires.get targetIndex
  have boundaryMember := (OpenConcreteDiagram.mem_exposedWires
    (expandedOpen input payload boundary) expandedWire).mp
      (List.get_mem _ targetIndex)
  change expandedWire ∈ boundary.map (expandWire input payload) at boundaryMember
  obtain ⟨reducedWire, reducedBoundary, expandedEq⟩ :=
    List.mem_map.mp boundaryMember
  have reducedMember : reducedWire ∈
      (reducedOpen input payload boundary).exposedWires :=
    (OpenConcreteDiagram.mem_exposedWires
      (reducedOpen input payload boundary) reducedWire).mpr reducedBoundary
  obtain ⟨sourceIndex, sourceLookup⟩ :=
    ConcreteElaboration.WireContext.lookup?_complete reducedMember
  have sourceGet := ConcreteElaboration.WireContext.lookup?_sound sourceLookup
  refine ⟨sourceIndex, ?_⟩
  apply Fin.ext
  exact (List.getElem_inj
    (expandedOpen input payload boundary).exposedWires_nodup).mp (by
      simpa only [List.get_eq_getElem] using
        ((exposedEmbedding input payload boundary).get sourceIndex).trans
          ((congrArg (expandWire input payload) sourceGet).trans expandedEq))

noncomputable def sourceExposedIndex
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (boundary : List (Fin (Reduced input payload).wireCount)) :
    Fin (expandedOpen input payload boundary).exposedWires.length →
      Fin (reducedOpen input payload boundary).exposedWires.length :=
  fun index => Classical.choose
    (exposedEmbedding_surjective input payload boundary index)

@[simp] theorem exposedIndex_sourceExposedIndex
    (index : Fin (expandedOpen input payload boundary).exposedWires.length) :
    (exposedEmbedding input payload boundary).index
      (sourceExposedIndex input payload boundary index) = index :=
  Classical.choose_spec
    (exposedEmbedding_surjective input payload boundary index)

@[simp] theorem sourceExposedIndex_exposedIndex
    (index : Fin (reducedOpen input payload boundary).exposedWires.length) :
    sourceExposedIndex input payload boundary
      ((exposedEmbedding input payload boundary).index index) = index := by
  apply ContextEmbedding.index_injective
    (exposedEmbedding input payload boundary)
    (reducedOpen input payload boundary).exposedWires_nodup
  exact exposedIndex_sourceExposedIndex
    (input := input) (payload := payload) (boundary := boundary)
    ((exposedEmbedding input payload boundary).index index)

theorem boundaryLengthEq
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (boundary : List (Fin (Reduced input payload).wireCount)) :
    (expandedOpen input payload boundary).boundary.length =
      (reducedOpen input payload boundary).boundary.length := by
  simp [expandedOpen, reducedOpen]

theorem boundaryClass
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (boundary : List (Fin (Reduced input payload).wireCount))
    (position : Fin (reducedOpen input payload boundary).boundary.length) :
    (exposedEmbedding input payload boundary).index
        ((reducedOpen input payload boundary).boundaryClass position) =
      (expandedOpen input payload boundary).boundaryClass
        (Fin.cast (boundaryLengthEq input payload boundary).symm position) := by
  apply OpenConcreteDiagram.boundaryClass_complete
  have mapped := (exposedEmbedding input payload boundary).get
    ((reducedOpen input payload boundary).boundaryClass position)
  have sourceGet := OpenConcreteDiagram.boundaryClass_sound
    (reducedOpen input payload boundary) position
  have targetGet : (expandedOpen input payload boundary).boundary.get
        (Fin.cast (boundaryLengthEq input payload boundary).symm position) =
      expandWire input payload
        ((reducedOpen input payload boundary).boundary.get position) := by
    simp [expandedOpen, reducedOpen, List.get_eq_getElem]
  exact mapped.trans
    ((congrArg (expandWire input payload) sourceGet).trans targetGet.symm)

theorem boundaryWitness
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (reducedWellFormed : (Reduced input payload).WellFormed signature)
    (expandedWellFormed : (Expanded input payload).WellFormed signature)
    (boundary : List (Fin (Reduced input payload).wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      ((Reduced input payload).wires wire).scope =
        (Reduced input payload).root)
    (direction : ConcreteElaboration.SimulationDirection)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceArgs : Fin boundary.length → model.Carrier) :
    ConcreteElaboration.ConcreteSemanticSimulation.DirectionalBoundaryWitness
      direction
      (reducedCheckedOpen input payload reducedWellFormed boundary
        boundaryRoot).elaborate
      (expandedCheckedOpen input payload expandedWellFormed boundary
        boundaryRoot).elaborate
      (ConcreteElaboration.ContextIndexRelation.forwardMap
        (exposedEmbedding input payload boundary).index)
      model named sourceArgs
      (sourceArgs ∘ Fin.cast (boundaryLengthEq input payload boundary)) := by
  cases direction with
  | forward =>
      intro sourceAssignment sourceArgsEq sourceDenotes
      let targetAssignment : BoundaryAssignment
          (expandedCheckedOpen input payload expandedWellFormed boundary
            boundaryRoot).elaborate model.Carrier := {
        args := sourceArgs ∘ Fin.cast (boundaryLengthEq input payload boundary)
        classes := sourceAssignment.classes ∘
          sourceExposedIndex input payload boundary
        agrees := by
          intro targetPosition
          let sourcePosition := Fin.cast
            (boundaryLengthEq input payload boundary) targetPosition
          have classEq := boundaryClass input payload boundary sourcePosition
          have positionEq : Fin.cast
              (boundaryLengthEq input payload boundary).symm sourcePosition =
                targetPosition := by
            apply Fin.ext
            rfl
          rw [positionEq] at classEq
          change sourceAssignment.classes
              (sourceExposedIndex input payload boundary
                ((expandedOpen input payload boundary).boundaryClass
                  targetPosition)) = sourceArgs sourcePosition
          rw [← classEq, sourceExposedIndex_exposedIndex]
          have sourceAgrees := sourceAssignment.agrees sourcePosition
          change sourceAssignment.classes
              ((reducedOpen input payload boundary).boundaryClass sourcePosition) =
            sourceAssignment.args sourcePosition at sourceAgrees
          rw [sourceArgsEq] at sourceAgrees
          exact sourceAgrees
      }
      refine ⟨targetAssignment, rfl, ?_⟩
      apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
        _ _ _).mpr
      funext sourceClass
      simp only [targetAssignment, Function.comp_apply]
      rw [sourceExposedIndex_exposedIndex]
  | backward =>
      intro targetAssignment targetArgsEq targetDenotes
      let sourceAssignment : BoundaryAssignment
          (reducedCheckedOpen input payload reducedWellFormed boundary
            boundaryRoot).elaborate model.Carrier := {
        args := sourceArgs
        classes := targetAssignment.classes ∘
          (exposedEmbedding input payload boundary).index
        agrees := by
          intro sourcePosition
          change targetAssignment.classes
              ((exposedEmbedding input payload boundary).index
                ((reducedOpen input payload boundary).boundaryClass
                  sourcePosition)) = sourceArgs sourcePosition
          rw [boundaryClass]
          have targetAgrees := targetAssignment.agrees
            (Fin.cast (boundaryLengthEq input payload boundary).symm
              sourcePosition)
          rw [targetArgsEq] at targetAgrees
          exact targetAgrees
      }
      refine ⟨sourceAssignment, rfl, ?_⟩
      apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
        _ _ _).mpr
      rfl

theorem expandWire_of_interface_image
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second)
    (wire : Fin input.val.wireCount)
    (mapped : Fin (Reduced input payload).wireCount)
    (image : (headStripInterfaceTransport input payload).image? wire =
      some mapped) :
    expandWire input payload mapped =
      Fin.castAdd payload.argumentIndices.length wire := by
  let domain := headStripWireDomain input.val payload.outputWire
  unfold headStripInterfaceTransport InterfaceTransport.rootFiltered at image
  dsimp only at image
  cases indexResult : domain.index? wire with
  | none =>
      rw [indexResult] at image
      change (none : Option (Fin (Reduced input payload).wireCount)) =
        some mapped at image
      contradiction
  | some compact =>
      rw [indexResult] at image
      change (if ((headStripRaw input payload).wires
          (Fin.castAdd payload.argumentIndices.length compact)).scope =
          (headStripRaw input payload).root then
            some (Fin.castAdd payload.argumentIndices.length compact)
          else none) = some mapped at image
      by_cases rootScoped : ((headStripRaw input payload).wires
          (Fin.castAdd payload.argumentIndices.length compact)).scope =
          (headStripRaw input payload).root
      · rw [if_pos rootScoped] at image
        have mappedEq := Option.some.inj image
        clear image
        -- Orient the image equality for substitution.
        have image : mapped =
            Fin.castAdd payload.argumentIndices.length compact := mappedEq.symm
        subst mapped
        have origin := (domain.index?_eq_some_iff wire compact).mp indexResult
        apply Fin.ext
        simpa [expandWire, domain] using congrArg Fin.val origin
      · rw [if_neg rootScoped] at image
        contradiction

theorem expandedBoundary_of_transport
    (input : CheckedDiagram signature)
    {first second : Fin input.val.nodeCount}
    (payload : HeadStripPayload input first second) :
    ∀ (boundary : List (Fin input.val.wireCount))
      (mapped : List (Fin (Reduced input payload).wireCount)),
      (headStripInterfaceTransport input payload).transportBoundary boundary =
        some mapped →
      mapped.map (expandWire input payload) =
        boundary.map (Fin.castAdd payload.argumentIndices.length)
  | [], mapped, transport => by
      simp [InterfaceTransport.transportBoundary] at transport
      subst mapped
      rfl
  | wire :: rest, mapped, transport => by
      cases wireImage : (headStripInterfaceTransport input payload).image? wire with
      | none =>
          simp [InterfaceTransport.transportBoundary, wireImage] at transport
      | some mappedWire =>
          cases restImage :
              (headStripInterfaceTransport input payload).transportBoundary rest with
          | none =>
              simp [InterfaceTransport.transportBoundary, wireImage, restImage]
                at transport
          | some mappedRest =>
              simp [InterfaceTransport.transportBoundary, wireImage, restImage]
                at transport
              subst mapped
              rw [List.map_cons, List.map_cons,
                expandWire_of_interface_image input payload wire mappedWire
                  wireImage,
                expandedBoundary_of_transport input payload rest mappedRest restImage]
              rfl

end HeadStripCompaction

end VisualProof.Rule
