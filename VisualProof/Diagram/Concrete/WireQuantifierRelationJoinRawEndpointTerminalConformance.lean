import VisualProof.Diagram.Concrete.WireQuantifierRelationJoinRawEndpointConformance
import VisualProof.Diagram.Concrete.WireQuantifierRelationJoinRawWirePayload

namespace VisualProof

namespace ConcreteWireQuantifier

variable {definitions : List (List Sig)}
variable {source : CheckedDiagram definitions}
variable {dying : source.val.WireId}
variable {content : CheckedOpenDiagram definitions}

private theorem reindexEndpoint?_eraseNode_exact
    (step : RelationJoinStep source dying content)
    (endpoint : CEndpoint step.prior.val.nodeCount)
    (different : endpoint.node ≠ step.priorApplication) :
    ConcreteDiagram.DenseErasure.reindexEndpoint?
        (ConcreteDiagram.DenseErasure.retainedNodes step.prior.val
          [step.priorApplication]) endpoint =
      some (ConcreteDiagram.DenseErasure.eraseNodeEndpoint step.prior
        step.priorApplication endpoint different) := by
  unfold ConcreteDiagram.DenseErasure.reindexEndpoint?
    ConcreteDiagram.DenseErasure.eraseNodeEndpoint
  have member : endpoint.node ∈
      ConcreteDiagram.DenseErasure.retainedNodes step.prior.val
        [step.priorApplication] := by
    simp [ConcreteDiagram.DenseErasure.retainedNodes,
      ConcreteDiagram.nodesList, Data.Finite.mem_allFin, different]
  have foundSome :
      (Data.Finite.indexOf?
        (ConcreteDiagram.DenseErasure.retainedNodes step.prior.val
          [step.priorApplication]) endpoint.node).isSome = true :=
    Data.Finite.indexOf?_isSome_iff.mpr member
  obtain ⟨position, found⟩ := Option.isSome_iff_exists.mp foundSome
  rw [found]
  simp only [Option.map_some, Option.some.injEq]
  congr 2
  exact (Option.get_of_eq_some _ found).symm

private theorem reindex_eraseNodeEndpoints_exact
    (step : RelationJoinStep source dying content)
    (endpoints : List (CEndpoint step.prior.val.nodeCount)) :
    (endpoints.filter fun endpoint =>
        decide (endpoint.node ≠ step.priorApplication)).filterMap
        (ConcreteDiagram.DenseErasure.reindexEndpoint?
          (ConcreteDiagram.DenseErasure.retainedNodes step.prior.val
            [step.priorApplication])) =
      endpoints.filterMap fun endpoint =>
        if different : endpoint.node ≠ step.priorApplication then
          some (ConcreteDiagram.DenseErasure.eraseNodeEndpoint step.prior
            step.priorApplication endpoint different)
        else none := by
  induction endpoints with
  | nil => rfl
  | cons endpoint rest induction =>
      by_cases different : endpoint.node ≠ step.priorApplication
      · rw [List.filter_cons_of_pos (by simp [different]),
          List.filterMap_cons,
          reindexEndpoint?_eraseNode_exact step endpoint different,
          List.filterMap_cons]
        simp only [different, dite_true, Option.toList_some]
        simpa [different] using congrArg
          (List.cons
            (ConcreteDiagram.DenseErasure.eraseNodeEndpoint step.prior
              step.priorApplication endpoint different)) induction
      · rw [List.filter_cons_of_neg (by simp [different]),
          List.filterMap_cons]
        simp only [different, dite_false, Option.toList_none,
          List.nil_append]
        simpa [different] using induction

private theorem map_survivingEndpoints_exact
    (step : RelationJoinStep source dying content)
    (endpoints : List (CEndpoint step.prior.val.nodeCount)) :
    ((endpoints.filterMap fun endpoint =>
        if different : endpoint.node ≠ step.priorApplication then
          some (ConcreteDiagram.DenseErasure.eraseNodeEndpoint step.prior
            step.priorApplication endpoint different)
        else none).map (Internal.checkedEndpoint step.baseGenerated)) =
      endpoints.filterMap fun endpoint =>
        if different : endpoint.node ≠ step.priorApplication then
          some (Internal.checkedEndpoint step.baseGenerated
            (ConcreteDiagram.DenseErasure.eraseNodeEndpoint step.prior
              step.priorApplication endpoint different))
        else none := by
  induction endpoints with
  | nil => rfl
  | cons endpoint rest induction =>
      by_cases different : endpoint.node ≠ step.priorApplication
      · simp only [List.filterMap_cons]
        simpa [different] using congrArg
          (List.cons
            (Internal.checkedEndpoint step.baseGenerated
              (ConcreteDiagram.DenseErasure.eraseNodeEndpoint step.prior
                step.priorApplication endpoint different))) induction
      · simp only [List.filterMap_cons]
        simpa [different] using induction

private theorem eraseNodeWire_endpoints_exact
    (step : RelationJoinStep source dying content)
    (wire : step.prior.val.WireId) :
    ((ConcreteDiagram.DenseErasure.eraseNodeCandidate step.prior
        step.priorApplication).wires
      (ConcreteDiagram.DenseErasure.eraseNodeWire step.prior
        step.priorApplication wire)).endpoints =
      (step.prior.val.wires wire).endpoints.filterMap fun endpoint =>
        if different : endpoint.node ≠ step.priorApplication then
          some (ConcreteDiagram.DenseErasure.eraseNodeEndpoint step.prior
            step.priorApplication endpoint different)
        else none := by
  have wireExact :
      step.prior.val.wiresList.get
          (ConcreteDiagram.DenseErasure.eraseNodeWire step.prior
            step.priorApplication wire) = wire := by
    apply Fin.ext
    simp [ConcreteDiagram.DenseErasure.eraseNodeWire,
      ConcreteDiagram.wiresList, Data.Finite.allFin_eq_finRange]
  change
    ConcreteDiagram.DenseErasure.reindexEndpoints
        (ConcreteDiagram.DenseErasure.retainedNodes step.prior.val
          [step.priorApplication])
        (ConcreteDiagram.DenseErasure.eraseNodeEndpoints
          step.priorApplication
          (step.prior.val.wires
            (step.prior.val.wiresList.get
              (ConcreteDiagram.DenseErasure.eraseNodeWire step.prior
                step.priorApplication wire))).endpoints) = _
  rw [wireExact]
  unfold ConcreteDiagram.DenseErasure.eraseNodeEndpoints
    ConcreteDiagram.DenseErasure.reindexEndpoints
  exact reindex_eraseNodeEndpoints_exact step _

private theorem checkedBaseWire_endpoints_exact
    (step : RelationJoinStep source dying content)
    (wire : step.prior.val.WireId) :
    (step.base.val.wires
      (Internal.checkedWire step.baseGenerated
        (ConcreteDiagram.DenseErasure.eraseNodeWire step.prior
          step.priorApplication wire))).endpoints =
      (step.prior.val.wires wire).endpoints.filterMap fun endpoint =>
        if different : endpoint.node ≠ step.priorApplication then
          some (Internal.checkedEndpoint step.baseGenerated
            (ConcreteDiagram.DenseErasure.eraseNodeEndpoint step.prior
              step.priorApplication endpoint different))
        else none := by
  rw [Internal.checkedWire_endpoints_transport,
    eraseNodeWire_endpoints_exact]
  exact map_survivingEndpoints_exact step _

/-- Exact one-step recurrence for a transported prior wire. Surviving prior
incidences retain their order, and the splice's independent generated fiber
is appended in fragment/request order. -/
theorem RelationJoinStep.checkedPriorWire_endpoints_exact
    (step : RelationJoinStep source dying content)
    (wire : step.prior.val.WireId) :
    (step.checked.val.wires (step.checkedPriorWire wire)).endpoints =
      ((step.prior.val.wires wire).endpoints.filterMap fun endpoint =>
          if different : endpoint.node ≠ step.priorApplication then
            some (step.checkedPriorEndpoint endpoint different)
          else none) ++
        (expectedStepGeneratedEndpoints step
          (step.attachment.hostWire
            (Internal.checkedWire step.baseGenerated
              (ConcreteDiagram.DenseErasure.eraseNodeWire step.prior
                step.priorApplication wire)))).map
          (fun endpoint =>
            Internal.checkedEndpoint step.generated
              (realizeStepGeneratedEndpoint step endpoint)) := by
  change
    (step.checked.val.wires
      (Internal.checkedWire step.generated
        (step.attachment.hostWire
          (Internal.checkedWire step.baseGenerated
            (ConcreteDiagram.DenseErasure.eraseNodeWire step.prior
              step.priorApplication wire))))).endpoints = _
  rw [step.checkedAttachmentWire_endpoints]
  unfold ConcreteSpliceAttachment.diagram
    ConcreteSpliceAttachment.wireTable
    ConcreteSpliceAttachment.hostWire
  simp only [Fin.addCases_left, List.map_append]
  rw [checkedBaseWire_endpoints_exact]
  have generatedExact := checkedWire_generatedEndpoints_exact step
    (step.attachment.hostWire
      (Internal.checkedWire step.baseGenerated
        (ConcreteDiagram.DenseErasure.eraseNodeWire step.prior
          step.priorApplication wire)))
  have generatedExact' := generatedExact.symm
  unfold ConcreteSpliceAttachment.hostWire at generatedExact'
  have priorExact :
      List.map (Internal.checkedEndpoint step.generated)
          (List.map step.attachment.hostEndpoint
            ((step.prior.val.wires wire).endpoints.filterMap fun endpoint =>
              if different : endpoint.node ≠ step.priorApplication then
                some (Internal.checkedEndpoint step.baseGenerated
                  (ConcreteDiagram.DenseErasure.eraseNodeEndpoint step.prior
                    step.priorApplication endpoint different))
              else none)) =
        (step.prior.val.wires wire).endpoints.filterMap fun endpoint =>
          if different : endpoint.node ≠ step.priorApplication then
            some (step.checkedPriorEndpoint endpoint different)
          else none := by
    induction (step.prior.val.wires wire).endpoints with
    | nil => rfl
    | cons endpoint rest induction =>
        by_cases different : endpoint.node ≠ step.priorApplication
        · simp only [List.filterMap_cons]
          rw [dif_pos different, dif_pos different]
          simp only [Option.toList_some, List.map_cons, List.cons.injEq]
          exact ⟨rfl, induction⟩
        · simp only [List.filterMap_cons]
          rw [dif_neg different, dif_neg different]
          simpa using induction
  congr 1

/-- Live construction-node origins at an arbitrary accepted prefix. -/
abbrev PrefixLiveNodeOrigin
    (steps : List (RelationJoinStep source dying content)) : Type :=
  { origin : PrefixNodeOrigin (source := source) (dying := dying)
      (content := content) steps // PrefixNodeLive origin }

/-- Read one checked endpoint through the certified atlas at its prefix. -/
def CertifiedAtlas.endpointOrigin
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    (atlas : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps final)
    (endpoint : CEndpoint final.val.nodeCount) :
    RawEndpoint (PrefixLiveNodeOrigin steps) :=
  { node := ⟨atlas.rows.nodeAt endpoint.node,
      atlas.nodeRowsLive endpoint.node⟩
    port := endpoint.port }

private def prefixContentNodeOrigin
    {steps : List (RelationJoinStep source dying content)}
    (occurrence : Fin steps.length)
    (node : content.val.diagram.NodeId) : PrefixLiveNodeOrigin steps :=
  ⟨.inr ⟨occurrence, .inl node⟩, trivial⟩

private def prefixRequestNodeOrigin
    {steps : List (RelationJoinStep source dying content)}
    (occurrence : Fin steps.length)
    (request : Fin
      ((steps.get occurrence).attachment.identityRequests.length)) :
    PrefixLiveNodeOrigin steps :=
  ⟨.inr ⟨occurrence, .inr request⟩, trivial⟩

private def expectedSourceStepEndpoints
    (step : RelationJoinStep source dying content)
    (wire : source.val.WireId)
    {nodeOrigin : Type}
    (contentNode : content.val.diagram.NodeId → nodeOrigin)
    (requestNode : Fin step.attachment.identityRequests.length →
      nodeOrigin) :
    List (RawEndpoint nodeOrigin) :=
  (content.val.diagram.endpointOccurrences.filterMap fun occurrence =>
    if step.attachment.fragmentWire occurrence.1 =
        step.attachment.hostWire (step.baseWireImage wire) then
      some
        { node := contentNode occurrence.2.node
          port := occurrence.2.port }
    else none) ++
  ((Data.Finite.allFin step.attachment.identityRequests.length).flatMap
    fun request =>
      let requestData := step.attachment.identityRequests.get request
      (Data.Finite.allFin requestData.attachments.length).filterMap fun port =>
        if requestData.attachments.get port = step.baseWireImage wire then
          some
            { node := requestNode request
              port := .identity port.val }
        else none)

private theorem expectedSourceStepEndpoints_congr
    {left right : RelationJoinStep source dying content}
    (same : left = right)
    (wire : source.val.WireId)
    {nodeOrigin : Type}
    (leftContent rightContent : content.val.diagram.NodeId → nodeOrigin)
    (leftRequest : Fin left.attachment.identityRequests.length →
      nodeOrigin)
    (rightRequest : Fin right.attachment.identityRequests.length →
      nodeOrigin)
    (contentExact : ∀ node, leftContent node = rightContent node)
    (requestExact : ∀ request,
      leftRequest request = rightRequest (Fin.cast (congrArg
        (fun current : RelationJoinStep source dying content =>
          current.attachment.identityRequests.length) same) request)) :
    expectedSourceStepEndpoints left wire leftContent leftRequest =
      expectedSourceStepEndpoints right wire rightContent rightRequest := by
  subst right
  have contentFunctions : leftContent = rightContent := funext contentExact
  have requestFunctions : leftRequest = rightRequest := by
    funext request
    simpa using requestExact request
  subst rightContent
  subst rightRequest
  rfl

/-- Retained original incidences of one source wire at an arbitrary accepted
prefix. -/
def expectedPrefixSourceEndpoints
    (steps : List (RelationJoinStep source dying content))
    (wire : source.val.WireId) :
    List (RawEndpoint (PrefixLiveNodeOrigin steps)) :=
  (source.val.wires wire).endpoints.filterMap fun endpoint =>
    if survives : endpoint.node ∉ steps.map RelationJoinStep.application then
      some
        { node := ⟨.inl endpoint.node, by
            simpa [PrefixNodeLive] using survives⟩
          port := endpoint.port }
    else none

/-- Copied-fragment and generated-request contribution to a source wire at
one prefix occurrence. -/
def expectedPrefixSourceEndpointsAt
    {steps : List (RelationJoinStep source dying content)}
    (wire : source.val.WireId)
    (occurrence : Fin steps.length) :
    List (RawEndpoint (PrefixLiveNodeOrigin steps)) :=
  let step := steps.get occurrence
  expectedSourceStepEndpoints step wire
    (prefixContentNodeOrigin occurrence)
    (prefixRequestNodeOrigin occurrence)

/-- Complete construction-order endpoint fiber of a source wire at an
arbitrary accepted prefix. -/
def expectedPrefixSourceWireEndpoints
    (steps : List (RelationJoinStep source dying content))
    (wire : source.val.WireId) :
    List (RawEndpoint (PrefixLiveNodeOrigin steps)) :=
  expectedPrefixSourceEndpoints steps wire ++
    (Data.Finite.allFin steps.length).flatMap fun occurrence =>
      expectedPrefixSourceEndpointsAt wire occurrence

/-- Creation-local copied-fragment fiber of an internal wire at an arbitrary
accepted prefix. -/
def expectedPrefixInternalWireEndpoints
    {steps : List (RelationJoinStep source dying content)}
    (origin : ConstructionWireOrigin steps) :
    List (RawEndpoint (PrefixLiveNodeOrigin steps)) :=
  let descriptor := constructionWireDescriptor origin
  content.val.diagram.endpointOccurrences.filterMap fun endpointOccurrence =>
    if origin.step.attachment.fragmentWire endpointOccurrence.1 =
        origin.step.attachment.fragmentWire origin.contentWire then
      some
        { node := prefixContentNodeOrigin descriptor.occurrence
            endpointOccurrence.2.node
          port := endpointOccurrence.2.port }
    else none

/-- Independent ordered endpoint fiber for every bound construction wire. -/
def expectedPrefixWireEndpoints
    (steps : List (RelationJoinStep source dying content)) :
    source.val.WireId ⊕ ConstructionWireOrigin steps →
      List (RawEndpoint (PrefixLiveNodeOrigin steps))
  | .inl wire => expectedPrefixSourceWireEndpoints steps wire
  | .inr origin => expectedPrefixInternalWireEndpoints origin

@[simp] private theorem ConstructionWireOrigin.step_lift
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (origin : ConstructionWireOrigin steps) :
    (liftConstructionWireOrigin step origin).step = origin.step := by
  induction steps with
  | nil => exact nomatch origin
  | cons head rest induction =>
      cases origin with
      | head position => rfl
      | tail origin => exact induction origin

@[simp] private theorem ConstructionWireOrigin.step_fresh
    (steps : List (RelationJoinStep source dying content))
    (step : RelationJoinStep source dying content)
    (position : Fin step.attachment.fragmentInternalWires.length) :
    (freshConstructionWireOrigin steps step position).step = step := by
  induction steps with
  | nil => rfl
  | cons head rest induction => exact induction

private theorem constructionWireDescriptor_occurrence_lift
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (origin : ConstructionWireOrigin steps) :
    (constructionWireDescriptor
        (liftConstructionWireOrigin step origin)).occurrence =
      Fin.cast (by simp)
        (Fin.castAdd 1 (constructionWireDescriptor origin).occurrence) := by
  induction steps with
  | nil => exact nomatch origin
  | cons head rest induction =>
      cases origin with
      | head position =>
          apply Fin.ext
          rfl
      | tail origin =>
          apply Fin.ext
          have exact := congrArg Fin.val (induction origin)
          simp only [liftConstructionWireOrigin,
            constructionWireDescriptor, Fin.val_cast, Fin.val_castAdd,
            Fin.val_succ]
          exact congrArg Nat.succ exact

private theorem constructionWireDescriptor_occurrence_fresh
    (steps : List (RelationJoinStep source dying content))
    (step : RelationJoinStep source dying content)
    (position : Fin step.attachment.fragmentInternalWires.length) :
    (constructionWireDescriptor
        (freshConstructionWireOrigin steps step position)).occurrence =
      Fin.cast (by simp) (Fin.last steps.length) := by
  induction steps with
  | nil =>
      apply Fin.ext
      rfl
  | cons head rest induction =>
      apply Fin.ext
      have exact := congrArg Fin.val induction
      simp only [freshConstructionWireOrigin, constructionWireDescriptor,
        Fin.val_cast, Fin.val_last, Fin.val_succ]
      exact congrArg Nat.succ exact

private theorem ConstructionWireOrigin.fragmentWire_descriptor
    {steps : List (RelationJoinStep source dying content)}
    (origin : ConstructionWireOrigin steps)
    (wire : content.val.diagram.WireId) :
    HEq (origin.step.attachment.fragmentWire wire)
      ((steps.get (constructionWireDescriptor origin).occurrence).attachment.fragmentWire
        wire) := by
  induction steps with
  | nil => exact nomatch origin
  | cons head rest induction =>
      cases origin with
      | head position => rfl
      | tail origin => exact induction origin

private theorem ConstructionWireOrigin.fragmentWire_content_descriptor
    {steps : List (RelationJoinStep source dying content)}
    (origin : ConstructionWireOrigin steps) :
    HEq (origin.step.attachment.fragmentWire origin.contentWire)
      ((steps.get (constructionWireDescriptor origin).occurrence).attachment.freshWire
        (constructionWireDescriptor origin).position) := by
  induction steps with
  | nil => exact nomatch origin
  | cons head rest induction =>
      cases origin with
      | head position =>
          exact heq_of_eq
            (head.attachment.fragmentWire_get_fragmentInternalWires position)
      | tail origin => exact induction origin

private theorem liftNodeOrigin_live_of_live_of_ne
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (origin : PrefixNodeOrigin (source := source) (dying := dying)
      (content := content) steps)
    (priorLive : PrefixNodeLive origin)
    (different : origin ≠ .inl step.application) :
    PrefixNodeLive (liftNodeOrigin step origin) := by
  cases origin with
  | inl node =>
      simp only [PrefixNodeLive, liftNodeOrigin, List.map_append,
        List.map_singleton, List.mem_append, List.mem_singleton]
      intro member
      rcases member with priorMember | newest
      · exact priorLive priorMember
      · exact different (congrArg Sum.inl newest)
  | inr occurrence =>
      rcases occurrence with ⟨occurrence, node⟩
      cases node <;> trivial

/-- Lift one live endpoint origin through a newest construction step, dropping
exactly the source application consumed by that step. -/
def liftPrefixEndpoint?
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (endpoint : RawEndpoint (PrefixLiveNodeOrigin steps)) :
    Option (RawEndpoint (PrefixLiveNodeOrigin (steps ++ [step]))) :=
  if different : endpoint.node.1 ≠ .inl step.application then
    some
      { node := ⟨liftNodeOrigin step endpoint.node.1,
          liftNodeOrigin_live_of_live_of_ne step endpoint.node.1
            endpoint.node.2 different⟩
        port := endpoint.port }
  else none

private theorem expectedPrefixSourceEndpoints_snoc
    (steps : List (RelationJoinStep source dying content))
    (step : RelationJoinStep source dying content)
    (wire : source.val.WireId) :
    (expectedPrefixSourceEndpoints steps wire).filterMap
        (liftPrefixEndpoint? step) =
      expectedPrefixSourceEndpoints (steps ++ [step]) wire := by
  unfold expectedPrefixSourceEndpoints
  induction (source.val.wires wire).endpoints with
  | nil => rfl
  | cons endpoint endpoints induction =>
      simp only [List.filterMap_cons]
      by_cases priorSurvives :
          endpoint.node ∉ steps.map RelationJoinStep.application
      · rw [dif_pos priorSurvives]
        simp only [Option.toList_some, List.filterMap_cons]
        by_cases newestSurvives : endpoint.node ≠ step.application
        · have extendedSurvives :
              endpoint.node ∉
                (steps ++ [step]).map RelationJoinStep.application := by
              simp [List.map_append, priorSurvives, newestSurvives]
          have originDifferent :
              (Sum.inl endpoint.node :
                PrefixNodeOrigin (source := source) (dying := dying)
                  (content := content) steps) ≠
                .inl step.application := by
              simpa using newestSurvives
          rw [dif_pos extendedSurvives]
          unfold liftPrefixEndpoint?
          rw [dif_pos originDifferent]
          simp only [Option.toList_some]
          congr 1
        · have newestConsumed : endpoint.node = step.application :=
            Decidable.not_not.mp newestSurvives
          have notExtended :
              ¬ endpoint.node ∉
                (steps ++ [step]).map RelationJoinStep.application := by
            simp [List.map_append, newestConsumed]
          rw [dif_neg notExtended]
          unfold liftPrefixEndpoint?
          rw [dif_neg]
          · exact induction
          · simp [liftNodeOrigin, newestConsumed]
      · rw [dif_neg priorSurvives]
        have notExtended :
            ¬ endpoint.node ∉
              (steps ++ [step]).map RelationJoinStep.application := by
          intro extended
          apply priorSurvives
          intro priorMember
          exact extended (by
            simp only [List.map_append, List.mem_append]
            exact Or.inl priorMember)
        rw [dif_neg notExtended]
        exact induction

/-- Embed a newest step's allocation-neutral generated endpoint in the live
prefix node-origin carrier. -/
def freshPrefixEndpointOrigin
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content) :
    StepGeneratedEndpointOrigin step →
      RawEndpoint (PrefixLiveNodeOrigin (steps ++ [step]))
  | ⟨.fragment node, port⟩ =>
      { node := ⟨freshContentNodeOrigin step node, trivial⟩
        port := port }
  | ⟨.request request, port⟩ =>
      { node := ⟨freshRequestNodeOrigin step request, trivial⟩
        port := port }

private theorem expectedPrefixSourceGeneratedEndpoints_fresh
    (steps : List (RelationJoinStep source dying content))
    (step : RelationJoinStep source dying content)
    (wire : source.val.WireId) :
    (expectedStepGeneratedEndpoints step
        (step.attachment.hostWire (step.baseWireImage wire))).map
        (freshPrefixEndpointOrigin (steps := steps) step) =
      expectedSourceStepEndpoints step wire
        (fun node => ⟨freshContentNodeOrigin (steps := steps) step node,
          trivial⟩)
        (fun request => ⟨freshRequestNodeOrigin (steps := steps) step request,
          trivial⟩) := by
  unfold expectedStepGeneratedEndpoints
    expectedStepGeneratedEndpointOccurrences
    expectedStepFragmentEndpointOccurrences
    expectedStepRequestEndpointOccurrences expectedSourceStepEndpoints
  rw [List.filterMap_append, List.map_append]
  congr 1
  · rw [List.map_filterMap, List.filterMap_map]
    apply congrArg (fun mapper => List.filterMap mapper
      content.val.diagram.endpointOccurrences)
    funext occurrence
    cases occurrence with
    | mk occurrenceWire occurrenceEndpoint =>
        cases occurrenceEndpoint with
        | mk node port =>
            by_cases same :
                step.attachment.fragmentWire occurrenceWire =
                  step.attachment.hostWire (step.baseWireImage wire)
            · simp only [Function.comp_apply]
              calc
                _ = Option.map (freshPrefixEndpointOrigin step)
                    (some ({ node := .fragment node, port := port } :
                      StepGeneratedEndpointOrigin step)) :=
                    congrArg (Option.map (freshPrefixEndpointOrigin step))
                      (if_pos same)
                _ = _ := by
                  rw [if_pos same]
                  rfl
            · simp only [Function.comp_apply]
              calc
                _ = Option.map (freshPrefixEndpointOrigin step)
                    (none : Option (StepGeneratedEndpointOrigin step)) :=
                    congrArg (Option.map (freshPrefixEndpointOrigin step))
                      (if_neg same)
                _ = _ := by
                  rw [if_neg same]
                  rfl
  · rw [List.filterMap_flatMap, List.map_flatMap]
    apply congrArg (fun mapper => List.flatMap mapper
      (Data.Finite.allFin step.attachment.identityRequests.length))
    funext request
    rw [List.map_filterMap, List.filterMap_map]
    apply congrArg (fun mapper => List.filterMap mapper
      (Data.Finite.allFin
        (step.attachment.identityRequests.get request).attachments.length))
    funext port
    by_cases same :
        (step.attachment.identityRequests.get request).attachments.get port =
          step.baseWireImage wire
    · have hosted := congrArg step.attachment.hostWire same
      simp only [Function.comp_apply]
      calc
        _ = Option.map (freshPrefixEndpointOrigin step)
            (some ({ node := .request request, port := .identity port.val } :
              StepGeneratedEndpointOrigin step)) :=
            congrArg (Option.map (freshPrefixEndpointOrigin step))
              (if_pos hosted)
        _ = _ := by
          rw [if_pos same]
          rfl
    · have notHosted :
          step.attachment.hostWire
              ((step.attachment.identityRequests.get request).attachments.get
                port) ≠
            step.attachment.hostWire (step.baseWireImage wire) := by
        intro hosted
        exact same (step.attachment.hostWire_injective hosted)
      simp only [Function.comp_apply]
      calc
        _ = Option.map (freshPrefixEndpointOrigin step)
            (none : Option (StepGeneratedEndpointOrigin step)) :=
            congrArg (Option.map (freshPrefixEndpointOrigin step))
              (if_neg notHosted)
        _ = _ := by
          rw [if_neg same]
          rfl

private theorem expectedPrefixSourceGeneratedEndpoints_fresh_at
    (steps : List (RelationJoinStep source dying content))
    (step : RelationJoinStep source dying content)
    (wire : source.val.WireId) :
    (expectedStepGeneratedEndpoints step
        (step.attachment.hostWire (step.baseWireImage wire))).map
        (freshPrefixEndpointOrigin (steps := steps) step) =
      expectedPrefixSourceEndpointsAt (steps := steps ++ [step]) wire
        (Fin.cast (by simp) (Fin.last steps.length)) := by
  rw [expectedPrefixSourceGeneratedEndpoints_fresh steps step wire]
  unfold expectedPrefixSourceEndpointsAt
  apply expectedSourceStepEndpoints_congr
      (steps_get_freshOccurrence step).symm wire
  · intro node
    apply congrArg (fun origin : PrefixLiveNodeOrigin (steps ++ [step]) =>
      origin)
    apply Subtype.ext
    simp [prefixContentNodeOrigin, freshContentNodeOrigin]
  · intro request
    apply Subtype.ext
    simp [prefixRequestNodeOrigin, freshRequestNodeOrigin]

private theorem expectedPrefixSourceEndpointsAt_lift
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (wire : source.val.WireId)
    (occurrence : Fin steps.length) :
    (expectedPrefixSourceEndpointsAt wire occurrence).filterMap
      (liftPrefixEndpoint? step) =
      expectedPrefixSourceEndpointsAt (steps := steps ++ [step]) wire
        (Fin.cast (by simp) (Fin.castAdd 1 occurrence)) := by
  let liftedContentNode : content.val.diagram.NodeId →
      PrefixLiveNodeOrigin (steps ++ [step]) := fun node =>
    let origin := prefixContentNodeOrigin occurrence node
    ⟨liftNodeOrigin step origin.1,
      liftNodeOrigin_live_of_live_of_ne step origin.1 origin.2 (by
        dsimp [origin]
        simp [prefixContentNodeOrigin])⟩
  let liftedRequestNode :
      Fin ((steps.get occurrence).attachment.identityRequests.length) →
        PrefixLiveNodeOrigin (steps ++ [step]) := fun request =>
    let origin := prefixRequestNodeOrigin occurrence request
    ⟨liftNodeOrigin step origin.1,
      liftNodeOrigin_live_of_live_of_ne step origin.1 origin.2 (by
        dsimp [origin]
        simp [prefixRequestNodeOrigin])⟩
  have mappedExact :
      (expectedPrefixSourceEndpointsAt wire occurrence).filterMap
          (liftPrefixEndpoint? step) =
        expectedSourceStepEndpoints (steps.get occurrence) wire
          liftedContentNode liftedRequestNode := by
    unfold expectedPrefixSourceEndpointsAt expectedSourceStepEndpoints
    rw [List.filterMap_append, List.filterMap_filterMap,
      List.filterMap_flatMap]
    congr 1
    · apply congrArg (fun mapper => List.filterMap mapper
          content.val.diagram.endpointOccurrences)
      funext endpointOccurrence
      by_cases same :
          (steps.get occurrence).attachment.fragmentWire endpointOccurrence.1 =
            (steps.get occurrence).attachment.hostWire
              ((steps.get occurrence).baseWireImage wire)
      · have same' :
            steps[occurrence.val].attachment.fragmentWire endpointOccurrence.1 =
              steps[occurrence.val].attachment.hostWire
                (steps[occurrence.val].baseWireImage wire) := by
            simpa only [List.get_eq_getElem] using same
        simp [same', liftPrefixEndpoint?, liftedContentNode,
          prefixContentNodeOrigin, liftNodeOrigin]
      · have same' : ¬
            steps[occurrence.val].attachment.fragmentWire endpointOccurrence.1 =
              steps[occurrence.val].attachment.hostWire
                (steps[occurrence.val].baseWireImage wire) := by
            simpa only [List.get_eq_getElem] using same
        simp [same']
    · apply congrArg (fun mapper => List.flatMap mapper
          (Data.Finite.allFin
            (steps.get occurrence).attachment.identityRequests.length))
      funext request
      rw [List.filterMap_filterMap]
      apply congrArg (fun mapper => List.filterMap mapper
        (Data.Finite.allFin
          ((steps.get occurrence).attachment.identityRequests.get request).attachments.length))
      funext port
      by_cases same :
          ((steps.get occurrence).attachment.identityRequests.get
            request).attachments.get port =
            (steps.get occurrence).baseWireImage wire
      · have same' :
            steps[occurrence.val].attachment.identityRequests[request.val].attachments[port.val] =
              steps[occurrence.val].baseWireImage wire := by
            simpa only [List.get_eq_getElem] using same
        simp [same', liftPrefixEndpoint?, liftedRequestNode,
          prefixRequestNodeOrigin, liftNodeOrigin]
      · have same' : ¬
            steps[occurrence.val].attachment.identityRequests[request.val].attachments[port.val] =
              steps[occurrence.val].baseWireImage wire := by
            simpa only [List.get_eq_getElem] using same
        simp [same']
  rw [mappedExact]
  unfold expectedPrefixSourceEndpointsAt
  apply expectedSourceStepEndpoints_congr
      (steps_get_liftedOccurrence step occurrence).symm wire
  · intro node
    apply Subtype.ext
    simp [liftedContentNode, prefixContentNodeOrigin, liftNodeOrigin]
  · intro request
    apply Subtype.ext
    simp [liftedRequestNode, prefixRequestNodeOrigin, liftNodeOrigin]

private theorem expectedPrefixSourceWireEndpoints_snoc
    (steps : List (RelationJoinStep source dying content))
    (step : RelationJoinStep source dying content)
    (wire : source.val.WireId) :
    (expectedPrefixSourceWireEndpoints steps wire).filterMap
        (liftPrefixEndpoint? step) ++
      (expectedStepGeneratedEndpoints step
        (step.attachment.hostWire (step.baseWireImage wire))).map
          (freshPrefixEndpointOrigin step) =
      expectedPrefixSourceWireEndpoints (steps ++ [step]) wire := by
  unfold expectedPrefixSourceWireEndpoints
  rw [List.filterMap_append,
    expectedPrefixSourceEndpoints_snoc steps step wire,
    List.filterMap_flatMap]
  have liftedOccurrences :
      (Data.Finite.allFin steps.length).flatMap
          (fun occurrence =>
            (expectedPrefixSourceEndpointsAt wire occurrence).filterMap
              (liftPrefixEndpoint? step)) =
        (Data.Finite.allFin steps.length).flatMap
          (fun occurrence =>
            expectedPrefixSourceEndpointsAt (steps := steps ++ [step]) wire
              (Fin.cast (by simp) (Fin.castAdd 1 occurrence))) := by
    apply congrArg (fun mapper => List.flatMap mapper
      (Data.Finite.allFin steps.length))
    funext occurrence
    exact expectedPrefixSourceEndpointsAt_lift step wire occurrence
  rw [liftedOccurrences]
  have allFinExact :
      Data.Finite.allFin (steps ++ [step]).length =
        (Data.Finite.allFin steps.length).map
            (fun occurrence =>
              Fin.cast (by simp) (Fin.castAdd 1 occurrence)) ++
          [Fin.cast (by simp) (Fin.last steps.length)] := by
    apply List.ext_getElem
    · simp [Data.Finite.allFin_eq_finRange]
    · intro index leftBound rightBound
      by_cases prior : index < steps.length
      · rw [List.getElem_append_left (by
            simpa [Data.Finite.allFin_eq_finRange] using prior)]
        simp [Data.Finite.allFin_eq_finRange, prior]
      · have newest : index = steps.length := by
          simp [Data.Finite.allFin_eq_finRange] at leftBound rightBound
          omega
        subst index
        simp [Data.Finite.allFin_eq_finRange]
        apply Fin.ext
        rfl
  rw [allFinExact, List.flatMap_append, List.flatMap_map]
  simp only [List.flatMap_singleton]
  rw [expectedPrefixSourceGeneratedEndpoints_fresh_at steps step wire]
  simp [List.append_assoc]

private theorem expectedPrefixInternalWireEndpoints_lift
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (origin : ConstructionWireOrigin steps) :
    (expectedPrefixInternalWireEndpoints origin).filterMap
        (liftPrefixEndpoint? step) =
      expectedPrefixInternalWireEndpoints
        (liftConstructionWireOrigin step origin) := by
  unfold expectedPrefixInternalWireEndpoints
  rw [List.filterMap_filterMap]
  apply congrArg (fun mapper => List.filterMap mapper
    content.val.diagram.endpointOccurrences)
  funext endpointOccurrence
  by_cases same :
      origin.step.attachment.fragmentWire endpointOccurrence.1 =
        origin.step.attachment.fragmentWire origin.contentWire
  · have liftedSame :
        (liftConstructionWireOrigin step origin).step.attachment.fragmentWire
            endpointOccurrence.1 =
          (liftConstructionWireOrigin step origin).step.attachment.fragmentWire
            origin.contentWire := by
        rw [ConstructionWireOrigin.step_lift step origin]
        exact same
    have liftedSame' :
        (liftConstructionWireOrigin step origin).step.attachment.fragmentWire
            endpointOccurrence.1 =
          (liftConstructionWireOrigin step origin).step.attachment.fragmentWire
            (liftConstructionWireOrigin step origin).contentWire := by
      rw [ConstructionWireOrigin.contentWire_lift step origin]
      exact liftedSame
    rw [if_pos same, if_pos liftedSame']
    unfold liftPrefixEndpoint?
    simp only [Option.bind_some]
    rw [dif_pos (by simp [prefixContentNodeOrigin])]
    apply congrArg some
    cases endpointOccurrence.2 with
    | mk node port =>
        apply congrArg (fun endpointNode :
            PrefixLiveNodeOrigin (steps ++ [step]) =>
          ({ node := endpointNode, port := port } :
            RawEndpoint (PrefixLiveNodeOrigin (steps ++ [step]))))
        apply Subtype.ext
        change liftNodeOrigin step
            (prefixContentNodeOrigin
              (constructionWireDescriptor origin).occurrence node).1 =
          (prefixContentNodeOrigin
            (constructionWireDescriptor
              (liftConstructionWireOrigin step origin)).occurrence node).1
        rw [constructionWireDescriptor_occurrence_lift step origin]
        rfl
  · have liftedSame : ¬
        (liftConstructionWireOrigin step origin).step.attachment.fragmentWire
            endpointOccurrence.1 =
          (liftConstructionWireOrigin step origin).step.attachment.fragmentWire
            origin.contentWire := by
        rw [ConstructionWireOrigin.step_lift step origin]
        exact same
    have liftedSame' : ¬
        (liftConstructionWireOrigin step origin).step.attachment.fragmentWire
            endpointOccurrence.1 =
          (liftConstructionWireOrigin step origin).step.attachment.fragmentWire
            (liftConstructionWireOrigin step origin).contentWire := by
      rw [ConstructionWireOrigin.contentWire_lift step origin]
      exact liftedSame
    rw [if_neg same, if_neg liftedSame']
    rfl

private theorem expectedPrefixInternalWireEndpoints_fresh
    (steps : List (RelationJoinStep source dying content))
    (step : RelationJoinStep source dying content)
    (position : Fin step.attachment.fragmentInternalWires.length) :
    (expectedStepGeneratedEndpoints step
        (step.attachment.freshWire position)).map
        (freshPrefixEndpointOrigin (steps := steps) step) =
      expectedPrefixInternalWireEndpoints
        (freshConstructionWireOrigin steps step position) := by
  have requestNil :
      (expectedStepRequestEndpointOccurrences step).filterMap
          (fun occurrence =>
            if occurrence.1 = step.attachment.freshWire position then
              some occurrence.2
            else none) = [] := by
    unfold expectedStepRequestEndpointOccurrences
    rw [List.filterMap_flatMap]
    apply List.flatMap_eq_nil_iff.mpr
    intro request _
    rw [List.filterMap_map]
    apply List.filterMap_eq_nil_iff.mpr
    intro port _
    simp only [Function.comp_apply]
    rw [if_neg]
    exact step.attachment.hostWire_ne_freshWire _ _
  unfold expectedStepGeneratedEndpoints
    expectedStepGeneratedEndpointOccurrences
  rw [List.filterMap_append, List.map_append]
  have mappedRequestNil :
      ((expectedStepRequestEndpointOccurrences step).filterMap
          (fun occurrence =>
            if occurrence.1 = step.attachment.freshWire position then
              some occurrence.2
            else none)).map
          (freshPrefixEndpointOrigin (steps := steps) step) = [] := by
    rw [requestNil]
    rfl
  have dropRequest :
      ((expectedStepFragmentEndpointOccurrences step).filterMap
          (fun occurrence =>
            if occurrence.1 = step.attachment.freshWire position then
              some occurrence.2
            else none)).map
          (freshPrefixEndpointOrigin (steps := steps) step) ++
        ((expectedStepRequestEndpointOccurrences step).filterMap
          (fun occurrence =>
            if occurrence.1 = step.attachment.freshWire position then
              some occurrence.2
            else none)).map
          (freshPrefixEndpointOrigin (steps := steps) step) =
        ((expectedStepFragmentEndpointOccurrences step).filterMap
          (fun occurrence =>
            if occurrence.1 = step.attachment.freshWire position then
              some occurrence.2
            else none)).map
          (freshPrefixEndpointOrigin (steps := steps) step) := by
    calc
      _ = ((expectedStepFragmentEndpointOccurrences step).filterMap
          (fun occurrence =>
            if occurrence.1 = step.attachment.freshWire position then
              some occurrence.2
            else none)).map
            (freshPrefixEndpointOrigin (steps := steps) step) ++ [] :=
        congrArg _ mappedRequestNil
      _ = _ := List.append_nil _
  change
    ((expectedStepFragmentEndpointOccurrences step).filterMap
          (fun occurrence =>
            if occurrence.1 = step.attachment.freshWire position then
              some occurrence.2
            else none)).map
          (freshPrefixEndpointOrigin (steps := steps) step) ++
        ((expectedStepRequestEndpointOccurrences step).filterMap
          (fun occurrence =>
            if occurrence.1 = step.attachment.freshWire position then
              some occurrence.2
            else none)).map
          (freshPrefixEndpointOrigin (steps := steps) step) =
      expectedPrefixInternalWireEndpoints
        (freshConstructionWireOrigin steps step position)
  rw [dropRequest]
  unfold expectedStepFragmentEndpointOccurrences
    expectedPrefixInternalWireEndpoints
  rw [List.filterMap_map, List.map_filterMap]
  apply congrArg (fun mapper => List.filterMap mapper
    content.val.diagram.endpointOccurrences)
  funext endpointOccurrence
  have internalExact :=
    step.attachment.fragmentWire_get_fragmentInternalWires position
  by_cases same : step.attachment.fragmentWire endpointOccurrence.1 =
      step.attachment.freshWire position
  · have targetSame :
        (freshConstructionWireOrigin steps step position).step.attachment.fragmentWire
            endpointOccurrence.1 =
          (freshConstructionWireOrigin steps step position).step.attachment.fragmentWire
            (freshConstructionWireOrigin steps step position).contentWire := by
        rw [ConstructionWireOrigin.step_fresh steps step position,
          ConstructionWireOrigin.contentWire_fresh, internalExact]
        exact same
    simp only [Function.comp_apply]
    rw [if_pos same, if_pos targetSame]
    simp only [Option.map_some]
    apply congrArg some
    cases endpointOccurrence.2 with
    | mk node port =>
        apply congrArg (fun endpointNode :
            PrefixLiveNodeOrigin (steps ++ [step]) =>
          ({ node := endpointNode, port := port } :
            RawEndpoint (PrefixLiveNodeOrigin (steps ++ [step]))))
        apply Subtype.ext
        change freshContentNodeOrigin step node =
          (prefixContentNodeOrigin
            (constructionWireDescriptor
              (freshConstructionWireOrigin steps step position)).occurrence
            node).1
        rw [constructionWireDescriptor_occurrence_fresh steps step position]
        rfl
  · have targetSame : ¬
        (freshConstructionWireOrigin steps step position).step.attachment.fragmentWire
            endpointOccurrence.1 =
          (freshConstructionWireOrigin steps step position).step.attachment.fragmentWire
            (freshConstructionWireOrigin steps step position).contentWire := by
        rw [ConstructionWireOrigin.step_fresh steps step position,
          ConstructionWireOrigin.contentWire_fresh, internalExact]
        exact same
    simp only [Function.comp_apply]
    rw [if_neg same, if_neg targetSame]
    rfl

private theorem RelationJoinConstructionTrace.boundWireOrigin_finalWireImage
    {parameters : List source.val.WireId}
    {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalAtlas : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps final}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId}
    {finalScope : final.val.RegionId}
    (trace : RelationJoinConstructionTrace source dying content parameters args
      steps final finalAtlas finalWireImage finalDying finalScope)
    (wire : source.val.WireId) :
    trace.boundWireOrigin (finalWireImage wire) = .inl wire := by
  unfold RelationJoinConstructionTrace.boundWireOrigin
  have targetExact :
      Fin.cast trace.boundWireCount_exact (finalWireImage wire) =
        Fin.castAdd (constructionWireOriginRows steps).length wire := by
    apply Fin.ext
    exact trace.finalWireImage_val wire
  rw [targetExact, Fin.addCases_left]

private theorem RelationJoinConstructionTrace.target_eq_finalWireImage_of_inl
    {parameters : List source.val.WireId}
    {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalAtlas : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps final}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId}
    {finalScope : final.val.RegionId}
    (trace : RelationJoinConstructionTrace source dying content parameters args
      steps final finalAtlas finalWireImage finalDying finalScope)
    (target : final.val.WireId)
    (wire : source.val.WireId)
    (originExact : trace.boundWireOrigin target = .inl wire) :
    target = finalWireImage wire := by
  unfold RelationJoinConstructionTrace.boundWireOrigin at originExact
  generalize splitExact : Fin.cast trace.boundWireCount_exact target = split
    at originExact
  let originAt : Fin
      (source.val.wireCount + (constructionWireOriginRows steps).length) →
        source.val.WireId ⊕ ConstructionWireOrigin steps :=
    Fin.addCases Sum.inl
      (fun position => Sum.inr
        ((constructionWireOriginRows steps).get position))
  change originAt split = Sum.inl wire at originExact
  revert splitExact originExact
  refine Fin.addCases (motive := fun split =>
    Fin.cast trace.boundWireCount_exact target = split →
      originAt split = Sum.inl wire →
      target = finalWireImage wire) ?_ ?_ split
  · intro sourceWire splitExact originExact
    simp only [originAt, Fin.addCases_left] at originExact
    have sourceExact : sourceWire = wire := Sum.inl.inj originExact
    subst sourceWire
    apply Fin.ext
    have splitValues := congrArg Fin.val splitExact
    simpa [trace.finalWireImage_val wire] using splitValues
  · intro position _ originExact
    simp only [originAt, Fin.addCases_right] at originExact
    contradiction

private theorem expectedStepGeneratedEndpoints_internal_eq_nil
    {parameters : List source.val.WireId}
    {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    {priorAtlas : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps step.prior}
    {currentWireImage : source.val.WireId → step.prior.val.WireId}
    {currentDying : step.prior.val.WireId}
    {currentScope : step.prior.val.RegionId}
    (trace : RelationJoinConstructionTrace source dying content parameters args
      steps step.prior priorAtlas currentWireImage currentDying currentScope)
    (priorWireImageExact : HEq step.priorWireImage currentWireImage)
    (target : step.prior.val.WireId)
    (origin : ConstructionWireOrigin steps)
    (originExact : trace.boundWireOrigin target = .inr origin) :
    expectedStepGeneratedEndpoints step
        (step.attachment.hostWire
          (Internal.checkedWire step.baseGenerated
            (ConcreteDiagram.DenseErasure.eraseNodeWire step.prior
              step.priorApplication target))) = [] := by
  have sourceImageNe (wire : source.val.WireId) :
      step.checkedWireImage wire ≠ step.checkedPriorWire target := by
    rw [step.checkedWireImage_eq_checkedPriorWire]
    intro same
    have priorSame : step.priorWireImage wire = target :=
      step.checkedPriorWire_injective same
    have currentSame : currentWireImage wire = target := by
      rw [← eq_of_heq priorWireImageExact]
      exact priorSame
    have originSame := congrArg trace.boundWireOrigin currentSame
    rw [trace.boundWireOrigin_finalWireImage wire, originExact] at originSame
    contradiction
  have queriedChecked :
      Internal.checkedWire step.generated
          (step.attachment.hostWire
            (Internal.checkedWire step.baseGenerated
              (ConcreteDiagram.DenseErasure.eraseNodeWire step.prior
                step.priorApplication target))) =
        step.checkedPriorWire target := by
    apply Fin.ext
    rfl
  have fragmentNe (wire : content.val.diagram.WireId) :
      step.attachment.fragmentWire wire ≠
        step.attachment.hostWire
          (Internal.checkedWire step.baseGenerated
            (ConcreteDiagram.DenseErasure.eraseNodeWire step.prior
              step.priorApplication target)) := by
    intro same
    have checkedSame :
        step.checkedFragmentWire wire = step.checkedPriorWire target := by
      rw [← queriedChecked]
      apply Fin.ext
      simpa [RelationJoinStep.checkedFragmentWire, Internal.checkedWire] using
        congrArg Fin.val same
    by_cases internal : wire ∉ content.val.boundary
    · exact step.checkedFragmentWire_ne_checkedPriorWire_of_internal
        wire internal target checkedSame
    · exact sourceImageNe _
        ((step.checkedFragmentWire_eq_checkedWireImage_of_boundary wire
          (Decidable.not_not.mp internal)).symm.trans checkedSame)
  have requestNe
      (request : Fin step.attachment.identityRequests.length)
      (port : Fin
        (step.attachment.identityRequests.get request).attachments.length) :
      step.attachment.hostWire
          ((step.attachment.identityRequests.get request).attachments.get port) ≠
        step.attachment.hostWire
          (Internal.checkedWire step.baseGenerated
            (ConcreteDiagram.DenseErasure.eraseNodeWire step.prior
              step.priorApplication target)) := by
    intro same
    have checkedSame :
        Internal.checkedWire step.generated
            (step.attachment.hostWire
              ((step.attachment.identityRequests.get request).attachments.get
                port)) =
          step.checkedPriorWire target := by
      rw [← queriedChecked]
      apply Fin.ext
      simpa [Internal.checkedWire] using congrArg Fin.val same
    exact sourceImageNe _
      ((step.checkedIdentityAttachmentWire_eq_checkedWireImage request port).symm.trans
        checkedSame)
  unfold expectedStepGeneratedEndpoints
    expectedStepGeneratedEndpointOccurrences
  rw [List.filterMap_append]
  apply List.append_eq_nil_iff.mpr
  constructor
  · unfold expectedStepFragmentEndpointOccurrences
    rw [List.filterMap_map]
    apply List.filterMap_eq_nil_iff.mpr
    intro endpointOccurrence _
    simp only [Function.comp_apply]
    exact if_neg (fragmentNe endpointOccurrence.1)
  · unfold expectedStepRequestEndpointOccurrences
    rw [List.filterMap_flatMap]
    apply List.flatMap_eq_nil_iff.mpr
    intro request _
    rw [List.filterMap_map]
    apply List.filterMap_eq_nil_iff.mpr
    intro port _
    simp only [Function.comp_apply]
    exact if_neg (requestNe request port)

private theorem priorEndpointOrigin_exact
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (priorAtlas : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps step.prior)
    (receipt : AtlasStepReceipt step priorAtlas)
    (applicationLanding : NodeLands priorAtlas.rows (.inl step.application)
      step.priorApplication)
    (endpoint : CEndpoint step.prior.val.nodeCount) :
    (if different : endpoint.node ≠ step.priorApplication then
        some ((extendAtlas step priorAtlas receipt
          applicationLanding).endpointOrigin
          (step.checkedPriorEndpoint endpoint different))
      else none) =
      liftPrefixEndpoint? step (priorAtlas.endpointOrigin endpoint) := by
  by_cases different : endpoint.node ≠ step.priorApplication
  · rw [dif_pos different]
    have originDifferent :
        priorAtlas.rows.nodeAt endpoint.node ≠ .inl step.application := by
      intro same
      have rowSame : priorAtlas.rows.nodeAt endpoint.node =
          priorAtlas.rows.nodeAt step.priorApplication :=
        same.trans applicationLanding.exact.symm
      exact different
        (priorAtlas.rows.nodeAt_injective priorAtlas.nodeNodup rowSame)
    let live := liftNodeOrigin_live_of_live_of_ne step
      (priorAtlas.rows.nodeAt endpoint.node)
      (priorAtlas.nodeRowsLive endpoint.node) originDifferent
    unfold liftPrefixEndpoint? CertifiedAtlas.endpointOrigin
    rw [dif_pos originDifferent]
    apply congrArg some
    cases endpoint with
    | mk node port =>
        apply congrArg (fun endpointNode :
            PrefixLiveNodeOrigin (steps ++ [step]) =>
          ({ node := endpointNode, port := port } :
            RawEndpoint (PrefixLiveNodeOrigin (steps ++ [step]))))
        apply Subtype.ext
        change
          (extendRows step receipt.toAtlasStepCounts priorAtlas.rows).nodeAt
              (step.checkedPriorNode node different) =
            liftNodeOrigin step (priorAtlas.rows.nodeAt node)
        rw [← retainedNodeAllocation_generic,
          extendRows_nodeAt_prior]
  · have same : endpoint.node = step.priorApplication :=
        Decidable.not_not.mp different
    rw [dif_neg different]
    have originSame : priorAtlas.rows.nodeAt endpoint.node =
        .inl step.application := by
      rw [same]
      exact applicationLanding.exact
    unfold liftPrefixEndpoint? CertifiedAtlas.endpointOrigin
    rw [dif_neg (fun different => different originSame)]

private theorem freshEndpointOrigin_exact
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (priorAtlas : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps step.prior)
    (receipt : AtlasStepReceipt step priorAtlas)
    (applicationLanding : NodeLands priorAtlas.rows (.inl step.application)
      step.priorApplication)
    (endpoint : StepGeneratedEndpointOrigin step) :
    (extendAtlas step priorAtlas receipt applicationLanding).endpointOrigin
        (Internal.checkedEndpoint step.generated
          (realizeStepGeneratedEndpoint step endpoint)) =
      freshPrefixEndpointOrigin step endpoint := by
  cases endpoint with
  | mk node port =>
      cases node with
      | fragment node =>
          apply congrArg (fun endpointNode :
              PrefixLiveNodeOrigin (steps ++ [step]) =>
            ({ node := endpointNode, port := port } :
              RawEndpoint (PrefixLiveNodeOrigin (steps ++ [step]))))
          apply Subtype.ext
          change
            (extendRows step receipt.toAtlasStepCounts priorAtlas.rows).nodeAt
                (step.checkedFragmentNode node) =
              freshContentNodeOrigin step node
          rw [extendRows_nodeAt_content]
      | request request =>
          apply congrArg (fun endpointNode :
              PrefixLiveNodeOrigin (steps ++ [step]) =>
            ({ node := endpointNode, port := port } :
              RawEndpoint (PrefixLiveNodeOrigin (steps ++ [step]))))
          apply Subtype.ext
          change
            (extendRows step receipt.toAtlasStepCounts priorAtlas.rows).nodeAt
                (step.checkedIdentityNode request) =
              freshRequestNodeOrigin step request
          rw [extendRows_nodeAt_request]

private theorem map_filterMap_priorEndpointOrigin_exact
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (priorAtlas : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps step.prior)
    (receipt : AtlasStepReceipt step priorAtlas)
    (applicationLanding : NodeLands priorAtlas.rows (.inl step.application)
      step.priorApplication)
    (endpoints : List (CEndpoint step.prior.val.nodeCount)) :
    ((endpoints.filterMap fun endpoint =>
        if different : endpoint.node ≠ step.priorApplication then
          some (step.checkedPriorEndpoint endpoint different)
        else none).map
      (extendAtlas step priorAtlas receipt applicationLanding).endpointOrigin) =
      (endpoints.map priorAtlas.endpointOrigin).filterMap
        (liftPrefixEndpoint? step) := by
  induction endpoints with
  | nil => rfl
  | cons endpoint rest induction =>
      rw [List.filterMap_cons, List.map_cons, List.filterMap_cons]
      by_cases different : endpoint.node ≠ step.priorApplication
      · rw [dif_pos different]
        have headExact := priorEndpointOrigin_exact step priorAtlas receipt
          applicationLanding endpoint
        rw [dif_pos different] at headExact
        rw [← headExact]
        simp only [Option.toList_some, List.map_cons]
        exact congrArg (List.cons _) induction
      · rw [dif_neg different]
        have headExact := priorEndpointOrigin_exact step priorAtlas receipt
          applicationLanding endpoint
        rw [dif_neg different] at headExact
        rw [← headExact]
        simp only [Option.toList_none, List.nil_append]
        exact induction

/-- Exact endpoint-origin recurrence on a transported prior bound wire. -/
theorem RelationJoinStep.checkedPriorWire_endpointOrigins_exact
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (priorAtlas : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps step.prior)
    (receipt : AtlasStepReceipt step priorAtlas)
    (applicationLanding : NodeLands priorAtlas.rows (.inl step.application)
      step.priorApplication)
    (wire : step.prior.val.WireId) :
    ((step.checked.val.wires (step.checkedPriorWire wire)).endpoints.map
      (extendAtlas step priorAtlas receipt applicationLanding).endpointOrigin) =
      (((step.prior.val.wires wire).endpoints.map
          priorAtlas.endpointOrigin).filterMap (liftPrefixEndpoint? step)) ++
        (expectedStepGeneratedEndpoints step
          (step.attachment.hostWire
            (Internal.checkedWire step.baseGenerated
              (ConcreteDiagram.DenseErasure.eraseNodeWire step.prior
                step.priorApplication wire)))).map
          (freshPrefixEndpointOrigin step) := by
  rw [step.checkedPriorWire_endpoints_exact, List.map_append,
    map_filterMap_priorEndpointOrigin_exact step priorAtlas receipt
      applicationLanding]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro endpoint _
  exact freshEndpointOrigin_exact step priorAtlas receipt
    applicationLanding endpoint

private theorem RelationJoinStep.checkedFreshWire_endpointOrigins_exact
    {steps : List (RelationJoinStep source dying content)}
    (step : RelationJoinStep source dying content)
    (priorAtlas : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps step.prior)
    (receipt : AtlasStepReceipt step priorAtlas)
    (applicationLanding : NodeLands priorAtlas.rows (.inl step.application)
      step.priorApplication)
    (position : Fin step.attachment.fragmentInternalWires.length) :
    ((step.checked.val.wires
        (Internal.checkedWire step.generated
          (step.attachment.freshWire position))).endpoints.map
      (extendAtlas step priorAtlas receipt applicationLanding).endpointOrigin) =
      (expectedStepGeneratedEndpoints step
        (step.attachment.freshWire position)).map
          (freshPrefixEndpointOrigin step) := by
  rw [checkedFreshWire_endpoints_exact step position, List.map_map]
  apply List.map_congr_left
  intro endpoint _
  exact freshEndpointOrigin_exact step priorAtlas receipt
    applicationLanding endpoint

/-- Every bound construction wire has exactly the independent ordered
endpoint fiber named by its construction origin. -/
theorem RelationJoinConstructionTrace.boundWire_endpointOrigins_exact
    {parameters : List source.val.WireId}
    {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalAtlas : CertifiedAtlas (source := source) (dying := dying)
      (content := content) steps final}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId}
    {finalScope : final.val.RegionId}
    (trace : RelationJoinConstructionTrace source dying content parameters args
      steps final finalAtlas finalWireImage finalDying finalScope)
    (target : final.val.WireId) :
    ((final.val.wires target).endpoints.map finalAtlas.endpointOrigin) =
      expectedPrefixWireEndpoints steps (trace.boundWireOrigin target) := by
  induction trace with
  | nil =>
      unfold RelationJoinConstructionTrace.boundWireOrigin
      generalize splitExact : Fin.cast _ target = splitTarget
      have splitTargetExact : splitTarget = Fin.castAdd 0 target := by
        apply Fin.ext
        simpa using (congrArg Fin.val splitExact).symm
      rw [splitTargetExact]
      let right : Fin 0 →
          source.val.WireId ⊕ ConstructionWireOrigin
            (source := source) (dying := dying) (content := content) [] :=
        fun position => Sum.inr
          ((constructionWireOriginRows (source := source) (dying := dying)
            (content := content) []).get position)
      have originExact :
          Fin.addCases (motive := fun _ =>
              source.val.WireId ⊕ ConstructionWireOrigin
                (source := source) (dying := dying) (content := content) [])
              (fun wire => Sum.inl wire) right
              (Fin.castAdd 0 target) =
            (Sum.inl target : source.val.WireId ⊕ ConstructionWireOrigin
              (source := source) (dying := dying) (content := content) []) :=
        Fin.addCases_left target
      change
        ((source.val.wires target).endpoints.map initialAtlas.endpointOrigin) =
          expectedPrefixWireEndpoints []
            (Fin.addCases (motive := fun _ =>
                source.val.WireId ⊕ ConstructionWireOrigin
                  (source := source) (dying := dying) (content := content) [])
              (fun wire => Sum.inl wire) right (Fin.castAdd 0 target))
      rw [originExact]
      unfold expectedPrefixWireEndpoints expectedPrefixSourceWireEndpoints
        expectedPrefixSourceEndpoints CertifiedAtlas.endpointOrigin
      simp [initialAtlas, PrefixNodeLive]
  | @snoc steps step priorAtlas currentWireImage currentDying currentScope
      trace priorWireImageExact priorDyingExact priorScopeExact
      relationArgsExact sourceParametersExact receipt applicationLanding
      induction =>
      let splitTarget : Fin
          (step.prior.val.wireCount +
            step.attachment.fragmentInternalWires.length) :=
        Fin.cast step.checked_wireCount target
      have targetExact :
          target = Fin.cast step.checked_wireCount.symm splitTarget := by
        apply Fin.ext
        rfl
      rw [targetExact]
      refine Fin.addCases (motive := fun splitTarget =>
        ((step.checked.val.wires
            (Fin.cast step.checked_wireCount.symm splitTarget)).endpoints.map
          (extendAtlas step priorAtlas receipt
            applicationLanding).endpointOrigin) =
          expectedPrefixWireEndpoints (steps ++ [step])
            ((RelationJoinConstructionTrace.snoc step trace
              priorWireImageExact priorDyingExact priorScopeExact
              relationArgsExact sourceParametersExact receipt
              applicationLanding).boundWireOrigin
                (Fin.cast step.checked_wireCount.symm splitTarget))) ?_ ?_
        splitTarget
      · intro priorTarget
        have checkedTarget :
            Fin.cast step.checked_wireCount.symm
                (Fin.castAdd step.attachment.fragmentInternalWires.length
                  priorTarget) =
              step.checkedPriorWire priorTarget := by
          apply Fin.ext
          rfl
        rw [checkedTarget,
          step.checkedPriorWire_endpointOrigins_exact priorAtlas receipt
            applicationLanding priorTarget,
          induction priorTarget]
        have extendedOrigin := trace.boundWireOrigin_checkedPrior step
          priorWireImageExact priorDyingExact priorScopeExact
          relationArgsExact sourceParametersExact receipt applicationLanding
          priorTarget
        rw [extendedOrigin]
        cases originDefinition : trace.boundWireOrigin priorTarget with
        | inl wire =>
            simp only [expectedPrefixWireEndpoints, liftBoundWireOrigin]
            have targetImageExact : priorTarget = currentWireImage wire :=
              trace.target_eq_finalWireImage_of_inl priorTarget wire
                originDefinition
            have priorImageExact : step.priorWireImage wire = priorTarget := by
              rw [eq_of_heq priorWireImageExact, ← targetImageExact]
            have queryExact :
                Internal.checkedWire step.baseGenerated
                    (ConcreteDiagram.DenseErasure.eraseNodeWire step.prior
                      step.priorApplication priorTarget) =
                  step.baseWireImage wire := by
              rw [step.baseWireImageExact, priorImageExact]
            rw [queryExact]
            exact expectedPrefixSourceWireEndpoints_snoc steps step wire
        | inr origin =>
            simp only [expectedPrefixWireEndpoints, liftBoundWireOrigin]
            rw [expectedStepGeneratedEndpoints_internal_eq_nil step trace
              priorWireImageExact priorTarget origin originDefinition,
              List.map_nil, List.append_nil]
            exact expectedPrefixInternalWireEndpoints_lift step origin
      · intro position
        have checkedTarget :
            Fin.cast step.checked_wireCount.symm
                (Fin.natAdd step.prior.val.wireCount position) =
              Internal.checkedWire step.generated
                (step.attachment.freshWire position) := by
          have baseCount :
              step.base.val.wireCount = step.prior.val.wireCount := by
            rw [step.baseGenerated]
            simp [ConcreteDiagram.DenseErasure.eraseNodeCandidate,
              Internal.retainedWires, ConcreteDiagram.wiresList,
              Data.Finite.allFin_eq_finRange]
          apply Fin.ext
          simp [Internal.checkedWire, ConcreteSpliceAttachment.freshWire,
            baseCount]
        rw [checkedTarget,
          step.checkedFreshWire_endpointOrigins_exact priorAtlas receipt
            applicationLanding position]
        rw [trace.boundWireOrigin_fresh step priorWireImageExact
          priorDyingExact priorScopeExact relationArgsExact
          sourceParametersExact receipt applicationLanding position]
        simp only [expectedPrefixWireEndpoints]
        exact expectedPrefixInternalWireEndpoints_fresh steps step position

private theorem expectedPrefixWireEndpoints_final
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source dying content parameters)
    (origin : FinalWireOrigin result) :
    expectedPrefixWireEndpoints result.steps
        (match origin with
        | .inl wire => .inl wire.1
        | .inr internal => .inr internal) =
      expectedFinalWireEndpoints result origin := by
  cases origin with
  | inl wire =>
      simp only [expectedPrefixWireEndpoints, expectedFinalWireEndpoints]
      unfold expectedPrefixSourceWireEndpoints expectedSurvivingWireEndpoints
        expectedPrefixSourceEndpoints expectedSourceWireEndpoints
        expectedPrefixSourceEndpointsAt expectedSourceStepEndpoints
        expectedSourceFragmentEndpointsAt expectedSourceRequestEndpointsAt
        prefixContentNodeOrigin prefixRequestNodeOrigin
      simp only [← result.steps_application_order]
      rfl
  | inr origin =>
      simp only [expectedPrefixWireEndpoints, expectedFinalWireEndpoints]
      unfold expectedPrefixInternalWireEndpoints expectedInternalWireEndpoints
      apply congrArg (fun mapper => List.filterMap mapper
        content.val.diagram.endpointOccurrences)
      funext endpointOccurrence
      let descriptor := constructionWireDescriptor origin
      have leftWire := origin.fragmentWire_descriptor endpointOccurrence.1
      have internalWire := origin.fragmentWire_content_descriptor
      by_cases same :
          origin.step.attachment.fragmentWire endpointOccurrence.1 =
            origin.step.attachment.fragmentWire origin.contentWire
      · have targetSame :
            (result.steps.get descriptor.occurrence).attachment.fragmentWire
                endpointOccurrence.1 =
              (result.steps.get descriptor.occurrence).attachment.freshWire
                descriptor.position :=
          eq_of_heq (leftWire.symm.trans (heq_of_eq same) |>.trans internalWire)
        rw [if_pos same, if_pos targetSame]
        rfl
      · have targetSame : ¬
            (result.steps.get descriptor.occurrence).attachment.fragmentWire
                endpointOccurrence.1 =
              (result.steps.get descriptor.occurrence).attachment.freshWire
                descriptor.position := by
          intro target
          apply same
          exact eq_of_heq
            (leftWire.trans (heq_of_eq target) |>.trans internalWire.symm)
        rw [if_neg same, if_neg targetSame]

/-- Terminal exhausted-wire deletion preserves the complete ordered endpoint
origin fiber of the bound representative selected by a final wire origin. -/
theorem RelationJoinResult.plainWire_endpointOrigins_eq_bound
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source dying content parameters)
    (origin : FinalWireOrigin result) :
    ((result.plainFinal.val.wires
        ((finalWireOriginEquiv result).symm origin)).endpoints.map
      result.finalEndpointOriginEquiv) =
      ((result.boundFinal.val.wires
        (result.boundWireOfFinalOrigin origin)).endpoints.map
      result.constructionAtlas.endpointOrigin) := by
  change
    ((result.plainFinal.val.wires
        ((finalWireOriginEquiv result).invFun origin)).endpoints.map
      result.finalEndpointOriginEquiv) = _
  rw [← result.plainBoundWireImage_boundWireOfFinalOrigin origin,
    result.plainBoundWireImage_endpoints, List.map_map]
  apply List.map_congr_left
  intro endpoint _
  cases endpoint with
  | mk node port =>
      apply congrArg (fun endpointNode : FinalNodeOrigin result =>
        ({ node := endpointNode, port := port } :
          RawEndpoint (FinalNodeOrigin result)))
      apply Subtype.ext
      change result.constructionAtlas.rows.nodeAt
          (Fin.cast result.plainFinal_nodeCount
            (result.plainBoundNodeImage node)) =
        result.constructionAtlas.rows.nodeAt node
      congr 1

/-- Once the construction-trace bound fiber is established, terminal
deletion and both committed origin equivalences preserve that equality
without any reordering. -/
private theorem RelationJoinResult.finalWire_endpoints_exact_of_bound
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source dying content parameters)
    (origin : FinalWireOrigin result)
    (boundExact :
      ((result.boundFinal.val.wires
          (result.boundWireOfFinalOrigin origin)).endpoints.map
        result.constructionAtlas.endpointOrigin) =
        expectedFinalWireEndpoints result origin) :
    ((result.plainFinal.val.wires
        ((finalWireOriginEquiv result).symm origin)).endpoints.map
      result.finalEndpointOriginEquiv) =
      expectedFinalWireEndpoints result origin := by
  rw [result.plainWire_endpointOrigins_eq_bound origin, boundExact]

/-- The raw terminal relation-join wire fiber is exactly the independent
construction-order endpoint specification carried by its final wire origin. -/
theorem RelationJoinResult.finalWire_endpoints_exact
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source dying content parameters)
    (origin : FinalWireOrigin result) :
    ((result.plainFinal.val.wires
        ((finalWireOriginEquiv result).symm origin)).endpoints.map
      result.finalEndpointOriginEquiv) =
      expectedFinalWireEndpoints result origin := by
  apply result.finalWire_endpoints_exact_of_bound origin
  rw [result.construction_trace.boundWire_endpointOrigins_exact,
    result.boundWireOfFinalOrigin_origin]
  exact expectedPrefixWireEndpoints_final result origin

end ConcreteWireQuantifier

end VisualProof
