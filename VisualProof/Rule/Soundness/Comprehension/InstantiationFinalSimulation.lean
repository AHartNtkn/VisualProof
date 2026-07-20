import VisualProof.Rule.Soundness.Comprehension.InstantiationFinalAllowed
import VisualProof.Rule.Soundness.Comprehension.InstantiationFinalFocusedKeptCompiler
import VisualProof.Rule.Soundness.Comprehension.InstantiationFinalPresentation
import VisualProof.Rule.Soundness.Comprehension.InstantiationFinalTerminalBinder
import VisualProof.Rule.Soundness.Comprehension.SameDiagramSemantic
import VisualProof.Rule.Soundness.Modal.VacuousEliminationSimulation

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationTrace

theorem transport_symm_transport
    {A : Sort u} (motive : A → Sort v) {left right : A}
    (equality : left = right) (value : motive left) :
    equality.symm ▸ (equality ▸ value) = value := by
  cases equality
  rfl

/-- Dropping the empty processed-atom list of the initial state only changes
the dense presentation of node identifiers. -/
noncomputable def initialDropIso
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders) :
    ConcreteIso (dropInstantiationAtomsRaw (initialInstantiationState payload))
      input.val := by
  let domain := instantiationAtomDomain (initialInstantiationState payload)
  have allSurvive : ∀ node, domain.survives node = true := by
    intro node
    change decide (node ∉ ([] : List
      (Fin (initialInstantiationState payload).diagram.val.nodeCount))) = true
    apply decide_eq_true
    simp
  have enumerationEq : domain.enumeration = allFin input.val.nodeCount := by
    apply List.filter_eq_self.mpr
    intro node _
    exact allSurvive node
  have countEq : domain.count = input.val.nodeCount := by
    calc
      domain.count = domain.enumeration.length := rfl
      _ = (allFin input.val.nodeCount).length :=
        congrArg List.length enumerationEq
      _ = input.val.nodeCount := by simp [allFin_eq_finRange]
  let nodeEquiv : FiniteEquiv domain.Carrier
      (Fin input.val.nodeCount) := {
    toFun := domain.origin
    invFun := fun node => domain.index node (allSurvive node)
    left_inv := domain.index_origin
    right_inv := fun node => domain.origin_index node (allSurvive node)
  }
  refine {
    regionCount_eq := rfl
    nodeCount_eq := countEq
    wireCount_eq := rfl
    regions := FiniteEquiv.refl _
    nodes := nodeEquiv
    wires := FiniteEquiv.refl _
    root_eq := rfl
    regions_eq := by
      simp [dropInstantiationAtomsRaw, initialInstantiationState]
    nodes_eq := by
      intro node
      simp [dropInstantiationAtomsRaw, initialInstantiationState, nodeEquiv,
        domain]
    wire_scope_eq := by
      intro wire
      simp [dropInstantiationAtomsRaw, initialInstantiationState]
    wire_endpoints_perm := ?_
  }
  intro wire
  change
    ((List.filterMap domain.reindexEndpoint?
        (input.val.wires wire).endpoints).map
      (CEndpoint.rename nodeEquiv)).Perm
        (input.val.wires wire).endpoints
  have mappedEq :
      (List.filterMap domain.reindexEndpoint?
          (input.val.wires wire).endpoints).map
        (CEndpoint.rename nodeEquiv) =
          (input.val.wires wire).endpoints := by
    induction (input.val.wires wire).endpoints with
    | nil => rfl
    | cons endpoint tail ih =>
        have reindexed : domain.reindexEndpoint? endpoint =
            some { node := domain.index endpoint.node
                    (allSurvive endpoint.node)
                   port := endpoint.port } := by
          unfold SurvivorDomain.reindexEndpoint?
          rw [domain.index?_index endpoint.node (allSurvive endpoint.node)]
          rfl
        have filtered := List.filterMap_cons_some (l := tail) reindexed
        have mapped := congrArg
          (List.map (CEndpoint.rename nodeEquiv)) filtered
        exact mapped.trans (by
          simp only [List.map_cons]
          congr 1
          cases endpoint with
          | mk node port =>
              exact congrArg
                (fun mapped => ({ node := mapped, port := port } :
                  CEndpoint input.val.nodeCount))
                (domain.origin_index node (allSurvive node)))
  rw [mappedEq]

@[simp] private theorem initialDropIso_regions
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    (region : Fin input.val.regionCount) :
    (initialDropIso payload).regions region = region := rfl

@[simp] private theorem initialDropIso_wires
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    (wire : Fin input.val.wireCount) :
    (initialDropIso payload).wires wire = wire := rfl

/-- The final root is either the promoted focus or the exact image of the
regular original root. -/
theorem finalRoot_admissible
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
      (dropInstantiationAtomsRaw result).WellFormed signature) :
    copyTrace.FinalAdmissible elimTrace finalWellFormed
      elimTrace.sourceDiagram.root := by
  by_cases rootFocus : input.val.root = payload.parent
  · right
    rw [← copyTrace.finalRegionMap_root elimTrace finalWellFormed, rootFocus]
    exact copyTrace.finalRegionMap_parent elimTrace finalWellFormed
  · left
    have rootRegular : FrameRegular payload input.val.root := by
      constructor
      · intro enclosed
        have bubbleRoot := ConcreteElaboration.encloses_sheet_eq
          input.property.root_is_sheet enclosed
        have sameShape := congrArg input.val.regions bubbleRoot
        have impossible := payload.bubble_eq.symm.trans
          (sameShape.trans input.property.root_is_sheet)
        cases impossible
      · exact rootFocus
    exact ⟨input.val.root, rootRegular,
      copyTrace.finalRegionMap_root elimTrace finalWellFormed⟩

/-- Final-to-original compiler simulation.  All non-focused regions are
handled pointwise by the certified reverse maps; the promoted focus owns the
comprehension-instantiation law. -/
noncomputable def finalSemanticSimulation
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
    (boundaryNodup : comprehension.val.boundary.Nodup)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature) :
    ConcreteElaboration.ConcreteSemanticSimulation signature
      elimTrace.sourceDiagram input.val model named where
  source_wellFormed := sourceWellFormed
  target_wellFormed := input.property
  regionMap := copyTrace.reverseRegionMap elimTrace finalWellFormed
  binderMap := copyTrace.reverseRegionMap elimTrace finalWellFormed
  Distinguished := fun region =>
    ¬ copyTrace.FinalRegularPreimage elimTrace finalWellFormed region
  occurrenceMap := fun region regular =>
    copyTrace.reverseOccurrenceMap elimTrace finalWellFormed region
      (Classical.not_not.mp regular)
  occurrenceMap_node := by
    intro region regular node nodeRegion
    exact copyTrace.reverseOccurrenceMap_node_of_regular elimTrace
      finalWellFormed region (Classical.not_not.mp regular) node nodeRegion
  occurrenceMap_child := by
    intro region regular child
    rfl
  root_eq := (copyTrace.reverseRegionMap_root elimTrace finalWellFormed).symm
  region_shape := by
    intro parent regular child childParent
    have shape := copyTrace.reverse_region_shape_of_regular elimTrace
      finalWellFormed parent (Classical.not_not.mp regular) child childParent
    cases finalShape : elimTrace.sourceDiagram.regions child <;>
      simp only [finalShape] at shape ⊢ <;> exact shape
  localOccurrences_map := by
    intro region regular
    exact copyTrace.reverse_localOccurrences elimTrace finalWellFormed region
      (Classical.not_not.mp regular)
  BinderWitness := fun sourceBinders targetBinders =>
    FinalBinderWitness copyTrace elimTrace finalWellFormed sourceBinders
      targetBinders
  relationMap := fun witness => witness.relationMap
  binders_empty := FinalBinderWitness.empty copyTrace elimTrace finalWellFormed
  binders_push := by
    intro sourceRels targetRels sourceBinders targetBinders witness child parent
      arity childKind regular
    exact witness.push child parent arity childKind
      (Classical.not_not.mp regular)
  relationMap_push := by
    intro sourceRels targetRels sourceBinders targetBinders witness child parent
      arity childKind regular
    exact witness.relationMap_push child parent arity childKind
      (Classical.not_not.mp regular)
  Allowed := FinalAllowed elimTrace.sourceDiagram
    (elimTrace.targetIndex finalWellFormed)
  allowed_cut := by
    intro direction child parent childKind regular allowed
    exact finalAllowed_cut elimTrace.sourceDiagram
      (elimTrace.targetIndex finalWellFormed) direction child parent childKind
      allowed
  allowed_bubble := by
    intro direction child parent arity childKind regular allowed
    exact finalAllowed_bubble elimTrace.sourceDiagram
      (elimTrace.targetIndex finalWellFormed) direction child parent arity
      childKind allowed
  ContextWitness := fun sourceContext targetContext =>
    PLift (FinalContextWitness copyTrace elimTrace sourceContext targetContext)
  AtRegion := fun _ region =>
    copyTrace.FinalAdmissible elimTrace finalWellFormed region
  indexRelation := fun witness => witness.down.indexRelation
  extendContext := by
    intro sourceContext targetContext witness region regular sourceExact
      targetExact
    exact PLift.up (witness.down.extendRegular finalWellFormed boundaryNodup
      region (Classical.not_not.mp regular))
  extendFocusedContext := by
    intro sourceContext targetContext witness region atRegion focused sourceExact
      targetExact
    have regionFocus : region = elimTrace.targetIndex finalWellFormed := by
      rcases atRegion with regular | focus
      · exact False.elim (focused regular)
      · exact focus
    subst region
    simpa using PLift.up
      (witness.down.extendFocused finalWellFormed boundaryNodup)
  at_child := by
    intro sourceContext targetContext context parent regular sourceExact
      targetExact child atParent childParent
    exact copyTrace.child_admissible_of_regular_parent elimTrace
      finalWellFormed parent child (Classical.not_not.mp regular) childParent
  at_extended := by
    intro sourceContext targetContext context region regular sourceExact
      targetExact atRegion
    exact atRegion
  at_focused_child := by
    intro sourceContext targetContext context parent focused sourceExact
      targetExact child atParent sourceParent targetParent
    have parentFocus : parent = elimTrace.targetIndex finalWellFormed := by
      rcases atParent with parentRegular | parentFocus
      · exact False.elim (focused parentRegular)
      · exact parentFocus
    subst parent
    left
    by_cases childRegular : copyTrace.FinalRegularPreimage elimTrace
        finalWellFormed child
    · exact childRegular
    have childFallback : copyTrace.reverseRegionMap elimTrace finalWellFormed
        child = payload.parent := by
      simp [reverseRegionMap, childRegular]
    have selfParent : (input.val.regions payload.parent).parent? =
        some payload.parent := by
      simpa [childFallback,
        copyTrace.reverseRegionMap_targetIndex elimTrace finalWellFormed]
        using targetParent
    exact False.elim ((ConcreteElaboration.checked_direct_child_not_encloses_parent
      input.property selfParent)
      (ConcreteDiagram.Encloses.refl input.val payload.parent))
  localTransport := by
    intro sourceRels targetRels direction fuelSource fuelTarget sourceContext
      targetContext context sourceBinders targetBinders binderWitness region
      atRegion regular allowed sourceExact targetExact sourceBindersCover
      targetBindersCover sourceEnumeration targetEnumeration sourceItems
      targetItems sourceCompiled targetCompiled itemSemantics relationEnvironment
    letI : Nonempty model.Carrier :=
      ConcreteElaboration.lambdaModel_carrier_nonempty model
    apply ConcreteElaboration.directionalLocalTransport_of_agreement
      direction sourceContext targetContext region
      (copyTrace.reverseRegionMap elimTrace finalWellFormed region)
      context.down.indexRelation
      (context.down.extendRegular finalWellFormed boundaryNodup region
        (Classical.not_not.mp regular)).indexRelation
      model named (sourceItems.renameRelations binderWitness.relationMap)
      targetItems
    · exact context.down.regularEnvironmentSelection finalWellFormed
        boundaryNodup direction sourceContext targetContext region
        (Classical.not_not.mp regular) sourceExact
    · exact itemSemantics
  nodeSemantic := by
    intro sourceRels targetRels direction region sourceContext targetContext
      context atRegion sourceNodup targetNodup sourceBinders targetBinders
      allowed binderWitness sourceNode targetNode regular mapped nodeRegion
      sourceItem targetItem sourceCompiled targetCompiled
    let regular' := Classical.not_not.mp regular
    have canonical := copyTrace.reverseOccurrenceMap_node_eq elimTrace
      finalWellFormed region regular' sourceNode nodeRegion
    rw [canonical] at mapped
    have targetNodeEq := ConcreteElaboration.LocalOccurrence.node.inj mapped
    subst targetNode
    exact copyTrace.regularNode_itemSimulation elimTrace sourceWellFormed
      finalWellFormed boundaryNodup model named direction sourceContext
      targetContext context.down sourceNodup sourceBinders targetBinders
      binderWitness region regular' sourceNode nodeRegion sourceItem targetItem
      sourceCompiled targetCompiled
  focusedRegionKernel := by
    intro sourceRels targetRels direction fuelSource fuelTarget region
      sourceContext targetContext context sourceBinders targetBinders atRegion
      focused allowed binderWitness sourceExact targetExact sourceBindersCover
      targetBindersCover sourceEnumeration targetEnumeration recurse recurseAt
      sourceItems targetItems sourceCompiled targetCompiled
    have regionFocus : region = elimTrace.targetIndex finalWellFormed := by
      rcases atRegion with regular | focusEq
      · exact False.elim (focused regular)
      · exact focusEq
    subst region
    have directionEq := finalAllowed_focus_forward elimTrace.sourceDiagram
      (elimTrace.targetIndex finalWellFormed) direction allowed
    subst direction
    let sourceRecurse : ∀ {rels : RelCtx},
        (region : Fin elimTrace.sourceDiagram.regionCount) →
        (context : ConcreteElaboration.WireContext elimTrace.sourceDiagram) →
        ConcreteElaboration.BinderContext elimTrace.sourceDiagram rels →
        Option (Region signature context.length rels) :=
      fun {rels} => ConcreteElaboration.compileRegion? signature
        elimTrace.sourceDiagram fuelSource
    let targetRecurse : ∀ {rels : RelCtx},
        (region : Fin input.val.regionCount) →
        (context : ConcreteElaboration.WireContext input.val) →
        ConcreteElaboration.BinderContext input.val rels →
        Option (Region signature context.length rels) :=
      fun {rels} => ConcreteElaboration.compileRegion? signature input.val
        fuelTarget
    have reverseFocus : copyTrace.reverseRegionMap elimTrace finalWellFormed
        (elimTrace.targetIndex finalWellFormed) = payload.parent :=
      copyTrace.reverseRegionMap_targetIndex elimTrace finalWellFormed
    revert targetCompiled targetItems
    rw [reverseFocus] at targetExact targetBindersCover targetEnumeration ⊢
    intro targetItems targetCompiled
    have targetCompiledAtParent :
        ConcreteElaboration.compileOccurrencesWith? signature input.val
          targetRecurse (targetContext.extend payload.parent) targetBinders
          (ConcreteElaboration.localOccurrences input.val payload.parent) =
            some targetItems := by
      simpa [targetRecurse] using targetCompiled
    obtain ⟨sourcePartitionItems, sourcePartitionCompiled⟩ :=
      ConcreteElaboration.compileOccurrencesWith?_complete sourceRecurse
        (sourceContext.extend (elimTrace.targetIndex finalWellFormed))
        sourceBinders
        (elimTrace.keptOccurrences finalWellFormed ++
          elimTrace.selectedOccurrences finalWellFormed)
        (by
          intro occurrence member
          exact VisualProof.Rule.ModalSoundness.compileOccurrence_success_of_mem
            elimTrace.sourceDiagram sourceRecurse
            (sourceContext.extend (elimTrace.targetIndex finalWellFormed))
            sourceBinders sourceCompiled
            ((elimTrace.focusOccurrences_perm_partition
              finalWellFormed).mem_iff.mp member))
    obtain ⟨sourceKeptItems, sourceSelectedItems, sourceKeptCompiled,
        sourceSelectedCompiled, sourcePartitionEq⟩ :=
      ConcreteElaboration.compileOccurrencesWith?_append_split sourceRecurse
        (sourceContext.extend (elimTrace.targetIndex finalWellFormed))
        sourceBinders (elimTrace.keptOccurrences finalWellFormed)
        (elimTrace.selectedOccurrences finalWellFormed) sourcePartitionItems
        sourcePartitionCompiled
    obtain ⟨targetPartitionItems, targetPartitionCompiled⟩ :=
      ConcreteElaboration.compileOccurrencesWith?_complete targetRecurse
        (targetContext.extend payload.parent) targetBinders
        ((elimTrace.keptOccurrences finalWellFormed).map
            (copyTrace.finalFocusOccurrenceMap elimTrace) ++
          [ConcreteElaboration.LocalOccurrence.child bubble])
        (by
          intro occurrence member
          exact VisualProof.Rule.ModalSoundness.compileOccurrence_success_of_mem
            input.val targetRecurse (targetContext.extend payload.parent)
            targetBinders targetCompiledAtParent
            ((copyTrace.finalFocusOccurrences_perm elimTrace
              finalWellFormed).mem_iff.mp member))
    obtain ⟨targetKeptItems, targetBubbleItems, targetKeptCompiled,
        targetBubbleCompiled, targetPartitionEq⟩ :=
      ConcreteElaboration.compileOccurrencesWith?_append_split targetRecurse
        (targetContext.extend payload.parent) targetBinders
        ((elimTrace.keptOccurrences finalWellFormed).map
          (copyTrace.finalFocusOccurrenceMap elimTrace))
        [ConcreteElaboration.LocalOccurrence.child bubble]
        targetPartitionItems targetPartitionCompiled
    simp only [ConcreteElaboration.compileOccurrencesWith?]
      at targetBubbleCompiled
    dsimp only [targetRecurse] at targetBubbleCompiled
    simp only [ConcreteElaboration.compileOccurrenceWith?, payload.bubble_eq]
      at targetBubbleCompiled
    cases bubbleResult : ConcreteElaboration.compileRegion? signature input.val
        fuelTarget bubble (targetContext.extend payload.parent)
        (targetBinders.push bubble payload.arity) with
    | none => simp [bubbleResult] at targetBubbleCompiled
    | some bubbleBody =>
        simp [bubbleResult] at targetBubbleCompiled
        subst targetBubbleItems
        cases fuelTarget with
        | zero => simp [ConcreteElaboration.compileRegion?] at bubbleResult
        | succ bubbleFuel =>
            simp only [ConcreteElaboration.compileRegion?] at bubbleResult
            obtain ⟨targetSelectedItems, targetSelectedCompiled,
                bubbleBodyEq⟩ := Option.bind_eq_some_iff.mp bubbleResult
            have bubbleBodyEq' :
                ConcreteElaboration.finishRegion input.val
                    (targetContext.extend payload.parent) bubble
                    targetSelectedItems = bubbleBody :=
              Option.some.inj bubbleBodyEq
            subst bubbleBody
            let focusedContext := context.down.extendFocused finalWellFormed
              boundaryNodup
            have keptPointwise : ∀ occurrence,
                occurrence ∈ elimTrace.keptOccurrences finalWellFormed →
                ∀ sourceItem targetItem,
                ConcreteElaboration.compileOccurrenceWith? signature
                    elimTrace.sourceDiagram sourceRecurse
                    (sourceContext.extend
                      (elimTrace.targetIndex finalWellFormed))
                    sourceBinders occurrence = some sourceItem →
                ConcreteElaboration.compileOccurrenceWith? signature input.val
                    targetRecurse (targetContext.extend payload.parent)
                    targetBinders
                    (copyTrace.finalFocusOccurrenceMap elimTrace occurrence) =
                      some targetItem →
                ConcreteElaboration.ItemSimulation model named .forward
                  focusedContext.indexRelation
                  (sourceItem.renameRelations binderWitness.relationMap)
                  targetItem := by
              intro occurrence member sourceItem targetItem sourceOccurrence
                targetOccurrence
              exact copyTrace.focusedKeptOccurrence_itemSimulation elimTrace
                sourceWellFormed finalWellFormed boundaryNodup model named
                .forward fuelSource (bubbleFuel + 1)
                (sourceContext.extend
                  (elimTrace.targetIndex finalWellFormed))
                (targetContext.extend payload.parent) focusedContext
                sourceBinders targetBinders binderWitness
                sourceExact targetExact sourceBindersCover targetBindersCover
                sourceEnumeration targetEnumeration allowed
                (fun childFuelTarget childSourceContext childTargetContext
                    childContext => recurseAt childFuelTarget childSourceContext
                      childTargetContext (PLift.up childContext)) occurrence
                member sourceItem targetItem (by
                  simpa [sourceRecurse] using sourceOccurrence)
                (by simpa [targetRecurse] using targetOccurrence)
            have keptSimulation :=
              ConcreteElaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
                model named .forward sourceRecurse targetRecurse
                (sourceContext.extend
                  (elimTrace.targetIndex finalWellFormed))
                (targetContext.extend payload.parent) sourceBinders
                targetBinders focusedContext.indexRelation
                binderWitness.relationMap
                (copyTrace.finalFocusOccurrenceMap elimTrace)
                (elimTrace.keptOccurrences finalWellFormed) keptPointwise
                sourceKeptItems targetKeptItems sourceKeptCompiled
                targetKeptCompiled
            let finalScopes := InstantiationSemantic.ParameterScopesAtBubble.afterTrace
              copyTrace
              (InstantiationSemantic.initial_parameterScopesAtBubble payload)
            let finalShape :=
              (InstantiationSemantic.initial_bubbleHasPayloadArity payload).afterTrace
                copyTrace
            let finalParent := Classical.choose finalShape
            have finalBubbleShape : result.diagram.val.regions result.bubble =
                .bubble finalParent payload.arity := Classical.choose_spec finalShape
            have elimBubbleShape : result.diagram.val.regions result.bubble =
                .bubble elimTrace.parent elimTrace.arity := by
              simpa only [InstantiationDrop.raw_regions] using elimTrace.bubble_eq
            have payloadArityEq : payload.arity = elimTrace.arity :=
              (CRegion.bubble.inj
                (finalBubbleShape.symm.trans elimBubbleShape)).2
            have terminalBubbleShape : result.diagram.val.regions result.bubble =
                .bubble elimTrace.parent payload.arity := by
              rw [payloadArityEq]
              exact elimBubbleShape
            let terminalContext := terminalPromotedContext elimTrace sourceContext
            let terminalOuter : ConcreteElaboration.WireContext
                (dropInstantiationAtomsRaw result) := sourceContext
            let terminalFocusedContext :=
              terminalContext.extendFocused finalWellFormed
            let terminalSelectedContext :=
              terminalContext.extendSelected finalWellFormed
            let terminalBinders := InstantiationSemantic.traceBinderContext
              copyTrace targetBinders
            have terminalParentCoverState :
                @ConcreteElaboration.BinderContext.Covers result.diagram.val
                  targetRels terminalBinders elimTrace.parent := by
              rw [← copyTrace.regionMap_parent_eq_elimParent elimTrace]
              exact InstantiationSemantic.traceBinderContext_covers_parent
                copyTrace targetBinders targetBindersCover
            have terminalParentCover :
                @ConcreteElaboration.BinderContext.Covers
                  (dropInstantiationAtomsRaw result) targetRels terminalBinders
                  elimTrace.parent :=
              InstantiationSemantic.binderCover_to_drop result terminalBinders
                elimTrace.parent terminalParentCoverState
            let terminalEnumerationState :=
              InstantiationSemantic.traceBinderEnumeration copyTrace
                targetBinders payload.parent targetEnumeration
            have terminalEnumerationStateAtParent :
                ConcreteElaboration.BinderContext.Enumeration result.diagram.val
                  terminalBinders elimTrace.parent := by
              rw [← copyTrace.regionMap_parent_eq_elimParent elimTrace]
              exact terminalEnumerationState
            let terminalEnumeration :=
              InstantiationSemantic.binderEnumeration_to_drop result
                terminalBinders elimTrace.parent terminalEnumerationStateAtParent
            have terminalParentExact :=
              InstantiationSemantic.terminalParent_exact elimTrace
                finalWellFormed sourceWellFormed sourceContext sourceExact
            have terminalSelectedExact :=
              elimTrace.targetSelected_exact finalWellFormed sourceContext
                terminalParentExact
            have terminalBubbleCover :=
              ConcreteElaboration.BinderContext.push_covers_bubble_child
                terminalParentCover (by
                  simpa only [InstantiationDrop.raw_regions] using
                    terminalBubbleShape)
            have terminalBubbleEnumeration :=
              terminalEnumeration.bubbleChild finalWellFormed (by
                simpa only [InstantiationDrop.raw_regions] using
                  terminalBubbleShape)
            let terminalBinderWitness :=
              terminalMappedBinderWitness binderWitness
            let terminalBubbleBinderWitness :=
              VacuousElimTrace.MappedBinderWitness.intoBubble
                terminalBinderWitness payload.arity
            let terminalDepth := Classical.choose
              (finalWellFormed.all_regions_reach_root result.bubble)
            have terminalDepthEq := Classical.choose_spec
              (finalWellFormed.all_regions_reach_root result.bubble)
            have terminalDepthLe : terminalDepth.val ≤
                (dropInstantiationAtomsRaw result).regionCount :=
              ConcreteElaboration.ParentTraversal.checked_climb_to_root_steps_le_regionCount
                (InstantiationDrop.checkedDrop result) terminalDepthEq
            let terminalFuel :=
              (dropInstantiationAtomsRaw result).regionCount + 1 -
                terminalDepth.val
            have terminalFuelEq : terminalDepth.val + terminalFuel =
                (dropInstantiationAtomsRaw result).regionCount + 1 := by
              dsimp [terminalFuel]
              omega
            obtain ⟨terminalBody, terminalCompiled⟩ :=
              ConcreteElaboration.compileRegion?_complete finalWellFormed
                terminalDepthEq terminalFuelEq terminalSelectedExact
                terminalBubbleCover
            cases terminalFuelCase : terminalFuel with
            | zero =>
                rw [terminalFuelCase] at terminalFuelEq
                simp only [Nat.add_zero] at terminalFuelEq
                omega
            | succ terminalBodyFuel =>
                rw [terminalFuelCase] at terminalCompiled
                simp only [ConcreteElaboration.compileRegion?]
                  at terminalCompiled
                obtain ⟨terminalSelectedItems, terminalSelectedCompiled,
                    terminalBodyEq⟩ :=
                  Option.bind_eq_some_iff.mp terminalCompiled
                have terminalBodyEq' :
                    ConcreteElaboration.finishRegion result.diagram.val
                        (@ConcreteElaboration.WireContext.extend
                          result.diagram.val sourceContext elimTrace.parent)
                        result.bubble
                        terminalSelectedItems = terminalBody := by
                  exact Option.some.inj terminalBodyEq
                subst terminalBody
                have terminalSelectedCompiledMapped :=
                  terminalSelectedCompiled
                rw [elimTrace.bubble_localOccurrences finalWellFormed]
                  at terminalSelectedCompiledMapped
                let terminalFresh :
                    VacuousElimTrace.FreshRelationSelector elimTrace
                      finalWellFormed model :=
                  InstantiationSemantic.finalFocusRelationSelector copyTrace
                    elimTrace finalWellFormed boundaryNodup model named
                let terminalSimulation := elimTrace.semanticSimulation
                  sourceWellFormed finalWellFormed model named terminalFresh
                have terminalSelectedPointwise : ∀ occurrence,
                    occurrence ∈ elimTrace.selectedOccurrences finalWellFormed →
                    ∀ sourceItem terminalItem,
                    ConcreteElaboration.compileOccurrenceWith? signature
                        elimTrace.sourceDiagram sourceRecurse
                        (sourceContext.extend
                          (elimTrace.targetIndex finalWellFormed))
                        sourceBinders occurrence = some sourceItem →
                    ConcreteElaboration.compileOccurrenceWith? signature
                        (dropInstantiationAtomsRaw result)
                        (ConcreteElaboration.compileRegion? signature
                          (dropInstantiationAtomsRaw result) terminalBodyFuel)
                        ((terminalOuter.extend elimTrace.parent).extend
                          result.bubble)
                        (terminalBinders.push result.bubble payload.arity)
                        (elimTrace.occurrenceMap occurrence) =
                          some terminalItem →
                    ConcreteElaboration.ItemSimulation model named .forward
                      terminalSelectedContext.indexRelation
                      (sourceItem.renameRelations
                        terminalBubbleBinderWitness.relationMap)
                      terminalItem := by
                  intro occurrence member sourceItem terminalItem
                    sourceOccurrence terminalOccurrence
                  apply elimTrace.focusedOccurrence_itemSimulation
                    sourceWellFormed finalWellFormed model named .forward
                    fuelSource terminalBodyFuel result.bubble
                    (sourceContext.extend
                      (elimTrace.targetIndex finalWellFormed))
                    ((terminalOuter.extend elimTrace.parent).extend
                      result.bubble)
                    terminalSelectedContext sourceBinders
                    (terminalBinders.push result.bubble payload.arity)
                    terminalBubbleBinderWitness sourceExact
                    terminalSelectedExact sourceBindersCover
                    terminalBubbleCover sourceEnumeration
                    terminalBubbleEnumeration occurrence
                  · intro node occurrenceEq
                    cases occurrenceEq
                    exact elimTrace.selected_node_region finalWellFormed node
                      member
                  · intro child occurrenceEq
                    cases occurrenceEq
                    exact elimTrace.selected_child_parent finalWellFormed child
                      member
                  · intro childDirection child childSourceRels childTargetRels
                      childSourceBinders childTargetBinders childFuelTarget
                      childSourceContext childTargetContext childContext
                      childAtRegion childAllowed childBinderWitness
                      childSourceCover childTargetCover childSourceEnumeration
                      childTargetEnumeration childSourceExact childTargetExact
                      sourceBody terminalBody childSourceCompiled
                      childTargetCompiled
                    exact terminalSimulation.compileRegion_denote
                      childDirection fuelSource childFuelTarget child
                      childSourceContext childTargetContext
                      (PLift.up childContext) childAtRegion childSourceBinders
                      childTargetBinders childAllowed childBinderWitness
                      childSourceCover childTargetCover childSourceEnumeration
                      childTargetEnumeration childSourceExact childTargetExact
                      sourceBody terminalBody childSourceCompiled
                      childTargetCompiled
                  · exact (List.mem_filter.mp member).1
                  · simpa [sourceRecurse] using sourceOccurrence
                  · exact terminalOccurrence
                have terminalSelectedSimulation :=
                  ConcreteElaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
                    model named .forward sourceRecurse
                    (ConcreteElaboration.compileRegion? signature
                      (dropInstantiationAtomsRaw result) terminalBodyFuel)
                    (sourceContext.extend
                      (elimTrace.targetIndex finalWellFormed))
                    ((terminalOuter.extend elimTrace.parent).extend
                      result.bubble)
                    sourceBinders
                    (terminalBinders.push result.bubble payload.arity)
                    terminalSelectedContext.indexRelation
                    terminalBubbleBinderWitness.relationMap
                    elimTrace.occurrenceMap
                    (elimTrace.selectedOccurrences finalWellFormed)
                    terminalSelectedPointwise sourceSelectedItems
                    terminalSelectedItems sourceSelectedCompiled
                    terminalSelectedCompiledMapped
                intro sourceEnvironment targetEnvironment targetRelations
                  outerAgreement sourceDenotation
                let sourceRelations : RelEnv model.Carrier sourceRels :=
                  RelEnv.pullback binderWitness.relationMap targetRelations
                have relationAgreement : RelEnv.Agrees
                    binderWitness.relationMap sourceRelations targetRelations :=
                  RelEnv.pullback_agrees binderWitness.relationMap
                    targetRelations
                have sourceOriginalRename :
                    denoteRegion model named sourceEnvironment targetRelations
                        ((ConcreteElaboration.finishRegion
                          elimTrace.sourceDiagram sourceContext
                          (elimTrace.targetIndex finalWellFormed)
                          sourceItems).renameRelations
                            binderWitness.relationMap) ↔
                      denoteRegion model named sourceEnvironment sourceRelations
                        (ConcreteElaboration.finishRegion
                          elimTrace.sourceDiagram sourceContext
                          (elimTrace.targetIndex finalWellFormed)
                          sourceItems) :=
                  denoteRegion_renameRelations model named
                    binderWitness.relationMap sourceRelations targetRelations
                    relationAgreement sourceEnvironment _
                obtain ⟨sourceLocal, sourceItemsDenote⟩ :=
                  (DoubleCutElimTrace.finishRegion_denote_iff
                    elimTrace.sourceDiagram
                    sourceContext (elimTrace.targetIndex finalWellFormed)
                    sourceItems model named sourceEnvironment
                    sourceRelations).mp
                    (sourceOriginalRename.mp sourceDenotation)
                have sourcePermutation :=
                  VisualProof.Rule.ModalSoundness.compileOccurrences_denote_perm
                    elimTrace.sourceDiagram sourceRecurse
                    (sourceContext.extend
                      (elimTrace.targetIndex finalWellFormed))
                    sourceBinders
                    (elimTrace.focusOccurrences_perm_partition
                      finalWellFormed).symm
                    sourceCompiled sourcePartitionCompiled model named
                let sourceFocusEnvironment :=
                  ConcreteElaboration.extendedEnvironment sourceContext
                    (elimTrace.targetIndex finalWellFormed)
                    sourceEnvironment sourceLocal
                have sourcePartitionDenote :=
                  (sourcePermutation sourceFocusEnvironment sourceRelations).mp
                    sourceItemsDenote
                rw [sourcePartitionEq, denoteItemSeq_append]
                  at sourcePartitionDenote
                rcases sourcePartitionDenote with
                  ⟨sourceKeptDenote, sourceSelectedDenote⟩
                let terminalFocusEnvironment :=
                  terminalFocusedContext.targetEnvironment
                    sourceFocusEnvironment
                let terminalSelectedEnvironment :=
                  terminalSelectedContext.targetEnvironment
                    sourceFocusEnvironment
                have terminalSelectedAgreement :
                    terminalSelectedContext.indexRelation.EnvironmentsAgree
                      sourceFocusEnvironment terminalSelectedEnvironment :=
                  terminalSelectedContext.targetEnvironment_agrees
                    sourceExact.nodup sourceFocusEnvironment
                let freshTrace : Relation model.Carrier elimTrace.arity :=
                  terminalFresh
                    (sourceContext.extend
                      (elimTrace.targetIndex finalWellFormed))
                    (terminalOuter.extend elimTrace.parent)
                    sourceBinders terminalBinders sourceExact
                    terminalSelectedExact sourceBindersCover
                    terminalParentCover sourceEnumeration terminalEnumeration
                    terminalBinderWitness sourceFocusEnvironment
                    terminalFocusEnvironment sourceRelations targetRelations
                let fresh : Relation model.Carrier payload.arity :=
                  payloadArityEq.symm ▸ freshTrace
                let terminalBubbleMap : RelationRenaming sourceRels
                    (payload.arity :: targetRels) :=
                  fun relation => ConcreteElaboration.BinderContext.liftVar
                    payload.arity (binderWitness.relationMap relation)
                have terminalBubbleAgreement : RelEnv.Agrees terminalBubbleMap
                    sourceRelations (fresh, targetRelations) := by
                  intro binderArity relation
                  exact relationAgreement binderArity relation
                have sourceSelectedRenamed :
                    denoteItemSeq (relCtx := payload.arity :: targetRels)
                      model named sourceFocusEnvironment
                      (fresh, targetRelations)
                      (sourceSelectedItems.renameRelations
                        terminalBubbleMap) :=
                  (denoteItemSeq_renameRelations model named terminalBubbleMap
                    sourceRelations (fresh, targetRelations)
                    terminalBubbleAgreement sourceFocusEnvironment
                    sourceSelectedItems).mpr sourceSelectedDenote
                have terminalSelectedDenote := terminalSelectedSimulation
                  sourceFocusEnvironment terminalSelectedEnvironment
                  (fresh, targetRelations) terminalSelectedAgreement (by
                    simpa [terminalBubbleMap, terminalBubbleBinderWitness,
                      terminalBinderWitness] using sourceSelectedRenamed)
                let terminalBubbleLocal :=
                  DoubleCutElimTrace.localEnvironmentPart
                    (terminalOuter.extend elimTrace.parent) result.bubble
                    terminalSelectedEnvironment
                have terminalSelectedEnvironmentEq :
                    ConcreteElaboration.extendedEnvironment
                        (terminalOuter.extend elimTrace.parent) result.bubble
                        terminalFocusEnvironment terminalBubbleLocal =
                      terminalSelectedEnvironment := by
                  apply DoubleCutElimTrace.extendedEnvironment_of_parts
                  intro index
                  exact elimTrace.selectedTargetEnvironment_outer
                    finalWellFormed sourceContext terminalOuter terminalContext
                    sourceExact sourceFocusEnvironment index
                have terminalBubbleDenote :
                    denoteRegion (relCtx := payload.arity :: targetRels)
                      model named terminalFocusEnvironment
                      (fresh, targetRelations)
                      (ConcreteElaboration.finishRegion result.diagram.val
                        (@ConcreteElaboration.WireContext.extend
                          result.diagram.val sourceContext elimTrace.parent)
                        result.bubble terminalSelectedItems) := by
                  apply (DoubleCutElimTrace.finishRegion_denote_iff
                    result.diagram.val
                    (@ConcreteElaboration.WireContext.extend
                      result.diagram.val sourceContext elimTrace.parent)
                    result.bubble terminalSelectedItems model named
                    terminalFocusEnvironment
                    (fresh, targetRelations)).mpr
                  refine ⟨terminalBubbleLocal, ?_⟩
                  have stateEnvironmentEq :
                      ConcreteElaboration.extendedEnvironment
                          (@ConcreteElaboration.WireContext.extend
                            result.diagram.val sourceContext elimTrace.parent)
                          result.bubble terminalFocusEnvironment
                          terminalBubbleLocal = terminalSelectedEnvironment := by
                    simpa [terminalOuter] using terminalSelectedEnvironmentEq
                  rw [stateEnvironmentEq]
                  exact terminalSelectedDenote
                have sourceKeptRenamed :
                    denoteItemSeq model named sourceFocusEnvironment
                      targetRelations
                      (sourceKeptItems.renameRelations
                        binderWitness.relationMap) :=
                  (denoteItemSeq_renameRelations model named
                    binderWitness.relationMap sourceRelations targetRelations
                    relationAgreement sourceFocusEnvironment
                    sourceKeptItems).mpr sourceKeptDenote
                let targetFocusEnvironment :=
                  focusedContext.targetEnvironment sourceFocusEnvironment
                have focusedAgreement :
                  focusedContext.indexRelation.EnvironmentsAgree
                      sourceFocusEnvironment targetFocusEnvironment :=
                  focusedContext.targetEnvironment_agrees sourceFocusEnvironment
                have targetKeptDenote :
                    denoteItemSeq model named targetFocusEnvironment
                      targetRelations targetKeptItems :=
                  keptSimulation sourceFocusEnvironment targetFocusEnvironment
                    targetRelations focusedAgreement sourceKeptRenamed
                have targetBubbleExact :
                    ((targetContext.extend payload.parent).extend bubble).Exact
                      bubble :=
                  targetExact.extend_child input.property (by
                    simp [payload.bubble_eq, CRegion.parent?])
                have targetBubbleCover :
                    (targetBinders.push bubble payload.arity).Covers bubble :=
                  ConcreteElaboration.BinderContext.push_covers_bubble_child
                    targetBindersCover payload.bubble_eq
                have targetBubbleEnumeration :
                    ConcreteElaboration.BinderContext.Enumeration input.val
                      (targetBinders.push bubble payload.arity) bubble :=
                  targetEnumeration.bubbleChild input.property payload.bubble_eq
                have targetBubbleDenote :
                    denoteRegion (relCtx := payload.arity :: targetRels)
                      model named targetFocusEnvironment
                      (fresh, targetRelations)
                      (ConcreteElaboration.finishRegion input.val
                        (targetContext.extend payload.parent) bubble
                        targetSelectedItems) := by
                  cases copyTrace with
                  | done traceFuel current pendingEmpty =>
                      let iso := initialDropIso payload
                      let sourceOuter :
                          ConcreteElaboration.WireContext
                            (dropInstantiationAtomsRaw
                              (initialInstantiationState payload)) :=
                        terminalOuter.extend elimTrace.parent
                      let targetOuter :=
                        targetContext.extend payload.parent
                      have sourceBubbleExact :
                          (sourceOuter.extend bubble).Exact bubble := by
                        simpa [sourceOuter, initialInstantiationState] using
                          terminalSelectedExact
                      let ambient :=
                        InstantiationSemantic.inheritedWireEquivIso iso bubble
                          sourceOuter targetOuter sourceBubbleExact
                          targetBubbleExact
                      have contextsAgree :
                          ConcreteElaboration.WireContextsAgree iso sourceOuter
                            targetOuter ambient := by
                        intro index
                        exact
                          InstantiationSemantic.inheritedWireEquivIso_spec iso
                            bubble sourceOuter targetOuter sourceBubbleExact
                            targetBubbleExact index
                      let sourceBinderContext :
                          ConcreteElaboration.BinderContext
                            (dropInstantiationAtomsRaw
                              (initialInstantiationState payload))
                            (payload.arity :: targetRels) :=
                        terminalBinders.push bubble payload.arity
                      let targetBinderContext :=
                        targetBinders.push bubble payload.arity
                      have baseBindersAgree :
                          ConcreteElaboration.BinderContextsAgree iso
                            terminalBinders targetBinders := by
                        intro owner
                        change targetBinders owner = terminalBinders owner
                        have mapped :=
                          InstantiationSemantic.traceBinderContext_regionMap
                            (trace := InstantiationTrace.done fuel
                              (initialInstantiationState payload) pendingEmpty)
                            targetBinders owner
                        change terminalBinders owner = targetBinders owner
                          at mapped
                        exact mapped.symm
                      have bindersAgree :
                          ConcreteElaboration.BinderContextsAgree iso
                            sourceBinderContext targetBinderContext := by
                        simpa [sourceBinderContext, targetBinderContext] using
                          baseBindersAgree.push bubble payload.arity
                      have sourceCompiledDrop :
                          ConcreteElaboration.compileRegion? signature
                              (dropInstantiationAtomsRaw
                                (initialInstantiationState payload))
                              (terminalBodyFuel + 1) bubble sourceOuter
                              sourceBinderContext =
                            some (ConcreteElaboration.finishRegion input.val
                              sourceOuter bubble terminalSelectedItems) := by
                        unfold ConcreteElaboration.compileRegion?
                        dsimp only
                        simpa [sourceOuter, sourceBinderContext,
                          initialInstantiationState] using terminalCompiled
                      have targetBubbleCompiledRegion :
                          ConcreteElaboration.compileRegion? signature input.val
                            (bubbleFuel + 1) bubble targetOuter
                            targetBinderContext =
                              some (ConcreteElaboration.finishRegion input.val
                                targetOuter bubble targetSelectedItems) := by
                        simpa [targetOuter, targetBinderContext,
                          ConcreteElaboration.compileRegion?] using bubbleResult
                      have compiledIso :=
                        ConcreteElaboration.compileRegion?_equivariant iso
                          input.property contextsAgree targetBubbleExact
                          bindersAgree sourceCompiledDrop
                          targetBubbleCompiledRegion
                      let fallback : model.Carrier :=
                        Classical.choice
                          (ConcreteElaboration.lambdaModel_carrier_nonempty model)
                      let wireValue :=
                        InstantiationSemantic.exactContextWireValue
                          (sourceContext.extend
                            (elimTrace.targetIndex finalWellFormed))
                          (elimTrace.targetIndex finalWellFormed) sourceExact
                          sourceFocusEnvironment fallback
                      have sourceAligned : ∀ index,
                          terminalFocusEnvironment index =
                            wireValue (sourceOuter.get index) := by
                        intro index
                        change sourceFocusEnvironment
                            (terminalFocusedContext.sourceIndex index) =
                          InstantiationSemantic.exactContextWireValue
                            (sourceContext.extend
                              (elimTrace.targetIndex finalWellFormed))
                            (elimTrace.targetIndex finalWellFormed) sourceExact
                            sourceFocusEnvironment fallback
                            ((terminalOuter.extend elimTrace.parent).get index)
                        rw [← terminalFocusedContext.sourceIndex_get index]
                        exact
                          (InstantiationSemantic.exactContextWireValue_get
                            (sourceContext.extend
                              (elimTrace.targetIndex finalWellFormed))
                            (elimTrace.targetIndex finalWellFormed) sourceExact
                            sourceFocusEnvironment fallback
                            (terminalFocusedContext.sourceIndex index)).symm
                      have targetAligned : ∀ index,
                          targetFocusEnvironment index =
                            wireValue (targetOuter.get index) := by
                        intro index
                        have focusedGet :=
                          focusedContext.sourceIndex_get index
                        have focusedGet' :
                            (sourceContext.extend
                              (elimTrace.targetIndex finalWellFormed)).get
                                (focusedContext.sourceIndex index) =
                              targetOuter.get index := by
                          simpa [targetOuter] using focusedGet
                        change sourceFocusEnvironment
                            (focusedContext.sourceIndex index) =
                          InstantiationSemantic.exactContextWireValue
                            (sourceContext.extend
                              (elimTrace.targetIndex finalWellFormed))
                            (elimTrace.targetIndex finalWellFormed) sourceExact
                            sourceFocusEnvironment fallback
                            (targetOuter.get index)
                        rw [← focusedGet']
                        exact
                          (InstantiationSemantic.exactContextWireValue_get
                            (sourceContext.extend
                              (elimTrace.targetIndex finalWellFormed))
                            (elimTrace.targetIndex finalWellFormed) sourceExact
                            sourceFocusEnvironment fallback
                            (focusedContext.sourceIndex index)).symm
                      have environmentAgreement :
                          EnvironmentsAgree ambient terminalFocusEnvironment
                            targetFocusEnvironment := by
                        intro index
                        rw [targetAligned (ambient index), sourceAligned index]
                        exact congrArg wireValue (by
                          simpa [iso] using
                            InstantiationSemantic.inheritedWireEquivIso_spec
                              iso bubble sourceOuter targetOuter
                              sourceBubbleExact targetBubbleExact index)
                      apply (compiledIso.denotation model named
                        terminalFocusEnvironment targetFocusEnvironment
                        (fresh, targetRelations) environmentAgreement).mp
                      simpa [sourceOuter, initialInstantiationState] using
                        terminalBubbleDenote
                  | step traceFuel _ _ atom tail site candidate arguments
                      plan pending_eq node_eq candidate_eq arguments_eq rest =>
                      let hadmissible :=
                        (Splice.Input.checkInput_sound
                          plan.checkedInputChecked).2
                      let initialTargets :
                          InstantiationSemantic.BinderTargetsAtBubble payload
                            (initialInstantiationState payload) := {
                        target_shape := hadmissible.binder_targets_match
                        target_encloses := fun index =>
                          (payload.binderTargetsProper index).1
                        target_ne := fun index =>
                          (payload.binderTargetsProper index).2
                      }
                      let wholeTrace : InstantiationTrace comprehension
                          attachments binders payload (traceFuel + 1)
                          (initialInstantiationState payload) result :=
                        .step traceFuel (initialInstantiationState payload)
                          result atom tail site candidate arguments plan
                          pending_eq node_eq candidate_eq arguments_eq rest
                      let finalTargets := initialTargets.afterTrace wholeTrace
                      let terminalStateExact :=
                        InstantiationSemantic.dropExact_to_state result
                          ((@ConcreteElaboration.WireContext.extend
                            result.diagram.val sourceContext elimTrace.parent).extend
                            result.bubble)
                          result.bubble terminalSelectedExact
                      let terminalStateCover :=
                        InstantiationSemantic.dropCover_to_state result
                          terminalBinders elimTrace.parent terminalParentCover
                      let parameterValues :=
                        InstantiationSemantic.parameterValuesOfExact result
                          finalScopes
                          (@ConcreteElaboration.WireContext.extend
                            result.diagram.val sourceContext elimTrace.parent)
                          terminalStateExact terminalFocusEnvironment
                      let proxyValues :=
                        InstantiationSemantic.proxyRelationsOfParentCover
                          payload result finalTargets terminalBinders
                          elimTrace.parent terminalBubbleShape
                          terminalStateCover targetRelations
                      let terminalPresentation :=
                        InstantiationSemantic.finalBubblePresentation payload
                          result finalTargets finalScopes model named
                          (@ConcreteElaboration.WireContext.extend
                            result.diagram.val sourceContext elimTrace.parent)
                          terminalSelectedExact finalWellFormed terminalBinders
                          elimTrace.parent terminalBubbleShape
                          terminalParentCover terminalEnumeration
                          terminalBodyFuel terminalSelectedItems
                          terminalSelectedCompiled terminalFocusEnvironment
                          targetRelations fresh terminalBubbleDenote
                      let fallback : model.Carrier :=
                        Classical.choice
                          (ConcreteElaboration.lambdaModel_carrier_nonempty model)
                      let terminalWireValue :=
                        InstantiationSemantic.exactContextWireValue
                          (sourceContext.extend
                            (elimTrace.targetIndex finalWellFormed))
                          (elimTrace.targetIndex finalWellFormed) sourceExact
                          sourceFocusEnvironment fallback
                      have terminalWireAligned :
                          terminalPresentation.OuterAligned terminalWireValue := by
                        intro index
                        change terminalFocusEnvironment index =
                          terminalWireValue
                            ((@ConcreteElaboration.WireContext.extend
                              result.diagram.val sourceContext
                              elimTrace.parent).get index)
                        change sourceFocusEnvironment
                            (terminalFocusedContext.sourceIndex index) =
                          InstantiationSemantic.exactContextWireValue
                            (sourceContext.extend
                              (elimTrace.targetIndex finalWellFormed))
                            (elimTrace.targetIndex finalWellFormed) sourceExact
                            sourceFocusEnvironment fallback
                            ((terminalOuter.extend elimTrace.parent).get index)
                        rw [← terminalFocusedContext.sourceIndex_get index]
                        exact (InstantiationSemantic.exactContextWireValue_get
                          (sourceContext.extend
                            (elimTrace.targetIndex finalWellFormed))
                          (elimTrace.targetIndex finalWellFormed) sourceExact
                          sourceFocusEnvironment fallback
                          (terminalFocusedContext.sourceIndex index)).symm
                      have selectorEq :=
                        InstantiationSemantic.finalFocusRelationSelector_eq_relationOfTraceFocus_of_step
                          (payload := payload) (traceFuel := traceFuel)
                          (result := result) (atom := atom) (tail := tail)
                          (site := site) (candidate := candidate)
                          (arguments := arguments) (plan := plan)
                          (pending_eq := pending_eq) (node_eq := node_eq)
                          (candidate_eq := candidate_eq)
                          (arguments_eq := arguments_eq)
                          (rest := rest)
                          elimTrace finalWellFormed boundaryNodup model named
                          (sourceContext.extend
                            (elimTrace.targetIndex finalWellFormed))
                          (terminalOuter.extend elimTrace.parent)
                          sourceBinders terminalBinders sourceExact
                          terminalSelectedExact sourceBindersCover
                          terminalParentCover sourceEnumeration
                          terminalEnumeration terminalBinderWitness
                          sourceFocusEnvironment terminalFocusEnvironment
                          sourceRelations targetRelations
                      have freshTraceEq : freshTrace =
                          payloadArityEq ▸
                            InstantiationSemantic.relationOfTraceFocus wholeTrace
                              model named parameterValues proxyValues := by
                        simpa [freshTrace, terminalFresh, wholeTrace,
                          parameterValues, proxyValues, terminalStateExact,
                          terminalStateCover, finalTargets, finalScopes,
                          finalShape, finalParent, finalBubbleShape,
                          terminalBubbleShape, terminalOuter] using selectorEq
                      have freshEq : fresh =
                          InstantiationSemantic.relationOfTraceFocus wholeTrace
                            model named parameterValues proxyValues := by
                        calc
                          fresh = payloadArityEq.symm ▸ freshTrace := rfl
                          _ = payloadArityEq.symm ▸
                              (payloadArityEq ▸
                                InstantiationSemantic.relationOfTraceFocus
                                  wholeTrace model named parameterValues
                                  proxyValues) := congrArg
                                    (fun relation => payloadArityEq.symm ▸
                                      relation) freshTraceEq
                          _ = InstantiationSemantic.relationOfTraceFocus
                              wholeTrace model named parameterValues
                              proxyValues := transport_symm_transport
                                (fun arity => Relation model.Carrier arity)
                                payloadArityEq
                                (InstantiationSemantic.relationOfTraceFocus
                                  wholeTrace model named parameterValues
                                  proxyValues)
                      have relationContract :
                          InstantiationSemantic.TraceRelationContract payload
                            input model named fresh proxyValues
                            parameterValues := by
                        rw [freshEq]
                        exact
                          InstantiationSemantic.relationOfTraceFocus_contract_of_step
                            model named parameterValues proxyValues
                      let simulations :=
                        InstantiationSemantic.initial_regionSimulationsEveryStep
                          wholeTrace model named fresh proxyValues
                          parameterValues relationContract
                      let terminalStateEnumeration :=
                        InstantiationSemantic.dropEnumeration_to_state result
                          (terminalBinders.push result.bubble payload.arity)
                          result.bubble terminalBubbleEnumeration
                      have canonicalExternalMapEq :=
                        InstantiationSemantic.traceExternalRelationMap_traceBinderContext_push
                          wholeTrace targetBinders payload.arity
                          terminalStateEnumeration targetBubbleCover
                          payload.parent
                      let terminalExternal :
                          InstantiationSemantic.ExternalAlignedBubblePresentation
                            payload result model named fresh proxyValues
                            parameterValues terminalWireValue
                            (targetBinders.push bubble payload.arity)
                            (fresh, targetRelations)
                            (InstantiationSemantic.traceRegionPreimage wholeTrace
                              payload.parent) := {
                        presentation := terminalPresentation
                        wireAligned := terminalWireAligned
                        relationMap :=
                          ConcreteElaboration.identityRelationRenaming
                            (payload.arity :: targetRels)
                        binderAligned := by
                          intro region binderArity relation lookup
                          have lookup' :
                              (InstantiationSemantic.traceBinderContext wholeTrace
                                targetBinders).push result.bubble payload.arity
                                  region = some ⟨binderArity, relation⟩ := by
                            simpa [terminalPresentation,
                              InstantiationSemantic.finalBubblePresentation]
                              using lookup
                          have mapped :=
                            InstantiationSemantic.traceExternalRelationMap_spec
                              wholeTrace
                              ((InstantiationSemantic.traceBinderContext wholeTrace
                                targetBinders).push result.bubble payload.arity)
                              terminalStateEnumeration
                              (targetBinders.push bubble payload.arity)
                              targetBubbleCover payload.parent relation lookup'
                          have mappedRelationEq := congrArg
                            (fun rename => rename relation)
                            canonicalExternalMapEq
                          change
                            InstantiationSemantic.traceExternalRelationMap
                                wholeTrace
                                ((InstantiationSemantic.traceBinderContext wholeTrace
                                  targetBinders).push result.bubble payload.arity)
                                terminalStateEnumeration
                                (targetBinders.push bubble payload.arity)
                                targetBubbleCover payload.parent relation =
                              ConcreteElaboration.identityRelationRenaming
                                (payload.arity :: targetRels) relation
                            at mappedRelationEq
                          rw [mappedRelationEq] at mapped
                          exact mapped
                        relationsAligned := by
                          intro binderArity relation
                          rfl
                      }
                      let initialExternal :=
                        InstantiationSemantic.externalAligned_of_trace wholeTrace
                          boundaryNodup model named fresh proxyValues
                          parameterValues simulations
                          (targetBinders.push bubble payload.arity)
                          (fresh, targetRelations) terminalWireValue
                          (InstantiationSemantic.traceRegionPreimage wholeTrace
                            payload.parent) terminalExternal
                      have initialOwnerIdentity : ∀ region,
                          (InstantiationSemantic.traceRegionPreimage wholeTrace
                            payload.parent ∘ wholeTrace.regionMap) region =
                            region := by
                        intro region
                        exact InstantiationSemantic.traceRegionPreimage_image
                          wholeTrace payload.parent region
                      have targetFocusAligned : ∀ index,
                          targetFocusEnvironment index =
                            (terminalWireValue ∘ wholeTrace.wireMap)
                              ((targetContext.extend payload.parent).get index) := by
                        intro index
                        change sourceFocusEnvironment
                            (focusedContext.sourceIndex index) =
                          InstantiationSemantic.exactContextWireValue
                            (sourceContext.extend
                              (elimTrace.targetIndex finalWellFormed))
                            (elimTrace.targetIndex finalWellFormed) sourceExact
                            sourceFocusEnvironment fallback
                            (wholeTrace.finalWireMap elimTrace
                              ((targetContext.extend payload.parent).get index))
                        rw [← focusedContext.sourceIndex_get index]
                        exact (InstantiationSemantic.exactContextWireValue_get
                          (sourceContext.extend
                            (elimTrace.targetIndex finalWellFormed))
                          (elimTrace.targetIndex finalWellFormed) sourceExact
                          sourceFocusEnvironment fallback
                          (focusedContext.sourceIndex index)).symm
                      have targetBubbleCompiledRegion :
                          ConcreteElaboration.compileRegion? signature input.val
                            (bubbleFuel + 1) bubble
                            (targetContext.extend payload.parent)
                            (targetBinders.push bubble payload.arity) =
                              some (ConcreteElaboration.finishRegion input.val
                                (targetContext.extend payload.parent) bubble
                                targetSelectedItems) := by
                        simpa only [ConcreteElaboration.compileRegion?] using
                          bubbleResult
                      exact initialExternal.denoteRecompiled_initial
                        initialOwnerIdentity
                        (targetContext.extend payload.parent) targetBubbleExact
                        targetBubbleCover targetBubbleEnumeration
                        (bubbleFuel + 1)
                        (ConcreteElaboration.finishRegion input.val
                          (targetContext.extend payload.parent) bubble
                          targetSelectedItems)
                        targetBubbleCompiledRegion targetFocusEnvironment
                        targetFocusAligned
                have targetBubbleItemDenote :
                    denoteItem model named targetFocusEnvironment
                      targetRelations
                      (Item.bubble payload.arity
                        (ConcreteElaboration.finishRegion input.val
                          (targetContext.extend payload.parent) bubble
                          targetSelectedItems)) := by
                  simp only [bubble_denotes_exists]
                  exact ⟨fresh, targetBubbleDenote⟩
                have targetPartitionDenote :
                    denoteItemSeq model named targetFocusEnvironment
                      targetRelations targetPartitionItems := by
                  rw [targetPartitionEq, denoteItemSeq_append]
                  refine ⟨targetKeptDenote, ?_⟩
                  simpa only [denoteItemSeq, and_true] using
                    targetBubbleItemDenote
                have targetPermutation :=
                  VisualProof.Rule.ModalSoundness.compileOccurrences_denote_perm
                    input.val targetRecurse
                    (targetContext.extend payload.parent) targetBinders
                    (copyTrace.finalFocusOccurrences_perm elimTrace
                      finalWellFormed).symm
                    targetCompiledAtParent targetPartitionCompiled model named
                have targetItemsDenote :
                    denoteItemSeq model named targetFocusEnvironment
                      targetRelations targetItems :=
                  (targetPermutation targetFocusEnvironment
                    targetRelations).mpr targetPartitionDenote
                let targetLocal :=
                  DoubleCutElimTrace.localEnvironmentPart targetContext
                    payload.parent targetFocusEnvironment
                have targetFocusOuter : ∀ index,
                    targetFocusEnvironment
                        (DoubleCutElimTrace.extendedOuterIndex targetContext
                          payload.parent index) =
                      targetEnvironment index := by
                  intro index
                  let sourceIndex := context.down.sourceIndex index
                  let sourceExtendedIndex :=
                    DoubleCutElimTrace.extendedOuterIndex sourceContext
                      (elimTrace.targetIndex finalWellFormed) sourceIndex
                  let targetExtendedIndex :=
                    DoubleCutElimTrace.extendedOuterIndex targetContext
                      payload.parent index
                  have corresponding :
                      (sourceContext.extend
                          (elimTrace.targetIndex finalWellFormed)).get
                            sourceExtendedIndex =
                        copyTrace.finalWireMap elimTrace
                          ((targetContext.extend payload.parent).get
                            targetExtendedIndex) := by
                    calc
                      _ = sourceContext.get sourceIndex :=
                        DoubleCutElimTrace.extendedOuterIndex_get sourceContext
                          (elimTrace.targetIndex finalWellFormed) sourceIndex
                      _ = copyTrace.finalWireMap elimTrace
                          (targetContext.get index) :=
                        context.down.sourceIndex_get index
                      _ = _ := congrArg (copyTrace.finalWireMap elimTrace)
                        (DoubleCutElimTrace.extendedOuterIndex_get targetContext
                          payload.parent index).symm
                  have sourceExtendedIndexEq : sourceExtendedIndex =
                      focusedContext.sourceIndex targetExtendedIndex :=
                    ConcreteElaboration.WireContext.lookup?_unique
                      sourceExact.nodup
                      (focusedContext.sourceIndex_lookup targetExtendedIndex)
                      corresponding
                  change sourceFocusEnvironment
                      (focusedContext.sourceIndex targetExtendedIndex) =
                    targetEnvironment index
                  rw [← sourceExtendedIndexEq]
                  change ConcreteElaboration.extendedEnvironment sourceContext
                      (elimTrace.targetIndex finalWellFormed)
                      sourceEnvironment sourceLocal sourceExtendedIndex =
                    targetEnvironment index
                  rw [DoubleCutElimTrace.extendedEnvironment_outer]
                  exact outerAgreement (context.down.sourceIndex index) index
                    rfl
                have targetFocusEq :
                    ConcreteElaboration.extendedEnvironment targetContext
                        payload.parent targetEnvironment targetLocal =
                      targetFocusEnvironment := by
                  apply DoubleCutElimTrace.extendedEnvironment_of_parts
                  intro index
                  exact targetFocusOuter index
                apply (DoubleCutElimTrace.finishRegion_denote_iff input.val
                  targetContext payload.parent targetItems model named
                  targetEnvironment targetRelations).mpr
                refine ⟨targetLocal, ?_⟩
                rw [targetFocusEq]
                exact targetItemsDenote

end InstantiationTrace

end VisualProof.Rule
