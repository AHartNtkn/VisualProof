import VisualProof.Rule.Soundness.Comprehension.InstantiationRelationSelector

namespace VisualProof.Rule

open VisualProof.Concrete

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- The exact terminal compiler focus produced during vacuous reconstruction
is a semantic presentation of the final moving bubble. -/
noncomputable def finalBubblePresentation
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Concrete.Checked }
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (targets : BinderTargetsAtBubble payload state)
    (scopes : ParameterScopesAtBubble state)
    (model : Model)
    {rels : RelCtx}
    (outer : Concrete.Elaboration.WireContext state.diagram.val)
    (outerExactDrop : @Concrete.Elaboration.WireContext.Exact
      (dropInstantiationAtomsRaw state) (outer.extend state.bubble)
        state.bubble)
    (dropWellFormed :
      (dropInstantiationAtomsRaw state).WellFormed )
    (binderContext : Concrete.Elaboration.BinderContext state.diagram.val rels)
    (parent : Fin state.diagram.val.regionCount)
    (bubbleShape : state.diagram.val.regions state.bubble =
      .bubble parent payload.arity)
    (binderCoverDrop : @Concrete.Elaboration.BinderContext.Covers
      (dropInstantiationAtomsRaw state) rels binderContext parent)
    (binderEnumerationDrop :
      Concrete.Elaboration.BinderContext.Enumeration
        (dropInstantiationAtomsRaw state) binderContext parent)
    (fuel : Nat)
    (items : ItemSeq  (outer.extend state.bubble).length
      (payload.arity :: rels))
    (itemsCompiled : Concrete.Elaboration.compileOccurrencesWith?
      (dropInstantiationAtomsRaw state)
      (Concrete.Elaboration.compileRegion?
        (dropInstantiationAtomsRaw state) fuel)
      (outer.extend state.bubble)
      (binderContext.push state.bubble payload.arity)
      (Concrete.Elaboration.localOccurrences
        (dropInstantiationAtomsRaw state) state.bubble) = some items)
    (environment : Fin outer.length → model.Carrier)
    (relationEnvironment : RelEnv model.Carrier rels)
    (relationValue : Relation model.Carrier payload.arity)
    (denotes : denoteRegion (relCtx := payload.arity :: rels) model
      environment
      (relationValue, relationEnvironment)
      (Concrete.Elaboration.finishRegion state.diagram.val outer state.bubble
        items)) :
    let parameterValues := parameterValuesOfExact state scopes outer
      (dropExact_to_state state (outer.extend state.bubble) state.bubble
        outerExactDrop)
      environment
    let proxyValues := proxyRelationsOfParentCover payload state targets
      binderContext parent bubbleShape
      (dropCover_to_state state binderContext parent binderCoverDrop)
      relationEnvironment
    BubblePresentation payload state model  relationValue proxyValues
      parameterValues := by
  dsimp only
  let outerExact := dropExact_to_state state (outer.extend state.bubble)
    state.bubble outerExactDrop
  let binderCover := dropCover_to_state state binderContext parent
    binderCoverDrop
  let parameterValues := parameterValuesOfExact state scopes outer outerExact
    environment
  let proxyValues := proxyRelationsOfParentCover payload state targets
    binderContext parent bubbleShape binderCover relationEnvironment
  have droppedBubbleShape :
      (dropInstantiationAtomsRaw state).regions state.bubble =
        .bubble parent payload.arity := by
    simpa only [InstantiationDrop.raw_regions] using bubbleShape
  have droppedCompiled : Concrete.Elaboration.compileRegion?
      (dropInstantiationAtomsRaw state) (fuel + 1) state.bubble outer
      (binderContext.push state.bubble payload.arity) =
        some (Concrete.Elaboration.finishRegion state.diagram.val outer
          state.bubble items) := by
    unfold Concrete.Elaboration.compileRegion?
    dsimp only
    change (Concrete.Elaboration.compileOccurrencesWith?
        (dropInstantiationAtomsRaw state)
        (Concrete.Elaboration.compileRegion?
          (dropInstantiationAtomsRaw state) fuel)
        (outer.extend state.bubble)
        (binderContext.push state.bubble payload.arity)
        (Concrete.Elaboration.localOccurrences
          (dropInstantiationAtomsRaw state) state.bubble)).bind
          (fun compiledItems => some (Concrete.Elaboration.finishRegion
            state.diagram.val outer state.bubble compiledItems)) =
      some (Concrete.Elaboration.finishRegion state.diagram.val outer
        state.bubble items)
    exact (congrArg (fun result => result.bind (fun compiledItems =>
      some (Concrete.Elaboration.finishRegion state.diagram.val outer
        state.bubble compiledItems))) itemsCompiled).trans rfl
  refine {
    rels := payload.arity :: rels
    outer := outer
    outerExact := outerExact
    binderContext := binderContext.push state.bubble payload.arity
    binderCover := ?_
    binderEnumeration := ?_
    fuel := fuel + 1
    body := Concrete.Elaboration.finishRegion state.diagram.val outer
      state.bubble items
    compiled := ?_
    environment := environment
    relationEnvironment := (relationValue, relationEnvironment)
    fixed := fixedRelationAt_push payload state relationValue binderContext
      relationEnvironment
    proxies := proxyRelationsOfParentCover_fixed payload state targets
      binderContext parent bubbleShape binderCover relationEnvironment
      relationValue
    parameters := parameterValuesOfExact_fixed state scopes outer outerExact
      environment
    denotes := denotes
  }
  · apply dropCover_to_state state
    exact Concrete.Elaboration.BinderContext.push_covers_bubble_child
      binderCoverDrop droppedBubbleShape
  · apply dropEnumeration_to_state state
    exact binderEnumerationDrop.bubbleChild dropWellFormed
      droppedBubbleShape
  · exact (drop_compileRegion_eq_survivor state (fuel + 1) state.bubble outer
      (binderContext.push state.bubble payload.arity)).symm.trans
        droppedCompiled

/-- The certified one-step simulations transport a final presentation back to
the original quantified bubble under one trace-wide relation contract. -/
noncomputable def initialBubblePresentationOfFinal
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (trace : InstantiationTrace comprehension attachments binders payload fuel
      (initialInstantiationState payload) result)
    (model : Model)
    (relationValue : Relation model.Carrier payload.arity)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (parameterValues : Fin attachments.length → model.Carrier)
    (contract : TraceRelationContract payload input model  relationValue
      values parameterValues)
    (finalPresentation : BubblePresentation payload result model
      relationValue values parameterValues) :
    BubblePresentation payload (initialInstantiationState payload) model
      relationValue values parameterValues :=
  bubblePresentation_of_trace trace model  relationValue
    values parameterValues
    (initial_regionSimulationsEveryStep trace model  relationValue values
      parameterValues contract)
    finalPresentation

/-- At the exact final compiler focus, package the selected bubble denotation
and immediately transport it back through the complete accepted copy trace.
Keeping this composition at the focus preserves the executor-selected relation
before the surrounding existential semantics hides its witness. -/
noncomputable def initialBubblePresentationOfFinalFocus
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    {comprehension : Concrete.CheckedOpen }
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {fuel : Nat}
    {result : InstantiationState input attachments.length
      payload.binderSpine.proxyCount}
    (trace : InstantiationTrace comprehension attachments binders payload fuel
      (initialInstantiationState payload) result)
    (targets : BinderTargetsAtBubble payload result)
    (scopes : ParameterScopesAtBubble result)
    (model : Model)
    {rels : RelCtx}
    (outer : Concrete.Elaboration.WireContext result.diagram.val)
    (outerExactDrop : @Concrete.Elaboration.WireContext.Exact
      (dropInstantiationAtomsRaw result) (outer.extend result.bubble)
        result.bubble)
    (dropWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed )
    (binderContext : Concrete.Elaboration.BinderContext result.diagram.val rels)
    (parent : Fin result.diagram.val.regionCount)
    (bubbleShape : result.diagram.val.regions result.bubble =
      .bubble parent payload.arity)
    (binderCoverDrop : @Concrete.Elaboration.BinderContext.Covers
      (dropInstantiationAtomsRaw result) rels binderContext parent)
    (binderEnumerationDrop :
      Concrete.Elaboration.BinderContext.Enumeration
        (dropInstantiationAtomsRaw result) binderContext parent)
    (compilerFuel : Nat)
    (items : ItemSeq  (outer.extend result.bubble).length
      (payload.arity :: rels))
    (itemsCompiled : Concrete.Elaboration.compileOccurrencesWith?
      (dropInstantiationAtomsRaw result)
      (Concrete.Elaboration.compileRegion?
        (dropInstantiationAtomsRaw result) compilerFuel)
      (outer.extend result.bubble)
      (binderContext.push result.bubble payload.arity)
      (Concrete.Elaboration.localOccurrences
        (dropInstantiationAtomsRaw result) result.bubble) = some items)
    (environment : Fin outer.length → model.Carrier)
    (relationEnvironment : RelEnv model.Carrier rels)
    (relationValue : Relation model.Carrier payload.arity)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (parameterValues : Fin attachments.length → model.Carrier)
    (contract : TraceRelationContract payload input model  relationValue
      values parameterValues)
    (parametersEq : parameterValuesOfExact result scopes outer
      (dropExact_to_state result (outer.extend result.bubble) result.bubble
        outerExactDrop) environment = parameterValues)
    (proxiesEq : proxyRelationsOfParentCover payload result targets
      binderContext parent bubbleShape
      (dropCover_to_state result binderContext parent binderCoverDrop)
      relationEnvironment = values)
    (denotes : denoteRegion (relCtx := payload.arity :: rels) model
      environment (relationValue, relationEnvironment)
      (Concrete.Elaboration.finishRegion result.diagram.val outer result.bubble
        items)) :
    BubblePresentation payload (initialInstantiationState payload) model
      relationValue values parameterValues := by
  let finalPresentation := finalBubblePresentation payload result targets scopes
    model  outer outerExactDrop dropWellFormed binderContext parent
    bubbleShape binderCoverDrop binderEnumerationDrop compilerFuel items
    itemsCompiled environment relationEnvironment relationValue denotes
  have finalPresentation' : BubblePresentation payload result model
      relationValue values parameterValues := by
    simpa only [parametersEq, proxiesEq] using finalPresentation
  exact initialBubblePresentationOfFinal trace model
    relationValue values parameterValues contract finalPresentation'

end InstantiationSemantic

end VisualProof.Rule
