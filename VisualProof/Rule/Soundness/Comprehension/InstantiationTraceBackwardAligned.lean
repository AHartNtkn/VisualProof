import VisualProof.Rule.Soundness.Comprehension.InstantiationTraceBackward

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- A bubble presentation whose inherited valuation is the restriction of one
wire-indexed valuation on the executor state. -/
def BubblePresentation.OuterAligned
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {origin : CheckedDiagram signature}
    {state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount}
    {model : Lambda.LambdaModel}
    {named : NamedEnv model.Carrier signature}
    {relationValue : Relation model.Carrier payload.arity}
    {values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index)}
    {parameterValues : Fin attachments.length → model.Carrier}
    (presentation : BubblePresentation payload state model named relationValue
      values parameterValues)
    (wireValue : Fin state.diagram.val.wireCount → model.Carrier) : Prop :=
  ∀ index, presentation.environment index =
    wireValue (presentation.outer.get index)

theorem coalescedBubblePresentation_of_target_outerAligned
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpenDiagram signature)
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (atom : Fin state.diagram.val.nodeCount)
    (tail : List (Fin state.diagram.val.nodeCount))
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (relationValue : Relation model.Carrier payload.arity)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (parameterValues : Fin attachments.length → model.Carrier)
    (simulations : ∀ sourceFuel targetFuel,
      FixedAdvanceRegionSimulation comprehension attachments binders payload
        state atom tail site arguments hadmissible model named relationValue
        values parameterValues .backward sourceFuel targetFuel state.bubble)
    (target : BubblePresentation payload
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible)
      model named relationValue values parameterValues)
    (targetWireValue : Fin
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val.wireCount →
        model.Carrier)
    (aligned : target.OuterAligned targetWireValue) :
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let source := coalescedBubblePresentation_of_target comprehension
      attachments binders payload state atom tail site arguments hadmissible
      model named relationValue values parameterValues simulations target
    source.OuterAligned (targetWireValue ∘ spliceInput.plugLayout.frameWire) := by
  dsimp only
  intro index
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let coalesced := coalescedInstantiationState comprehension attachments binders
    payload state site arguments hadmissible
  let sourceView := droppedBubbleView coalesced
  let sourceLeaf := sourceView.compilerLeaf
  let sourceOuter := sourceLeaf.inheritedWires
  let targetExact : (target.outer.extend
      (spliceInput.plugLayout.frameRegion state.bubble)).Exact
      (spliceInput.plugLayout.frameRegion state.bubble) := by
    simpa [spliceInput, advanceInstantiationState] using target.outerExact
  let sourceExact : @ConcreteElaboration.WireContext.Exact
      coalesced.diagram.val (sourceOuter.extend state.bubble) state.bubble := by
    apply exact_of_drop coalesced
    simpa [sourceOuter, sourceLeaf, sourceView] using sourceLeaf.wiresExact
  let outerMap := frameInheritedIndex spliceInput state.bubble sourceOuter
    target.outer sourceExact targetExact
  change target.environment (outerMap index) =
    targetWireValue (spliceInput.plugLayout.frameWire (sourceOuter.get index))
  rw [aligned]
  exact congrArg targetWireValue
    (frameInheritedIndex_spec spliceInput state.bubble sourceOuter target.outer
      sourceExact targetExact index)

theorem bubblePresentation_of_coalesced_outerAligned
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    (comprehension : CheckedOpenDiagram signature)
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (site : Fin state.diagram.val.regionCount)
    (arguments : Fin payload.arity → Fin state.diagram.val.wireCount)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (boundaryNodup : comprehension.val.boundary.Nodup)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (relationValue : Relation model.Carrier payload.arity)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (parameterValues : Fin attachments.length → model.Carrier)
    (source : BubblePresentation payload
      (coalescedInstantiationState comprehension attachments binders payload
        state site arguments hadmissible)
      model named relationValue values parameterValues)
    (sourceWireValue : Fin
      (coalescedInstantiationState comprehension attachments binders payload
        state site arguments hadmissible).diagram.val.wireCount → model.Carrier)
    (aligned : source.OuterAligned sourceWireValue) :
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let target := bubblePresentation_of_coalesced comprehension attachments
      binders payload state site arguments hadmissible boundaryNodup model named
      relationValue values parameterValues source
    target.OuterAligned (sourceWireValue ∘ spliceInput.quotientWire) := by
  dsimp only
  intro index
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let coalesced := coalescedInstantiationState comprehension attachments binders
    payload state site arguments hadmissible
  let actualIso := Splice.Input.coalescedFrameIsoOfBoundaryNodup spliceInput
    boundaryNodup
  let targetView := droppedBubbleView state
  let targetLeaf := targetView.compilerLeaf
  let targetOuter := targetLeaf.inheritedWires
  let sourceExact : @ConcreteElaboration.WireContext.Exact
      spliceInput.coalesceFrameRaw (source.outer.extend state.bubble)
      state.bubble := by
    simpa [coalesced, spliceInput] using source.outerExact
  let targetExact : @ConcreteElaboration.WireContext.Exact state.diagram.val
      (targetOuter.extend state.bubble) state.bubble := by
    apply exact_of_drop state
    simpa [targetOuter, targetLeaf, targetView] using targetLeaf.wiresExact
  let ambient := inheritedWireEquivIso actualIso state.bubble source.outer
    targetOuter sourceExact targetExact
  let sourceIndex := ambient.invFun index
  have mapped := inheritedWireEquivIso_spec actualIso state.bubble source.outer
    targetOuter sourceExact targetExact sourceIndex
  have mappedAtIndex : targetOuter.get index =
      actualIso.wires (source.outer.get sourceIndex) := by
    rw [ambient.right_inv index] at mapped
    exact mapped
  change source.environment sourceIndex =
    sourceWireValue (spliceInput.quotientWire (targetOuter.get index))
  rw [aligned, mappedAtIndex]
  change sourceWireValue (source.outer.get sourceIndex) =
    sourceWireValue (spliceInput.quotientWire
      (Splice.Input.discreteQuotientWireEquiv spliceInput boundaryNodup
        (source.outer.get sourceIndex)))
  rw [show spliceInput.quotientWire
      (Splice.Input.discreteQuotientWireEquiv spliceInput boundaryNodup
        (source.outer.get sourceIndex)) = source.outer.get sourceIndex by
    exact (Splice.Input.discreteQuotientWireEquiv spliceInput
      boundaryNodup).left_inv _]

/-- A bubble presentation paired with the fact that its inherited environment
is the restriction of a single valuation on the executor state. -/
structure AlignedBubblePresentation
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    (payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : CheckedDiagram signature}
    (state : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (relationValue : Relation model.Carrier payload.arity)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (parameterValues : Fin attachments.length → model.Carrier)
    (wireValue : Fin state.diagram.val.wireCount → model.Carrier) where
  presentation : BubblePresentation payload state model named relationValue
    values parameterValues
  aligned : presentation.OuterAligned wireValue

/-- Backward semantic transport over the complete executor trace preserves
alignment with the composite trace wire map. -/
theorem alignedBubblePresentation_nonempty_of_trace
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {origin : CheckedDiagram signature}
    {fuel : Nat}
    {state result : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount}
    (trace : InstantiationTrace comprehension attachments binders payload fuel
      state result)
    (boundaryNodup : comprehension.val.boundary.Nodup)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (relationValue : Relation model.Carrier payload.arity)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (parameterValues : Fin attachments.length → model.Carrier)
    (simulations : RegionSimulationsEveryStep trace model named relationValue
      values parameterValues)
    (targetWireValue : Fin result.diagram.val.wireCount → model.Carrier)
    (target : AlignedBubblePresentation payload result model named relationValue
      values parameterValues targetWireValue) :
    Nonempty (AlignedBubblePresentation payload state model named relationValue
      values parameterValues (targetWireValue ∘ trace.wireMap)) := by
  sorry

/-- Canonical aligned presentation extracted from the propositional trace
composition theorem. -/
noncomputable def alignedBubblePresentation_of_trace
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {origin : CheckedDiagram signature}
    {fuel : Nat}
    {state result : InstantiationState origin attachments.length
      payload.binderSpine.proxyCount}
    (trace : InstantiationTrace comprehension attachments binders payload fuel
      state result)
    (boundaryNodup : comprehension.val.boundary.Nodup)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (relationValue : Relation model.Carrier payload.arity)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (parameterValues : Fin attachments.length → model.Carrier)
    (simulations : RegionSimulationsEveryStep trace model named relationValue
      values parameterValues)
    (targetWireValue : Fin result.diagram.val.wireCount → model.Carrier)
    (target : AlignedBubblePresentation payload result model named relationValue
      values parameterValues targetWireValue) :
    AlignedBubblePresentation payload state model named relationValue values
      parameterValues (targetWireValue ∘ trace.wireMap) :=
  Classical.choice (alignedBubblePresentation_nonempty_of_trace trace
    boundaryNodup model named relationValue values parameterValues simulations
    targetWireValue target)

end InstantiationSemantic

end VisualProof.Rule
