import VisualProof.Rule.Soundness.Comprehension.SameDiagramSemantic

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- A total inverse with a harmless fallback outside an executor trace's
region image.  Soundness uses it only at compiler binder owners, all of which
are certified images. -/
noncomputable def traceRegionPreimage
    (trace : InstantiationTrace comprehension attachments binders payload fuel
      state result)
    (fallback : Fin state.diagram.val.regionCount)
    (region : Fin result.diagram.val.regionCount) :
    Fin state.diagram.val.regionCount :=
  if image : ∃ source, trace.regionMap source = region then
    Classical.choose image
  else fallback

@[simp] theorem traceRegionPreimage_image
    (trace : InstantiationTrace comprehension attachments binders payload fuel
      state result)
    (fallback source) :
    traceRegionPreimage trace fallback (trace.regionMap source) = source := by
  unfold traceRegionPreimage
  have image : ∃ candidate,
      trace.regionMap candidate = trace.regionMap source := ⟨source, rfl⟩
  rw [dif_pos image]
  exact trace.regionMap_injective
    (Classical.choose_spec image)

/-- A semantic presentation aligned simultaneously with a total state-wire
valuation and an external relation environment.  `ownerMap` records concrete
binder provenance; `relationMap` records the corresponding intrinsic variable
renaming. -/
structure ExternalAlignedBubblePresentation
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
    (wireValue : Fin state.diagram.val.wireCount → model.Carrier)
    {externalRels : RelCtx}
    (externalBinders : ConcreteElaboration.BinderContext input.val externalRels)
    (externalRelations : RelEnv model.Carrier externalRels)
    (ownerMap : Fin state.diagram.val.regionCount →
      Fin input.val.regionCount) where
  presentation : BubblePresentation payload state model named relationValue
    values parameterValues
  wireAligned : presentation.OuterAligned wireValue
  relationMap : RelationRenaming presentation.rels externalRels
  binderAligned : ∀ region arity
      (relation : RelVar presentation.rels arity),
    presentation.binderContext region = some ⟨arity, relation⟩ →
      externalBinders (ownerMap region) =
        some ⟨arity, relationMap relation⟩
  relationsAligned : RelEnv.Agrees relationMap
    presentation.relationEnvironment externalRelations

theorem coalescedExternalAligned_nonempty
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
    {externalRels : RelCtx}
    (externalBinders : ConcreteElaboration.BinderContext input.val externalRels)
    (externalRelations : RelEnv model.Carrier externalRels)
    (targetWireValue : Fin
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val.wireCount →
        model.Carrier)
    (targetOwnerMap : Fin
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val.regionCount →
        Fin input.val.regionCount)
    (target : ExternalAlignedBubblePresentation payload
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible)
      model named relationValue values parameterValues targetWireValue
      externalBinders externalRelations targetOwnerMap) :
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let coalesced := coalescedInstantiationState comprehension attachments
      binders payload state site arguments hadmissible
    Nonempty (ExternalAlignedBubblePresentation payload coalesced model named
      relationValue values parameterValues
      (targetWireValue ∘ spliceInput.plugLayout.frameWire)
      externalBinders externalRelations
      (targetOwnerMap ∘ spliceInput.plugLayout.frameRegion)) := by
  dsimp only
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let coalesced := coalescedInstantiationState comprehension attachments
    binders payload state site arguments hadmissible
  let source := coalescedBubblePresentation_of_target comprehension attachments
    binders payload state atom tail site arguments hadmissible model named
    relationValue values parameterValues simulations target.presentation
  let sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      spliceInput.coalesceFrameRaw source.binderContext state.bubble := by
    simpa [source, coalesced, spliceInput] using source.binderEnumeration
  let frameMap : RelationRenaming source.rels target.presentation.rels :=
    frameRelationMap spliceInput state.bubble
    source.binderContext sourceEnumeration target.presentation.binderContext
    (by
      simpa [advanceInstantiationState, spliceInput] using
        target.presentation.binderCover)
  let externalMap : RelationRenaming source.rels externalRels :=
    fun relation => target.relationMap (frameMap relation)
  refine ⟨{
    presentation := source
    wireAligned := coalescedBubblePresentation_of_target_outerAligned
      comprehension attachments binders payload state atom tail site arguments
      hadmissible model named relationValue values parameterValues simulations
      target.presentation targetWireValue target.wireAligned
    relationMap := externalMap
    binderAligned := ?_
    relationsAligned := ?_
  }⟩
  · intro region arity relation sourceLookup
    have ownerEq : sourceEnumeration.binder relation.index = region :=
      sourceEnumeration.lookup_owner relation (by
        simpa [sourceEnumeration, spliceInput, coalesced, source] using
          sourceLookup)
    have frameLookup := frameRelationMap_spec spliceInput state.bubble
      source.binderContext sourceEnumeration target.presentation.binderContext
      (by
        simpa [advanceInstantiationState, spliceInput] using
          target.presentation.binderCover) relation
    rw [ownerEq] at frameLookup
    exact target.binderAligned _ arity (frameMap relation) (by
      simpa [frameMap] using frameLookup)
  · intro arity relation
    change source.relationEnvironment.lookup relation =
      externalRelations.lookup (target.relationMap (frameMap relation))
    have pulled : source.relationEnvironment.lookup relation =
        target.presentation.relationEnvironment.lookup (frameMap relation) := by
      simpa [source, coalescedBubblePresentation_of_target, frameMap,
        sourceEnumeration, coalesced, spliceInput] using
        (RelEnv.pullback_agrees frameMap
          target.presentation.relationEnvironment arity relation)
    exact pulled.trans
      (target.relationsAligned arity (frameMap relation))

theorem externalAligned_nonempty_of_trace
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
    {externalRels : RelCtx}
    (externalBinders : ConcreteElaboration.BinderContext input.val externalRels)
    (externalRelations : RelEnv model.Carrier externalRels)
    (targetWireValue : Fin result.diagram.val.wireCount → model.Carrier)
    (targetOwnerMap : Fin result.diagram.val.regionCount →
      Fin input.val.regionCount)
    (target : ExternalAlignedBubblePresentation payload result model named
      relationValue values parameterValues targetWireValue externalBinders
      externalRelations targetOwnerMap) :
    Nonempty (ExternalAlignedBubblePresentation payload state model named
      relationValue values parameterValues (targetWireValue ∘ trace.wireMap)
      externalBinders externalRelations (targetOwnerMap ∘ trace.regionMap)) := by
  induction trace with
  | done =>
      exact ⟨{
        presentation := target.presentation
        wireAligned := by simpa [InstantiationTrace.wireMap] using
          target.wireAligned
        relationMap := target.relationMap
        binderAligned := by simpa [InstantiationTrace.regionMap] using
          target.binderAligned
        relationsAligned := target.relationsAligned
      }⟩
  | step fuel state result atom tail site candidate arguments checkedInput
      pending_eq node_eq candidate_eq arguments_eq input_eq rest ih =>
      rcases simulations with ⟨stepSimulations, restSimulations⟩
      obtain ⟨next⟩ := ih restSimulations targetWireValue targetOwnerMap target
      let hadmissible := (Splice.Input.checkInput_sound input_eq).2
      obtain ⟨coalesced⟩ := coalescedExternalAligned_nonempty comprehension
        attachments binders payload state atom tail site arguments hadmissible
        model named relationValue values parameterValues
        (fun sourceFuel targetFuel =>
          stepSimulations .backward sourceFuel targetFuel state.bubble
            (ConcreteDiagram.Encloses.refl state.diagram.val state.bubble))
        externalBinders externalRelations (targetWireValue ∘ rest.wireMap)
        (targetOwnerMap ∘ rest.regionMap) next
      let spliceInput := instantiateSpliceInput comprehension attachments
        binders payload state site arguments
      let sourcePresentation := bubblePresentation_of_coalesced comprehension
        attachments binders payload state site arguments hadmissible
        boundaryNodup model named relationValue values parameterValues
        coalesced.presentation
      let actualIso := Splice.Input.coalescedFrameIsoOfBoundaryNodup spliceInput
        boundaryNodup
      refine ⟨{
        presentation := sourcePresentation
        wireAligned := bubblePresentation_of_coalesced_outerAligned
          comprehension attachments binders payload state site arguments
          hadmissible boundaryNodup model named relationValue values
          parameterValues coalesced.presentation
          ((targetWireValue ∘ rest.wireMap) ∘
            spliceInput.plugLayout.frameWire) coalesced.wireAligned
        relationMap := coalesced.relationMap
        binderAligned := ?_
        relationsAligned := coalesced.relationsAligned
      }⟩
      · intro region arity relation sourceLookup
        change coalesced.presentation.binderContext
            (actualIso.regions.invFun region) = some ⟨arity, relation⟩
          at sourceLookup
        have mapped := coalesced.binderAligned
          (actualIso.regions.invFun region) arity relation sourceLookup
        simpa [InstantiationTrace.regionMap, advanceInstantiationState,
          sourcePresentation, actualIso, spliceInput, Function.comp_def] using
          mapped

/-- Canonical fully aligned presentation transported through a complete
accepted executor trace. -/
noncomputable def externalAligned_of_trace
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
    {externalRels : RelCtx}
    (externalBinders : ConcreteElaboration.BinderContext input.val externalRels)
    (externalRelations : RelEnv model.Carrier externalRels)
    (targetWireValue : Fin result.diagram.val.wireCount → model.Carrier)
    (targetOwnerMap : Fin result.diagram.val.regionCount →
      Fin input.val.regionCount)
    (target : ExternalAlignedBubblePresentation payload result model named
      relationValue values parameterValues targetWireValue externalBinders
      externalRelations targetOwnerMap) :
    ExternalAlignedBubblePresentation payload state model named relationValue
      values parameterValues (targetWireValue ∘ trace.wireMap) externalBinders
      externalRelations (targetOwnerMap ∘ trace.regionMap) :=
  Classical.choice (externalAligned_nonempty_of_trace trace boundaryNodup model
    named relationValue values parameterValues simulations externalBinders
    externalRelations targetWireValue targetOwnerMap target)

end InstantiationSemantic

end VisualProof.Rule
