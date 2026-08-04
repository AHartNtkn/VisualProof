import VisualProof.Rule.Soundness.Comprehension.SameDiagramSemantic
import VisualProof.Rule.Soundness.Comprehension.InstantiationTraceAncestor

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

/-- On every lexical ancestor of the terminal moving bubble, the total trace
preimage is the genuine source ancestor certified by the frame trace. -/
theorem traceRegionPreimage_of_encloses
    (trace : InstantiationTrace comprehension attachments binders payload fuel
      state result)
    (fallback : Fin state.diagram.val.regionCount)
    (region : Fin result.diagram.val.regionCount)
    (encloses : result.diagram.val.Encloses region result.bubble) :
    state.diagram.val.Encloses
        (traceRegionPreimage trace fallback region) state.bubble ∧
      trace.regionMap (traceRegionPreimage trace fallback region) = region := by
  obtain ⟨source, sourceEncloses, mapped⟩ :=
    trace.ancestor_preimage region encloses
  have chosenEq : traceRegionPreimage trace fallback region = source := by
    apply trace.regionMap_injective
    rw [← mapped, traceRegionPreimage_image]
  rw [chosenEq]
  exact ⟨sourceEncloses, mapped⟩

private theorem traceExternalRelation_exists
    (trace : InstantiationTrace comprehension attachments binders payload fuel
      state result)
    (sourceBinders : ConcreteElaboration.BinderContext
      result.diagram.val sourceRels)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      result.diagram.val sourceBinders result.bubble)
    (externalBinders : ConcreteElaboration.BinderContext
      state.diagram.val externalRels)
    (externalCover : externalBinders.Covers state.bubble)
    (fallback : Fin state.diagram.val.regionCount)
    {arity : Nat} (relation : RelVar sourceRels arity) :
    ∃ externalRelation : RelVar externalRels arity,
      externalBinders
          (traceRegionPreimage trace fallback
            (sourceEnumeration.binder relation.index)) =
        some ⟨arity, externalRelation⟩ := by
  let owner := sourceEnumeration.binder relation.index
  obtain ⟨targetParent, targetShape⟩ := sourceEnumeration.bubble relation.index
  rw [relation.hasArity] at targetShape
  have targetEncloses := sourceEnumeration.encloses relation.index
  have sourceFacts := traceRegionPreimage_of_encloses trace fallback owner
    targetEncloses
  let sourceOwner := traceRegionPreimage trace fallback owner
  have mappedShape := trace.regionMap_shape sourceOwner
  rw [sourceFacts.2] at mappedShape
  cases sourceShape : state.diagram.val.regions sourceOwner with
  | sheet =>
      rw [sourceShape] at mappedShape
      cases targetShape.symm.trans mappedShape
  | cut parent =>
      rw [sourceShape] at mappedShape
      cases targetShape.symm.trans mappedShape
  | bubble parent sourceArity =>
      rw [sourceShape] at mappedShape
      have arityEq : sourceArity = arity :=
        (CRegion.bubble.inj (mappedShape.symm.trans targetShape)).2
      subst sourceArity
      exact externalCover sourceOwner parent arity sourceShape sourceFacts.1

/-- Canonical relation renaming from a terminal compiler binder enumeration
to any source-state binder context covering the moving bubble. -/
noncomputable def traceExternalRelationMap
    (trace : InstantiationTrace comprehension attachments binders payload fuel
      state result)
    (sourceBinders : ConcreteElaboration.BinderContext
      result.diagram.val sourceRels)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      result.diagram.val sourceBinders result.bubble)
    (externalBinders : ConcreteElaboration.BinderContext
      state.diagram.val externalRels)
    (externalCover : externalBinders.Covers state.bubble)
    (fallback : Fin state.diagram.val.regionCount) :
    RelationRenaming sourceRels externalRels :=
  fun relation => Classical.choose
    (traceExternalRelation_exists trace sourceBinders sourceEnumeration
      externalBinders externalCover fallback relation)

theorem traceExternalRelationMap_spec
    (trace : InstantiationTrace comprehension attachments binders payload fuel
      state result)
    (sourceBinders : ConcreteElaboration.BinderContext
      result.diagram.val sourceRels)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      result.diagram.val sourceBinders result.bubble)
    (externalBinders : ConcreteElaboration.BinderContext
      state.diagram.val externalRels)
    (externalCover : externalBinders.Covers state.bubble)
    (fallback : Fin state.diagram.val.regionCount)
    {region arity} (relation : RelVar sourceRels arity)
    (lookup : sourceBinders region = some ⟨arity, relation⟩) :
    externalBinders (traceRegionPreimage trace fallback region) =
      some ⟨arity, traceExternalRelationMap trace sourceBinders
        sourceEnumeration externalBinders externalCover fallback relation⟩ := by
  have ownerEq : sourceEnumeration.binder relation.index = region :=
    sourceEnumeration.lookup_owner relation lookup
  rw [← ownerEq]
  exact Classical.choose_spec
    (traceExternalRelation_exists trace sourceBinders sourceEnumeration
      externalBinders externalCover fallback relation)

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

/-- Package a terminal presentation against a source-state lexical
environment.  Ancestor provenance supplies the binder mapping; callers retain
control of the semantic relation values through the explicit agreement. -/
noncomputable def ExternalAlignedBubblePresentation.ofTerminal
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
    {externalRels : RelCtx}
    (trace : InstantiationTrace comprehension attachments binders payload fuel
      (initialInstantiationState payload) result)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (relationValue : Relation model.Carrier payload.arity)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (parameterValues : Fin attachments.length → model.Carrier)
    (wireValue : Fin result.diagram.val.wireCount → model.Carrier)
    (presentation : BubblePresentation payload result model named relationValue
      values parameterValues)
    (wireAligned : presentation.OuterAligned wireValue)
    (externalBinders : ConcreteElaboration.BinderContext
      input.val externalRels)
    (externalCover : externalBinders.Covers bubble)
    (externalRelations : RelEnv model.Carrier externalRels)
    (fallback : Fin input.val.regionCount)
    (relationsAligned : RelEnv.Agrees
      (traceExternalRelationMap trace presentation.binderContext
        presentation.binderEnumeration externalBinders externalCover fallback)
      presentation.relationEnvironment externalRelations) :
    ExternalAlignedBubblePresentation payload result model named relationValue
      values parameterValues wireValue externalBinders externalRelations
      (traceRegionPreimage trace fallback) where
  presentation := presentation
  wireAligned := wireAligned
  relationMap := traceExternalRelationMap trace presentation.binderContext
    presentation.binderEnumeration externalBinders externalCover fallback
  binderAligned := by
    intro region arity relation lookup
    exact traceExternalRelationMap_spec trace presentation.binderContext
      presentation.binderEnumeration externalBinders externalCover fallback
      relation lookup
  relationsAligned := relationsAligned

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
  | done fuel state pending_empty =>
      exact ⟨target⟩
  | step fuel state result atom tail site candidate arguments plan
      pending_eq node_eq candidate_eq arguments_eq rest ih =>
      rcases plan with ⟨materialization, materializationChecked,
        attachmentsRespectBoundary, checkedInput, checkedInputChecked,
        nextState, next_eq⟩
      cases next_eq
      let plan : InstantiationCopyPlan comprehension attachments binders payload
          state atom tail site arguments := {
        materialization := materialization
        materializationChecked := materializationChecked
        attachmentsRespectBoundary := attachmentsRespectBoundary
        checkedInput := checkedInput
        checkedInputChecked := checkedInputChecked
        next := advanceMaterializedInstantiationState comprehension attachments
          binders payload state atom tail site arguments materialization
            (Splice.Input.checkInput_sound checkedInputChecked).2
        next_eq := rfl
      }
      rcases simulations with ⟨simulation, restSimulations⟩
      obtain ⟨nextExternal⟩ := ih restSimulations targetWireValue targetOwnerMap
        target
      let hadmissible :=
        (Splice.Input.checkInput_sound plan.checkedInputChecked).2
      let nextWireValue := targetWireValue ∘ rest.wireMap
      let nextOwnerMap := targetOwnerMap ∘ rest.regionMap
      let operationalPresentation : BubblePresentation plan.operationalPayload
          (advanceInstantiationState plan.materialization.result attachments
            binders plan.operationalPayload state atom tail site arguments
            hadmissible)
          model named relationValue values parameterValues := {
        rels := nextExternal.presentation.rels
        outer := nextExternal.presentation.outer
        outerExact := nextExternal.presentation.outerExact
        binderContext := nextExternal.presentation.binderContext
        binderCover := nextExternal.presentation.binderCover
        binderEnumeration := nextExternal.presentation.binderEnumeration
        fuel := nextExternal.presentation.fuel
        body := nextExternal.presentation.body
        compiled := nextExternal.presentation.compiled
        environment := nextExternal.presentation.environment
        relationEnvironment := nextExternal.presentation.relationEnvironment
        fixed := by
          simpa [InstantiationCopyPlan.operationalPayload,
            materializedInstantiationPayload,
            Splice.AttachmentAliasMaterialization.Certificate.spine,
            Splice.AttachmentAliasMaterialization.binderSpine] using
            nextExternal.presentation.fixed
        proxies := by
          simpa [InstantiationCopyPlan.operationalPayload,
            materializedInstantiationPayload,
            Splice.AttachmentAliasMaterialization.Certificate.spine,
            Splice.AttachmentAliasMaterialization.binderSpine] using
            nextExternal.presentation.proxies
        parameters := nextExternal.presentation.parameters
        denotes := nextExternal.presentation.denotes
      }
      have operationalWireAligned :
          operationalPresentation.OuterAligned nextWireValue := by
        intro index
        simpa [operationalPresentation, nextWireValue] using
          nextExternal.wireAligned index
      let operationalTarget : ExternalAlignedBubblePresentation
          plan.operationalPayload
          (advanceInstantiationState plan.materialization.result attachments
            binders plan.operationalPayload state atom tail site arguments
            hadmissible)
          model named relationValue values parameterValues nextWireValue
          externalBinders externalRelations nextOwnerMap := {
        presentation := operationalPresentation
        wireAligned := operationalWireAligned
        relationMap := nextExternal.relationMap
        binderAligned := by
          intro region arity relation lookup
          exact nextExternal.binderAligned region arity relation (by
            simpa [operationalPresentation] using lookup)
        relationsAligned := by
          intro arity relation
          exact nextExternal.relationsAligned arity relation
      }
      obtain ⟨coalescedExternal⟩ := coalescedExternalAligned_nonempty
        plan.materialization.result attachments binders plan.operationalPayload
        state atom tail site arguments hadmissible model named relationValue
        values parameterValues
        (fun sourceFuel targetFuel => simulation .backward sourceFuel targetFuel
          state.bubble (ConcreteDiagram.Encloses.refl _ _)) externalBinders
        externalRelations nextWireValue nextOwnerMap operationalTarget
      let spliceInput := plan.spliceInput
      let sourcePresentation := bubblePresentation_of_coalesced
        plan.materialization.result attachments binders plan.operationalPayload
        state site arguments hadmissible plan.attachmentsRespectBoundary model
        named relationValue values parameterValues
        coalescedExternal.presentation
      have sourceWireAligned : sourcePresentation.OuterAligned
          ((nextWireValue ∘ spliceInput.plugLayout.frameWire) ∘
            spliceInput.quotientWire) := by
        exact bubblePresentation_of_coalesced_outerAligned
          plan.materialization.result attachments binders
          plan.operationalPayload state site arguments hadmissible
          plan.attachmentsRespectBoundary model named relationValue values
          parameterValues coalescedExternal.presentation
          (nextWireValue ∘ spliceInput.plugLayout.frameWire)
          coalescedExternal.wireAligned
      let originalPresentation : BubblePresentation payload state model named
          relationValue values parameterValues := {
        rels := sourcePresentation.rels
        outer := sourcePresentation.outer
        outerExact := sourcePresentation.outerExact
        binderContext := sourcePresentation.binderContext
        binderCover := sourcePresentation.binderCover
        binderEnumeration := sourcePresentation.binderEnumeration
        fuel := sourcePresentation.fuel
        body := sourcePresentation.body
        compiled := sourcePresentation.compiled
        environment := sourcePresentation.environment
        relationEnvironment := sourcePresentation.relationEnvironment
        fixed := by
          simpa [InstantiationCopyPlan.operationalPayload,
            materializedInstantiationPayload,
            Splice.AttachmentAliasMaterialization.Certificate.spine,
            Splice.AttachmentAliasMaterialization.binderSpine] using
            sourcePresentation.fixed
        proxies := by
          simpa [InstantiationCopyPlan.operationalPayload,
            materializedInstantiationPayload,
            Splice.AttachmentAliasMaterialization.Certificate.spine,
            Splice.AttachmentAliasMaterialization.binderSpine] using
            sourcePresentation.proxies
        parameters := sourcePresentation.parameters
        denotes := sourcePresentation.denotes
      }
      let sourceExternal : ExternalAlignedBubblePresentation payload state
          model named relationValue values parameterValues
          ((nextWireValue ∘ spliceInput.plugLayout.frameWire) ∘
            spliceInput.quotientWire)
          externalBinders externalRelations
          (nextOwnerMap ∘ spliceInput.plugLayout.frameRegion) := {
        presentation := originalPresentation
        wireAligned := by
          intro index
          simpa [originalPresentation] using sourceWireAligned index
        relationMap := coalescedExternal.relationMap
        binderAligned := by
          intro region arity relation lookup
          apply coalescedExternal.binderAligned region arity relation
          simpa [originalPresentation, sourcePresentation,
            bubblePresentation_of_coalesced] using lookup
        relationsAligned := by
          intro arity relation
          exact coalescedExternal.relationsAligned arity relation
      }
      refine ⟨?_ ⟩
      simpa [sourceExternal, nextWireValue, nextOwnerMap, spliceInput,
        Function.comp_def, InstantiationTrace.wireMap,
        InstantiationTrace.regionMap] using sourceExternal

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
  Classical.choice (externalAligned_nonempty_of_trace trace model named
    relationValue values parameterValues simulations externalBinders
    externalRelations targetWireValue targetOwnerMap target)

/-- A fully aligned presentation returned to the initial executor state can be
recompiled by the authoritative compiler in any exact context for the original
bubble.  Alignment supplies both environment agreement and binder provenance. -/
theorem ExternalAlignedBubblePresentation.denoteRecompiled_initial
    {signature : List Nat}
    {input : CheckedDiagram signature}
    {bubble : Fin input.val.regionCount}
    {comprehension : CheckedOpenDiagram signature}
    {attachments : List (Fin input.val.wireCount)}
    {binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
    {payload : ComprehensionInstantiatePayload input bubble comprehension
      attachments binders}
    {model : Lambda.LambdaModel}
    {named : NamedEnv model.Carrier signature}
    {relationValue : Relation model.Carrier payload.arity}
    {values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index)}
    {parameterValues : Fin attachments.length → model.Carrier}
    {wireValue : Fin input.val.wireCount → model.Carrier}
    {externalRels : RelCtx}
    {externalBinders : ConcreteElaboration.BinderContext input.val externalRels}
    {externalRelations : RelEnv model.Carrier externalRels}
    {ownerMap : Fin input.val.regionCount → Fin input.val.regionCount}
    (aligned : ExternalAlignedBubblePresentation payload
      (initialInstantiationState payload) model named relationValue values
      parameterValues wireValue externalBinders externalRelations ownerMap)
    (ownerIdentity : ∀ region, ownerMap region = region)
    (targetOuter : ConcreteElaboration.WireContext input.val)
    (targetExact : (targetOuter.extend bubble).Exact bubble)
    (targetCover : externalBinders.Covers bubble)
    (targetEnumeration : ConcreteElaboration.BinderContext.Enumeration
      input.val externalBinders bubble)
    (targetFuel : Nat)
    (targetBody : Region signature targetOuter.length externalRels)
    (targetCompiled : ConcreteElaboration.compileRegion? signature input.val
      targetFuel bubble targetOuter externalBinders = some targetBody)
    (targetEnvironment : Fin targetOuter.length → model.Carrier)
    (targetAligned : ∀ index, targetEnvironment index =
      wireValue (targetOuter.get index)) :
    denoteRegion model named targetEnvironment externalRelations targetBody := by
  let source := aligned.presentation
  let context := SameDiagramContext.ofExact bubble source.outer targetOuter
    source.outerExact targetExact
  let binderWitness : SameDiagramBinderWitness input.val source.binderContext
      externalBinders := {
    relationMap := aligned.relationMap
    mapped := by
      intro region arity relation lookup
      simpa [ownerIdentity region] using
        aligned.binderAligned region arity relation lookup
  }
  have sourceCompiled : ConcreteElaboration.compileRegion? signature input.val
      source.fuel bubble source.outer source.binderContext = some source.body := by
    have compilerEq := compileSurvivorRegion_eq_of_clean_subtree
      (signature := signature) (state := initialInstantiationState payload)
      source.fuel bubble source.outer source.binderContext (by
        intro node member
        exact False.elim (List.not_mem_nil member))
    have compilerEq' : compileSurvivorRegion? signature
        (initialInstantiationState payload) source.fuel bubble source.outer
          source.binderContext =
        ConcreteElaboration.compileRegion? signature input.val source.fuel
          bubble source.outer source.binderContext := by
      simpa [initialInstantiationState] using compilerEq
    rw [← compilerEq']
    simpa [source] using source.compiled
  let simulation := sameDiagramSemanticSimulation input.val input.property
    model named
  have bodySimulation := simulation.compileRegion_denote .forward source.fuel
    targetFuel bubble source.outer targetOuter context trivial
    source.binderContext externalBinders trivial binderWitness source.binderCover
    targetCover source.binderEnumeration targetEnumeration source.outerExact
    targetExact source.body targetBody sourceCompiled targetCompiled
  have environmentAgreement : context.indexRelation.EnvironmentsAgree
      source.environment targetEnvironment := by
    apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
      context.index source.environment targetEnvironment).mpr
    funext index
    simp only [Function.comp_apply]
    rw [aligned.wireAligned index, targetAligned (context.index index),
      context.get index]
    rfl
  have sourceRenamed : denoteRegion model named source.environment
      externalRelations (source.body.renameRelations aligned.relationMap) :=
    (denoteRegion_renameRelations model named aligned.relationMap
      source.relationEnvironment externalRelations aligned.relationsAligned
      source.environment source.body).mpr source.denotes
  exact bodySimulation source.environment targetEnvironment externalRelations
    environmentAgreement sourceRenamed

end InstantiationSemantic

end VisualProof.Rule
