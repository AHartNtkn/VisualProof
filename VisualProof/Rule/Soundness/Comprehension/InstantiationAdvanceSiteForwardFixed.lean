import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvanceSiteForward

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- Zero-spine forward site transport.  The current source atom exposes the
authoritative open-pattern witness; its hidden-root valuation is installed in
the executor's exact material-local block. -/
theorem advance_site_items_denote_empty_fixed_forward
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
    (node_eq : state.diagram.val.nodes atom = .atom site state.bubble)
    (arguments_eq : instantiateArguments? state atom payload.arity =
      some arguments)
    (pending_eq : state.pendingAtoms = atom :: tail)
    (ownedNodup : state.ownedAtoms.Nodup)
    (shape : BubbleHasPayloadArity payload state)
    (targets : BinderTargetsAtBubble payload state)
    (hzero : payload.binderSpine.proxyCount = 0)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (sourceFuel targetFuel : Nat)
    (sourceOuter : ConcreteElaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw)
    (targetOuter : ConcreteElaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw)
    (sourceExact : (sourceOuter.extend site).Exact site)
    (targetExact : (targetOuter.extend
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site)).Exact
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site))
    (sourceBinders : ConcreteElaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw targetRels)
    (sourceCover : sourceBinders.Covers site)
    (targetCover : targetBinders.Covers
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site))
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceBinders site)
    (targetEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw targetBinders
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site))
    (outerMap : Fin sourceOuter.length → Fin targetOuter.length)
    (outerSpec : ∀ index, targetOuter.get (outerMap index) =
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameWire (sourceOuter.get index))
    (relationMap : RelationRenaming sourceRels targetRels)
    (relationSpec : ∀ {arity} (relation : RelVar sourceRels arity),
      targetBinders
          ((instantiateSpliceInput comprehension attachments binders payload
            state site arguments).plugLayout.frameRegion
            (sourceEnumeration.binder relation.index)) =
        some ⟨arity, relationMap relation⟩)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (relationValue : Relation model.Carrier payload.arity)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (parameterValues : Fin attachments.length → model.Carrier)
    (sourceOuterEnv : Fin sourceOuter.length → model.Carrier)
    (targetOuterEnv : Fin targetOuter.length → model.Carrier)
    (targetRelEnv : RelEnv model.Carrier targetRels)
    (outerAgrees :
      (ConcreteElaboration.ContextIndexRelation.forwardMap outerMap)
        |>.EnvironmentsAgree sourceOuterEnv targetOuterEnv)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw site).length → model.Carrier)
    (sourceItems : ItemSeq signature (sourceOuter.extend site).length sourceRels)
    (targetItems : ItemSeq signature (targetOuter.extend
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site)).length targetRels)
    (fullItems : ItemSeq signature (targetOuter.extend
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site)).length targetRels)
    (sourceCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw
      (compileSurvivorRegion? signature
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible) sourceFuel)
      (sourceOuter.extend site) sourceBinders
      ((ConcreteElaboration.localOccurrences
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible).diagram.val site).filter
        (dropOccurrenceSurvives
          (coalescedInstantiationState comprehension attachments binders payload
            state site arguments hadmissible))) = some sourceItems)
    (targetCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val
      (compileSurvivorRegion? signature
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible) targetFuel)
      (targetOuter.extend
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion site)) targetBinders
      ((ConcreteElaboration.localOccurrences
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible).diagram.val
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion site)).filter
        (dropOccurrenceSurvives
          (advanceInstantiationState comprehension attachments binders payload
            state atom tail site arguments hadmissible))) = some targetItems)
    (fullCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw
      (ConcreteElaboration.compileRegion? signature
        (instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.plugRaw targetFuel)
      (targetOuter.extend
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion site)) targetBinders
      (ConcreteElaboration.localOccurrences
        (instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.plugRaw
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion site)) = some fullItems)
    (sourceDenotes : denoteItemSeq model named
      (ConcreteElaboration.extendedEnvironment sourceOuter site sourceOuterEnv
        sourceLocal)
      (RelEnv.pullback relationMap targetRelEnv) sourceItems)
    (targetFixed : FixedRelationAt payload
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible)
      relationValue targetBinders targetRelEnv)
    (targetProxies : ProxyRelationsAt payload
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible)
      targetBinders targetRelEnv values)
    (targetParameters : ParameterValuesAt
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible)
      targetOuter targetOuterEnv parameterValues)
    (relationEq : relationValue =
      payload.interpretedRelation model named parameterValues)
    (childSimulation : ∀ direction
      (child : Fin state.diagram.val.regionCount),
      FixedAdvanceRegionSimulation comprehension attachments binders payload
        state atom tail site arguments hadmissible model named relationValue
        values parameterValues direction sourceFuel targetFuel child) :
    ∃ targetLocal : Fin (ConcreteElaboration.exactScopeWires
        (instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.plugRaw
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion site)).length → model.Carrier,
      denoteItemSeq model named
        (ConcreteElaboration.extendedEnvironment targetOuter
          ((instantiateSpliceInput comprehension attachments binders payload
            state site arguments).plugLayout.frameRegion site) targetOuterEnv
          targetLocal)
        targetRelEnv targetItems := by
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let coalesced := coalescedInstantiationState comprehension attachments binders
    payload state site arguments hadmissible
  let next := advanceInstantiationState comprehension attachments binders
    payload state atom tail site arguments hadmissible
  let sourceContext := sourceOuter.extend site
  let targetContext := targetOuter.extend (layout.frameRegion site)
  let sourceEnv := ConcreteElaboration.extendedEnvironment sourceOuter site
    sourceOuterEnv sourceLocal
  let fallback : model.Carrier :=
    model.eval (Lambda.Term.lam (Lambda.Term.bvar 0) :
      Lambda.Term 0 (Fin 0)) Fin.elim0
  have outerEq : sourceOuterEnv = targetOuterEnv ∘ outerMap := by
    simpa using outerAgrees
  let dummyHidden : Fin comprehension.val.hiddenWires.length → model.Carrier :=
    fun _ => fallback
  let preliminaryLocal := siteTargetLocalOfEmpty layout hzero sourceLocal
    dummyHidden
  let preliminaryEnv := ConcreteElaboration.extendedEnvironment targetOuter
    (layout.frameRegion site) targetOuterEnv preliminaryLocal
  let wireMap := siteForwardHostWireMapOfEmpty layout hzero sourceOuter
    targetOuter outerMap
  have wireSpec : ∀ index, targetContext.get (wireMap index) =
      layout.frameWire (sourceContext.get index) :=
    siteForwardHostWireMapOfEmpty_spec layout hzero sourceOuter targetOuter
      outerMap outerSpec
  have preliminaryEnvironmentEq : sourceEnv = preliminaryEnv ∘ wireMap :=
    siteForwardHostEnvironmentsAgreeOfEmpty layout hzero sourceOuter targetOuter
      outerMap sourceOuterEnv targetOuterEnv outerEq sourceLocal dummyHidden
  let quotientValues := Splice.Input.siteQuotientEnvironment spliceInput
    targetContext targetExact preliminaryEnv fallback
  have quotientAtSource : ∀ index,
      quotientValues (sourceContext.get index) = sourceEnv index := by
    exact siteQuotientEnvironment_of_frameMap spliceInput sourceContext
      targetContext sourceExact targetExact wireMap wireSpec sourceEnv
      preliminaryEnv preliminaryEnvironmentEq fallback
  obtain ⟨sourceRelation, sourceLookup⟩ :=
    coalesced_bubbleRelation_exists comprehension attachments binders payload
      state atom site arguments node_eq hadmissible shape sourceBinders
      sourceCover
  have sourceFixed := fixedRelationAt_pullback_frame comprehension attachments
    binders payload state atom tail site arguments hadmissible site sourceBinders
    targetBinders sourceEnumeration relationMap relationSpec model relationValue
    targetRelEnv targetFixed
  have relationTruth := coalesced_survivor_items_entail_fixedRelation
    comprehension attachments binders payload state atom tail site arguments
    node_eq arguments_eq pending_eq ownedNodup hadmissible model named
    quotientValues relationValue sourceFuel sourceContext sourceBinders
    (RelEnv.pullback relationMap targetRelEnv) sourceFixed sourceRelation
    sourceLookup sourceEnv (fun index => (quotientAtSource index).symm)
    sourceItems sourceCompiled sourceDenotes
  have preliminaryParameters : ParameterValuesAt next targetContext
      preliminaryEnv parameterValues :=
    ParameterValuesAt.extend next targetOuter targetOuterEnv parameterValues
      targetParameters (layout.frameRegion site) preliminaryLocal
  have quotientParameters :
      (fun index => quotientValues
        (spliceInput.quotientWire (state.parameters index))) =
      parameterValues := by
    funext position
    exact siteQuotientEnvironment_parameter comprehension attachments binders
      payload state atom tail site arguments hadmissible targetContext
      targetExact preliminaryEnv parameterValues preliminaryParameters
      fallback position
  have patternDenotes : comprehension.denote model named
      (Fin.addCases
        (fun index => quotientValues
          (spliceInput.quotientWire (arguments index)))
        parameterValues ∘ Fin.cast payload.boundarySplit) := by
    apply (payload.interpretedRelation_apply model named parameterValues _).mp
    rw [← relationEq]
    exact relationTruth
  have attachmentValues :
      (fun position => quotientValues
        (spliceInput.quotientWire (spliceInput.attachment position))) =
      Fin.addCases
        (fun index => quotientValues
          (spliceInput.quotientWire (arguments index)))
        parameterValues ∘ Fin.cast payload.boundarySplit := by
    funext position
    let split := Fin.cast payload.boundarySplit position
    have recover : Fin.cast payload.boundarySplit.symm split = position := by
      apply Fin.ext
      rfl
    rw [← recover]
    refine Fin.addCases (fun argument => ?_) (fun parameter => ?_) split
    · simp [spliceInput, instantiateSpliceInput, Function.comp_def]
    · simpa [spliceInput, instantiateSpliceInput, Function.comp_def] using
        congrFun quotientParameters parameter
  have patternAtQuotient : comprehension.denote model named
      (fun position => quotientValues
        (spliceInput.quotientWire (spliceInput.attachment position))) := by
    exact Eq.mp
      (congrArg (fun arguments => comprehension.denote model named arguments)
        attachmentValues.symm) patternDenotes
  let pattern := Splice.Input.compiledSpliceOpenRootItems comprehension
  obtain ⟨hiddenEnv, nativePatternDenotes⟩ :=
    Splice.Input.patternRootItems_of_pattern_denote spliceInput model named
      quotientValues patternAtQuotient
  let targetLocal := Splice.Input.focusedLocalEnvironmentOfEmpty spliceInput
    hzero quotientValues hiddenEnv
  refine ⟨targetLocal, ?_⟩
  let targetEnv := ConcreteElaboration.extendedEnvironment targetOuter
    (layout.frameRegion site) targetOuterEnv targetLocal
  have hostValues : ∀ index, quotientValues
      ((ConcreteElaboration.exactScopeWires spliceInput.coalesceFrameRaw
        site).get index) = sourceLocal index := by
    intro index
    let sourceIndex : Fin sourceContext.length := Fin.cast
      (ConcreteElaboration.WireContext.length_extend sourceOuter site).symm
      (Fin.natAdd sourceOuter.length index)
    have quotientEq := quotientAtSource sourceIndex
    have sourceWire : sourceContext.get sourceIndex =
        (ConcreteElaboration.exactScopeWires spliceInput.coalesceFrameRaw
          site).get index := by
      simpa [sourceContext, sourceIndex, spliceInput] using
        (Splice.Input.PlugLayout.ConcreteElaboration.WireContext.extend_get_local
          sourceOuter site index)
    rw [sourceWire] at quotientEq
    simpa [sourceEnv, sourceIndex,
      ConcreteElaboration.extendedEnvironment, extendWireEnv] using quotientEq
  have targetLocalEq : targetLocal =
      siteTargetLocalOfEmpty layout hzero sourceLocal hiddenEnv := by
    exact focusedLocalEnvironmentOfEmpty_eq_siteTargetLocal hzero quotientValues
      sourceLocal hiddenEnv hostValues
  have environmentEq : sourceEnv = targetEnv ∘ wireMap := by
    change sourceEnv =
      ConcreteElaboration.extendedEnvironment targetOuter
        (layout.frameRegion site) targetOuterEnv targetLocal ∘ wireMap
    rw [targetLocalEq]
    exact siteForwardHostEnvironmentsAgreeOfEmpty layout hzero sourceOuter
      targetOuter outerMap sourceOuterEnv targetOuterEnv outerEq sourceLocal
      hiddenEnv
  let outputBody := ConcreteElaboration.finishRegion layout.plugRaw targetOuter
    (layout.frameRegion site) fullItems
  let outputWitness : Region.ContextPath outputBody [] := .here _
  let outputLeaf := Splice.Region.ContextPath.CompilerLeaf.hereOfItemsComputation
    layout.plugRaw (layout.frameRegion site) targetOuter targetBinders targetFuel
    fullItems fullCompiled targetExact targetCover targetEnumeration
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  have outerValues : ∀ quotient index,
      outputLeaf.inheritedWires.get index = layout.frameWire quotient →
        targetOuterEnv index = quotientValues quotient := by
    intro quotient index indexWire
    have visible : layout.plugRaw.Encloses
        (layout.plugRaw.wires (layout.frameWire quotient)).scope
        (layout.frameRegion site) :=
      (targetExact.mem_iff _).1 (by
        apply List.mem_append_left
        simpa [outputLeaf] using indexWire.symm ▸ List.get_mem targetOuter index)
    have valueEq := Splice.Input.siteQuotientEnvironment_eq spliceInput
      targetContext targetExact preliminaryEnv fallback
      quotient visible
      (Fin.cast
        (ConcreteElaboration.WireContext.length_extend targetOuter
          (layout.frameRegion site)).symm
        (Fin.castAdd
          (ConcreteElaboration.exactScopeWires layout.plugRaw
            (layout.frameRegion site)).length index)) (by
          simpa [targetContext, outputLeaf] using
            (Splice.Input.PlugLayout.ConcreteElaboration.WireContext.extend_get_outer
              targetOuter (layout.frameRegion site) index).trans indexWire)
    have preliminaryValue : preliminaryEnv
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend targetOuter
            (layout.frameRegion site)).symm
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires layout.plugRaw
              (layout.frameRegion site)).length index)) =
        targetOuterEnv index := by
      change extendWireEnv targetOuterEnv preliminaryLocal
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires layout.plugRaw
              (layout.frameRegion site)).length index) = targetOuterEnv index
      exact Fin.addCases_left index
    exact preliminaryValue.symm.trans valueEq.symm
  have rootEnvironmentEq :=
    Splice.Input.focusedExtendedEnvironment_patternRoot_eq spliceInput
      hadmissible outputWitness outputLeaf hzero targetOuterEnv quotientValues
      hiddenEnv outerValues
  exact advance_site_items_denote_forward comprehension attachments binders
    payload state atom tail site arguments hadmissible sourceFuel targetFuel
    sourceContext targetContext sourceBinders targetBinders model named sourceEnv
    targetEnv (RelEnv.pullback relationMap targetRelEnv) targetRelEnv sourceItems
    targetItems sourceCompiled targetCompiled sourceDenotes
    (by
      intro occurrence member notCurrent sourceItem targetItem sourceAt targetAt
        sourceItemDenotes
      cases occurrence with
      | node node =>
          have nodeRegion :=
            (ConcreteElaboration.mem_localOccurrences_node _ _ _).1
              (List.mem_filter.mp member).1
          have simulation := frameNode_simulation_of_mapped spliceInput
            hadmissible site sourceContext targetContext sourceExact targetExact
            sourceBinders targetBinders sourceCover sourceEnumeration wireMap
            wireSpec relationMap relationSpec node nodeRegion model named .forward
            sourceItem targetItem
            (by simpa [ConcreteElaboration.compileOccurrenceWith?] using sourceAt)
            (by simpa [layout, Splice.Input.PlugLayout.mapFrameOccurrence,
              ConcreteElaboration.compileOccurrenceWith?] using targetAt)
          apply simulation sourceEnv targetEnv targetRelEnv
            (by simpa using environmentEq)
          exact (denoteItem_renameRelations model named relationMap
            (RelEnv.pullback relationMap targetRelEnv) targetRelEnv
            (RelEnv.pullback_agrees relationMap targetRelEnv) sourceEnv
            sourceItem).mpr sourceItemDenotes
      | child child =>
          exact advance_site_child_denotes_fixed_forward comprehension
            attachments binders payload state atom tail site arguments node_eq
            hadmissible targets sourceFuel targetFuel site
            (by simpa [node_eq] using
              state.diagram.property.atom_binders_enclose atom)
            sourceContext targetContext sourceExact targetExact sourceBinders
            targetBinders sourceCover targetCover sourceEnumeration
            targetEnumeration wireMap wireSpec relationMap relationSpec model
            named relationValue values parameterValues sourceEnv targetEnv
            targetRelEnv environmentEq targetFixed targetProxies
            (ParameterValuesAt.extend next targetOuter targetOuterEnv
              parameterValues targetParameters (layout.frameRegion site)
              targetLocal)
            childSimulation child member sourceItem targetItem sourceAt targetAt
            sourceItemDenotes)
    (by
      intro occurrence member targetItem targetAt
      have bodyRoot : payload.binderSpine.bodyContainer =
          comprehension.val.diagram.root :=
        payload.binderSpine.body_eq_root_of_empty hzero
      have rootMember : occurrence ∈ ConcreteElaboration.localOccurrences
          comprehension.val.diagram comprehension.val.diagram.root := by
        simpa [bodyRoot] using member
      have patternLength := ConcreteElaboration.compileOccurrencesWith?_length
        (ConcreteElaboration.compileRegion? signature comprehension.val.diagram
          comprehension.val.diagram.regionCount)
        (comprehension.val.exposedWires ++ comprehension.val.hiddenWires)
        ConcreteElaboration.BinderContext.empty pattern.computation
      obtain ⟨occurrenceIndex, occurrenceIndexEq⟩ := indexOf?_complete rootMember
      have occurrenceEq := indexOf?_sound occurrenceIndexEq
      let sourceIndex := Fin.cast patternLength.symm occurrenceIndex
      have sourceAt := ConcreteElaboration.compileOccurrencesWith?_get
        (ConcreteElaboration.compileRegion? signature comprehension.val.diagram
          comprehension.val.diagram.regionCount)
        (comprehension.val.exposedWires ++ comprehension.val.hiddenWires)
        ConcreteElaboration.BinderContext.empty pattern.computation
        occurrenceIndex
      have sourceAt' : ConcreteElaboration.compileOccurrenceWith? signature
          comprehension.val.diagram
          (ConcreteElaboration.compileRegion? signature
            comprehension.val.diagram comprehension.val.diagram.regionCount)
          (comprehension.val.exposedWires ++ comprehension.val.hiddenWires)
          ConcreteElaboration.BinderContext.empty occurrence =
            some (pattern.items.get sourceIndex) := by
        rw [← occurrenceEq]
        simpa [sourceIndex] using sourceAt
      have sourceItemDenotes :=
        (denoteItemSeq_iff_get (relCtx := []) model named
          (extendWireEnv
            (spliceInput.patternAttachmentAssignment.map quotientValues).classes
            hiddenEnv ∘ Fin.cast (by
              simp [spliceInput, instantiateSpliceInput,
                OpenConcreteDiagram.rootWires]))
          PUnit.unit pattern.items).mp nativePatternDenotes sourceIndex
      apply advance_pattern_root_item_denotes_empty_forward comprehension
        attachments binders payload state atom tail site arguments hadmissible
        host outputWitness outputLeaf hzero model named targetEnv targetRelEnv
        occurrence rootMember (pattern.items.get sourceIndex) targetItem
        sourceAt' targetAt
      dsimp only
      let targetEq := ConcreteElaboration.WireContext.length_extend
        outputLeaf.inheritedWires (layout.frameRegion site)
      let castTargetEnv : Fin
          (outputLeaf.inheritedWires.length +
            (ConcreteElaboration.exactScopeWires layout.plugRaw
              (layout.frameRegion site)).length) → model.Carrier :=
        targetEnv ∘ Fin.cast targetEq.symm
      let combined := layout.siteCombinedWireEquivOfEmpty hadmissible host
        outputWitness outputLeaf hzero
      let seamSourceEnv := castTargetEnv ∘ combined
      have seamEq := layout.patternRootSeamWireMapOfEmpty_eq hadmissible host
        outputWitness outputLeaf hzero
      have seamEnvironmentEq :
          seamSourceEnv ∘
              layout.patternRootSeamPreparedWireOfEmpty hadmissible host =
            targetEnv ∘ layout.patternRootWireIndexMap hadmissible hzero
              outputWitness outputLeaf := by
        funext index
        exact congrArg targetEnv (congrFun seamEq index)
      change denoteItem (relCtx := []) model named
        (seamSourceEnv ∘
          layout.patternRootSeamPreparedWireOfEmpty hadmissible host)
        PUnit.unit (pattern.items.get sourceIndex)
      rw [seamEnvironmentEq]
      have rootEnvironmentEq' :
          targetEnv ∘ layout.patternRootWireIndexMap hadmissible hzero
              outputWitness outputLeaf =
            extendWireEnv
                (spliceInput.patternAttachmentAssignment.map
                  quotientValues).classes hiddenEnv ∘
              Fin.cast (by
                exact List.length_append) := by
        simpa [targetEnv, targetLocal, outputLeaf, layout, spliceInput] using
          rootEnvironmentEq
      rw [rootEnvironmentEq']
      exact sourceItemDenotes)

end InstantiationSemantic

end VisualProof.Rule
