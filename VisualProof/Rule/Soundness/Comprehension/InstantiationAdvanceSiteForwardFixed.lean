import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvanceSiteForward

namespace VisualProof.Rule

open VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- Zero-spine forward site transport.  The current source atom exposes the
authoritative open-pattern witness; its hidden-root valuation is installed in
the executor's exact material-local block. -/
theorem advance_site_items_denote_empty_fixed_forward
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    (comprehension : Concrete.CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Concrete.Checked }
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
    (sourceOuter : Concrete.Elaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw)
    (targetOuter : Concrete.Elaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw)
    (sourceExact : (sourceOuter.extend site).Exact site)
    (targetExact : (targetOuter.extend
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site)).Exact
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site))
    (sourceBinders : Concrete.Elaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw targetRels)
    (sourceCover : sourceBinders.Covers site)
    (targetCover : targetBinders.Covers
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site))
    (sourceEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceBinders site)
    (targetEnumeration : Concrete.Elaboration.BinderContext.Enumeration
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
    (model : Model)
    (relationValue : Relation model.Carrier payload.arity)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (parameterValues : Fin attachments.length → model.Carrier)
    (sourceOuterEnv : Fin sourceOuter.length → model.Carrier)
    (targetOuterEnv : Fin targetOuter.length → model.Carrier)
    (targetRelEnv : RelEnv model.Carrier targetRels)
    (outerAgrees :
      (Concrete.Elaboration.ContextIndexRelation.forwardMap outerMap)
        |>.EnvironmentsAgree sourceOuterEnv targetOuterEnv)
    (sourceLocal : Fin (Concrete.Elaboration.exactScopeWires
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw site).length → model.Carrier)
    (sourceItems : ItemSeq  (sourceOuter.extend site).length sourceRels)
    (targetItems : ItemSeq  (targetOuter.extend
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site)).length targetRels)
    (fullItems : ItemSeq  (targetOuter.extend
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site)).length targetRels)
    (sourceCompiled : Concrete.Elaboration.compileOccurrencesWith?
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw
      (compileSurvivorRegion?
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible) sourceFuel)
      (sourceOuter.extend site) sourceBinders
      ((Concrete.Elaboration.localOccurrences
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible).diagram.val site).filter
        (dropOccurrenceSurvives
          (coalescedInstantiationState comprehension attachments binders payload
            state site arguments hadmissible))) = some sourceItems)
    (targetCompiled : Concrete.Elaboration.compileOccurrencesWith?
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val
      (compileSurvivorRegion?
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible) targetFuel)
      (targetOuter.extend
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion site)) targetBinders
      ((Concrete.Elaboration.localOccurrences
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible).diagram.val
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion site)).filter
        (dropOccurrenceSurvives
          (advanceInstantiationState comprehension attachments binders payload
            state atom tail site arguments hadmissible))) = some targetItems)
    (fullCompiled : Concrete.Elaboration.compileOccurrencesWith?
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw
      (Concrete.Elaboration.compileRegion?
        (instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.plugRaw targetFuel)
      (targetOuter.extend
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion site)) targetBinders
      (Concrete.Elaboration.localOccurrences
        (instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.plugRaw
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion site)) = some fullItems)
    (sourceDenotes : denoteItemSeq model
      (Concrete.Elaboration.extendedEnvironment sourceOuter site sourceOuterEnv
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
      payload.interpretedRelation model  parameterValues)
    (childSimulation : ∀ direction
      (child : Fin state.diagram.val.regionCount),
      state.diagram.val.Encloses state.bubble child →
      FixedAdvanceRegionSimulation comprehension attachments binders payload
        state atom tail site arguments hadmissible model  relationValue
        values parameterValues direction sourceFuel targetFuel child) :
    ∃ targetLocal : Fin (Concrete.Elaboration.exactScopeWires
        (instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.plugRaw
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion site)).length → model.Carrier,
      denoteItemSeq model
        (Concrete.Elaboration.extendedEnvironment targetOuter
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
  let sourceEnv := Concrete.Elaboration.extendedEnvironment sourceOuter site
    sourceOuterEnv sourceLocal
  let fallback : model.Carrier := Classical.choice model.nonempty
  have outerEq : sourceOuterEnv = targetOuterEnv ∘ outerMap := by
    simpa using outerAgrees
  let dummyHidden : Fin comprehension.val.hiddenWires.length → model.Carrier :=
    fun _ => fallback
  let preliminaryLocal := siteTargetLocalOfEmpty layout hzero sourceLocal
    dummyHidden
  let preliminaryEnv := Concrete.Elaboration.extendedEnvironment targetOuter
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
  let quotientValues := Concrete.Splice.Input.siteQuotientEnvironment spliceInput
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
    node_eq arguments_eq pending_eq ownedNodup hadmissible model
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
  have patternDenotes : comprehension.denote model
      (Fin.addCases
        (fun index => quotientValues
          (spliceInput.quotientWire (arguments index)))
        parameterValues ∘ Fin.cast payload.boundarySplit) := by
    apply (payload.interpretedRelation_apply model  parameterValues _).mp
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
  have patternAtQuotient : comprehension.denote model
      (fun position => quotientValues
        (spliceInput.quotientWire (spliceInput.attachment position))) := by
    exact Eq.mp
      (congrArg (fun arguments => comprehension.denote model  arguments)
        attachmentValues.symm) patternDenotes
  let pattern := Concrete.Splice.Input.compiledSpliceOpenRootItems comprehension
  obtain ⟨hiddenEnv, nativePatternDenotes⟩ :=
    Concrete.Splice.Input.patternRootItems_of_pattern_denote spliceInput model
      quotientValues patternAtQuotient
  let targetLocal := Concrete.Splice.Input.focusedLocalEnvironmentOfEmpty spliceInput
    hzero quotientValues hiddenEnv
  refine ⟨targetLocal, ?_⟩
  let targetEnv := Concrete.Elaboration.extendedEnvironment targetOuter
    (layout.frameRegion site) targetOuterEnv targetLocal
  have hostValues : ∀ index, quotientValues
      ((Concrete.Elaboration.exactScopeWires spliceInput.coalesceFrameRaw
        site).get index) = sourceLocal index := by
    intro index
    let sourceIndex : Fin sourceContext.length := Fin.cast
      (Concrete.Elaboration.WireContext.length_extend sourceOuter site).symm
      (Fin.natAdd sourceOuter.length index)
    have quotientEq := quotientAtSource sourceIndex
    have sourceWire : sourceContext.get sourceIndex =
        (Concrete.Elaboration.exactScopeWires spliceInput.coalesceFrameRaw
          site).get index := by
      simpa [sourceContext, sourceIndex, spliceInput] using
        (Concrete.Splice.Input.PlugLayout.Elaboration.WireContext.extend_get_local
          sourceOuter site index)
    rw [sourceWire] at quotientEq
    simpa [sourceEnv, sourceIndex,
      Concrete.Elaboration.extendedEnvironment, extendWireEnv] using quotientEq
  have targetLocalEq : targetLocal =
      siteTargetLocalOfEmpty layout hzero sourceLocal hiddenEnv := by
    exact focusedLocalEnvironmentOfEmpty_eq_siteTargetLocal hzero quotientValues
      sourceLocal hiddenEnv hostValues
  have environmentEq : sourceEnv = targetEnv ∘ wireMap := by
    change sourceEnv =
      Concrete.Elaboration.extendedEnvironment targetOuter
        (layout.frameRegion site) targetOuterEnv targetLocal ∘ wireMap
    rw [targetLocalEq]
    exact siteForwardHostEnvironmentsAgreeOfEmpty layout hzero sourceOuter
      targetOuter outerMap sourceOuterEnv targetOuterEnv outerEq sourceLocal
      hiddenEnv
  let outputBody := Concrete.Elaboration.finishRegion layout.plugRaw targetOuter
    (layout.frameRegion site) fullItems
  let outputWitness : Region.ContextPath outputBody [] := .here _
  let outputLeaf := Concrete.Splice.Region.ContextPath.CompilerLeaf.hereOfItemsComputation
    layout.plugRaw (layout.frameRegion site) targetOuter targetBinders targetFuel
    fullItems fullCompiled targetExact targetCover targetEnumeration
  let host := Concrete.Splice.Input.compiledSpliceHostView spliceInput hadmissible
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
    have valueEq := Concrete.Splice.Input.siteQuotientEnvironment_eq spliceInput
      targetContext targetExact preliminaryEnv fallback
      quotient visible
      (Fin.cast
        (Concrete.Elaboration.WireContext.length_extend targetOuter
          (layout.frameRegion site)).symm
        (Fin.castAdd
          (Concrete.Elaboration.exactScopeWires layout.plugRaw
            (layout.frameRegion site)).length index)) (by
          simpa [targetContext, outputLeaf] using
            (Concrete.Splice.Input.PlugLayout.Elaboration.WireContext.extend_get_outer
              targetOuter (layout.frameRegion site) index).trans indexWire)
    have preliminaryValue : preliminaryEnv
        (Fin.cast
          (Concrete.Elaboration.WireContext.length_extend targetOuter
            (layout.frameRegion site)).symm
          (Fin.castAdd
            (Concrete.Elaboration.exactScopeWires layout.plugRaw
              (layout.frameRegion site)).length index)) =
        targetOuterEnv index := by
      change extendWireEnv targetOuterEnv preliminaryLocal
          (Fin.castAdd
            (Concrete.Elaboration.exactScopeWires layout.plugRaw
              (layout.frameRegion site)).length index) = targetOuterEnv index
      exact Fin.addCases_left index
    exact preliminaryValue.symm.trans valueEq.symm
  have rootEnvironmentEq :=
    Concrete.Splice.Input.focusedExtendedEnvironment_patternRoot_eq spliceInput
      hadmissible outputWitness outputLeaf hzero targetOuterEnv quotientValues
      hiddenEnv outerValues
  exact advance_site_items_denote_forward comprehension attachments binders
    payload state atom tail site arguments hadmissible sourceFuel targetFuel
    sourceContext targetContext sourceBinders targetBinders model  sourceEnv
    targetEnv (RelEnv.pullback relationMap targetRelEnv) targetRelEnv sourceItems
    targetItems sourceCompiled targetCompiled sourceDenotes
    (by
      intro occurrence member notCurrent sourceItem targetItem sourceAt targetAt
        sourceItemDenotes
      cases occurrence with
      | node node =>
          have nodeRegion :=
            (Concrete.Elaboration.mem_localOccurrences_node _ _ _).1
              (List.mem_filter.mp member).1
          have simulation := frameNode_simulation_of_mapped spliceInput
            hadmissible site sourceContext targetContext sourceExact targetExact
            sourceBinders targetBinders sourceCover sourceEnumeration wireMap
            wireSpec relationMap relationSpec node nodeRegion model  .forward
            sourceItem targetItem
            (by simpa [Concrete.Elaboration.compileOccurrenceWith?] using sourceAt)
            (by simpa [layout, Concrete.Splice.Input.PlugLayout.mapFrameOccurrence,
              Concrete.Elaboration.compileOccurrenceWith?] using targetAt)
          apply simulation sourceEnv targetEnv targetRelEnv
            (by simpa using environmentEq)
          exact (denoteItem_renameRelations model  relationMap
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
             relationValue values parameterValues sourceEnv targetEnv
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
      have rootMember : occurrence ∈ Concrete.Elaboration.localOccurrences
          comprehension.val.diagram comprehension.val.diagram.root := by
        simpa [bodyRoot] using member
      have patternLength := Concrete.Elaboration.compileOccurrencesWith?_length
        (Concrete.Elaboration.compileRegion?  comprehension.val.diagram
          comprehension.val.diagram.regionCount)
        (comprehension.val.exposedWires ++ comprehension.val.hiddenWires)
        Concrete.Elaboration.BinderContext.empty pattern.computation
      obtain ⟨occurrenceIndex, occurrenceIndexEq⟩ := indexOf?_complete rootMember
      have occurrenceEq := indexOf?_sound occurrenceIndexEq
      let sourceIndex := Fin.cast patternLength.symm occurrenceIndex
      have sourceAt := Concrete.Elaboration.compileOccurrencesWith?_get
        (Concrete.Elaboration.compileRegion?  comprehension.val.diagram
          comprehension.val.diagram.regionCount)
        (comprehension.val.exposedWires ++ comprehension.val.hiddenWires)
        Concrete.Elaboration.BinderContext.empty pattern.computation
        occurrenceIndex
      have sourceAt' : Concrete.Elaboration.compileOccurrenceWith?
          comprehension.val.diagram
          (Concrete.Elaboration.compileRegion?
            comprehension.val.diagram comprehension.val.diagram.regionCount)
          (comprehension.val.exposedWires ++ comprehension.val.hiddenWires)
          Concrete.Elaboration.BinderContext.empty occurrence =
            some (pattern.items.get sourceIndex) := by
        rw [← occurrenceEq]
        simpa [sourceIndex] using sourceAt
      have sourceItemDenotes :=
        (denoteItemSeq_iff_get (relCtx := []) model
          (extendWireEnv
            (spliceInput.patternAttachmentAssignment.map quotientValues).classes
            hiddenEnv ∘ Fin.cast (by
              simp [spliceInput, instantiateSpliceInput,
                Concrete.OpenDiagram.rootWires]))
          PUnit.unit pattern.items).mp nativePatternDenotes sourceIndex
      apply advance_pattern_root_item_denotes_empty_forward comprehension
        attachments binders payload state atom tail site arguments hadmissible
        host outputWitness outputLeaf hzero model  targetEnv targetRelEnv
        occurrence rootMember (pattern.items.get sourceIndex) targetItem
        sourceAt' targetAt
      dsimp only
      let targetEq := Concrete.Elaboration.WireContext.length_extend
        outputLeaf.inheritedWires (layout.frameRegion site)
      let castTargetEnv : Fin
          (outputLeaf.inheritedWires.length +
            (Concrete.Elaboration.exactScopeWires layout.plugRaw
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
      change denoteItem (relCtx := []) model
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

/-- Nonzero-spine forward site transport.  The current source atom exposes
the canonical terminal relation witness; its terminal locals and proxy
environment are installed through the authoritative executor seam. -/
theorem advance_site_items_denote_nonempty_fixed_forward
    {input : Concrete.Checked }
    {bubble : Fin input.val.regionCount}
    (comprehension : Concrete.CheckedOpen )
    (attachments : List (Fin input.val.wireCount))
    (binders : List
      (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount))
    (payload : OperationComprehensionInstantiatePayload input bubble comprehension
      attachments binders)
    {origin : Concrete.Checked }
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
    (hnonempty : payload.binderSpine.proxyCount ≠ 0)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (sourceFuel targetFuel : Nat)
    (sourceOuter : Concrete.Elaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw)
    (targetOuter : Concrete.Elaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw)
    (sourceExact : (sourceOuter.extend site).Exact site)
    (targetExact : (targetOuter.extend
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site)).Exact
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site))
    (sourceBinders : Concrete.Elaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw targetRels)
    (sourceCover : sourceBinders.Covers site)
    (targetCover : targetBinders.Covers
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site))
    (sourceEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceBinders site)
    (targetEnumeration : Concrete.Elaboration.BinderContext.Enumeration
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
    (model : Model)
    (relationValue : Relation model.Carrier payload.arity)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    (parameterValues : Fin attachments.length → model.Carrier)
    (sourceOuterEnv : Fin sourceOuter.length → model.Carrier)
    (targetOuterEnv : Fin targetOuter.length → model.Carrier)
    (targetRelEnv : RelEnv model.Carrier targetRels)
    (outerAgrees :
      (Concrete.Elaboration.ContextIndexRelation.forwardMap outerMap)
        |>.EnvironmentsAgree sourceOuterEnv targetOuterEnv)
    (sourceLocal : Fin (Concrete.Elaboration.exactScopeWires
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw site).length → model.Carrier)
    (sourceItems : ItemSeq  (sourceOuter.extend site).length sourceRels)
    (targetItems : ItemSeq  (targetOuter.extend
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site)).length targetRels)
    (fullItems : ItemSeq  (targetOuter.extend
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site)).length targetRels)
    (sourceCompiled : Concrete.Elaboration.compileOccurrencesWith?
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw
      (compileSurvivorRegion?
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible) sourceFuel)
      (sourceOuter.extend site) sourceBinders
      ((Concrete.Elaboration.localOccurrences
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible).diagram.val site).filter
        (dropOccurrenceSurvives
          (coalescedInstantiationState comprehension attachments binders payload
            state site arguments hadmissible))) = some sourceItems)
    (targetCompiled : Concrete.Elaboration.compileOccurrencesWith?
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val
      (compileSurvivorRegion?
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible) targetFuel)
      (targetOuter.extend
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion site)) targetBinders
      ((Concrete.Elaboration.localOccurrences
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible).diagram.val
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion site)).filter
        (dropOccurrenceSurvives
          (advanceInstantiationState comprehension attachments binders payload
            state atom tail site arguments hadmissible))) = some targetItems)
    (fullCompiled : Concrete.Elaboration.compileOccurrencesWith?
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw
      (Concrete.Elaboration.compileRegion?
        (instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.plugRaw targetFuel)
      (targetOuter.extend
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion site)) targetBinders
      (Concrete.Elaboration.localOccurrences
        (instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.plugRaw
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion site)) = some fullItems)
    (sourceDenotes : denoteItemSeq model
      (Concrete.Elaboration.extendedEnvironment sourceOuter site sourceOuterEnv
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
    (relationEq : relationValue = terminalRelationOfParameterValues payload
      state site arguments hnonempty model  parameterValues values)
    (childSimulation : ∀ direction
      (child : Fin state.diagram.val.regionCount),
      state.diagram.val.Encloses state.bubble child →
      FixedAdvanceRegionSimulation comprehension attachments binders payload
        state atom tail site arguments hadmissible model  relationValue
        values parameterValues direction sourceFuel targetFuel child) :
    ∃ targetLocal : Fin (Concrete.Elaboration.exactScopeWires
        (instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.plugRaw
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion site)).length → model.Carrier,
      denoteItemSeq model
        (Concrete.Elaboration.extendedEnvironment targetOuter
          ((instantiateSpliceInput comprehension attachments binders payload
            state site arguments).plugLayout.frameRegion site) targetOuterEnv
          targetLocal)
        targetRelEnv targetItems := by
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let next := advanceInstantiationState comprehension attachments binders
    payload state atom tail site arguments hadmissible
  let sourceContext := sourceOuter.extend site
  let targetContext := targetOuter.extend (layout.frameRegion site)
  let sourceEnv := Concrete.Elaboration.extendedEnvironment sourceOuter site
    sourceOuterEnv sourceLocal
  let fallback : model.Carrier := Classical.choice model.nonempty
  have outerEq : sourceOuterEnv = targetOuterEnv ∘ outerMap := by
    simpa using outerAgrees
  let dummyPattern : Fin (Concrete.Elaboration.exactScopeWires
      comprehension.val.diagram payload.binderSpine.bodyContainer).length →
      model.Carrier := fun _ => fallback
  let preliminaryLocal := siteTargetLocalOfNonempty layout hnonempty sourceLocal
    dummyPattern
  let preliminaryEnv := Concrete.Elaboration.extendedEnvironment targetOuter
    (layout.frameRegion site) targetOuterEnv preliminaryLocal
  let wireMap := siteForwardHostWireMapOfNonempty layout hnonempty sourceOuter
    targetOuter outerMap
  have wireSpec : ∀ index, targetContext.get (wireMap index) =
      layout.frameWire (sourceContext.get index) :=
    siteForwardHostWireMapOfNonempty_spec layout hnonempty sourceOuter
      targetOuter outerMap outerSpec
  have preliminaryEnvironmentEq : sourceEnv = preliminaryEnv ∘ wireMap :=
    siteForwardHostEnvironmentsAgreeOfNonempty layout hnonempty sourceOuter
      targetOuter outerMap sourceOuterEnv targetOuterEnv outerEq sourceLocal
      dummyPattern
  let quotientValues := Concrete.Splice.Input.siteQuotientEnvironment spliceInput
    targetContext targetExact preliminaryEnv fallback
  have quotientAtSource : ∀ index,
      quotientValues (sourceContext.get index) = sourceEnv index :=
    siteQuotientEnvironment_of_frameMap spliceInput sourceContext targetContext
      sourceExact targetExact wireMap wireSpec sourceEnv preliminaryEnv
      preliminaryEnvironmentEq fallback
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
    node_eq arguments_eq pending_eq ownedNodup hadmissible model
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
      targetExact preliminaryEnv parameterValues preliminaryParameters fallback
      position
  have terminalTruth : terminalRelationOfParameterValues payload state site
      arguments hnonempty model  parameterValues values
      (fun index => quotientValues
        (spliceInput.quotientWire (arguments index))) := by
    rw [← relationEq]
    exact relationTruth
  change ∃ assignment : BoundaryAssignment comprehension.elaborate model.Carrier,
      assignment.args =
          Fin.addCases
            (fun index => quotientValues
              (spliceInput.quotientWire (arguments index))) parameterValues ∘
            Fin.cast payload.boundarySplit ∧
        ∃ relEnv : RelEnv model.Carrier
            (Concrete.Splice.Input.compiledSpliceTerminalView spliceInput
              hnonempty).witness.toFocus.holeRels,
          TerminalRelationsMatch payload state site arguments hnonempty values
              relEnv ∧
            denoteRegion model
              (terminalInheritedEnvironment payload state site arguments
                hnonempty assignment)
              relEnv
              (Concrete.Elaboration.finishRegion comprehension.val.diagram
                (Concrete.Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
                  ).leaf.inheritedWires payload.binderSpine.bodyContainer
                (Concrete.Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
                  ).leaf.items) at terminalTruth
  obtain ⟨assignment, assignmentArgs, terminalRelEnv, terminalRelations,
    terminalDenotes⟩ := terminalTruth
  let pattern := Concrete.Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
  change ∃ patternLocal : Fin (Concrete.Elaboration.exactScopeWires
      comprehension.val.diagram payload.binderSpine.bodyContainer).length →
      model.Carrier,
    denoteItemSeq model
      (extendWireEnv
        (terminalInheritedEnvironment payload state site arguments hnonempty
          assignment) patternLocal)
      terminalRelEnv
      (pattern.leaf.items.castWiresEq
        (Concrete.Elaboration.WireContext.length_extend
          pattern.leaf.inheritedWires payload.binderSpine.bodyContainer))
    at terminalDenotes
  obtain ⟨patternLocal, terminalItemsDenoteCast⟩ := terminalDenotes
  have terminalItemsDenote : denoteItemSeq model
      (Concrete.Elaboration.extendedEnvironment pattern.leaf.inheritedWires
        payload.binderSpine.bodyContainer
        (terminalInheritedEnvironment payload state site arguments hnonempty
          assignment) patternLocal)
      terminalRelEnv pattern.leaf.items := by
    rw [ItemSeq.castWiresEq_eq_renameWires, denoteItemSeq_renameWires]
      at terminalItemsDenoteCast
    simpa [Concrete.Elaboration.extendedEnvironment] using
      terminalItemsDenoteCast
  let targetLocal := siteTargetLocalOfNonempty layout hnonempty sourceLocal
    patternLocal
  refine ⟨targetLocal, ?_⟩
  let targetEnv := Concrete.Elaboration.extendedEnvironment targetOuter
    (layout.frameRegion site) targetOuterEnv targetLocal
  have environmentEq : sourceEnv = targetEnv ∘ wireMap := by
    exact siteForwardHostEnvironmentsAgreeOfNonempty layout hnonempty
      sourceOuter targetOuter outerMap sourceOuterEnv targetOuterEnv outerEq
      sourceLocal patternLocal
  let outputBody := Concrete.Elaboration.finishRegion layout.plugRaw targetOuter
    (layout.frameRegion site) fullItems
  let outputWitness : Region.ContextPath outputBody [] := .here _
  let outputLeaf := Concrete.Splice.Region.ContextPath.CompilerLeaf.hereOfItemsComputation
    layout.plugRaw (layout.frameRegion site) targetOuter targetBinders targetFuel
    fullItems fullCompiled targetExact targetCover targetEnumeration
  let host := Concrete.Splice.Input.compiledSpliceHostView spliceInput hadmissible
  let finalQuotientValues := Concrete.Splice.Input.siteQuotientEnvironment spliceInput
    targetContext targetExact targetEnv fallback
  let preliminaryAssignment :=
    spliceInput.patternAttachmentAssignment.map quotientValues
  let finalAssignment :=
    spliceInput.patternAttachmentAssignment.map finalQuotientValues
  have preliminaryAssignmentArgs : assignment.args =
      preliminaryAssignment.args := by
    rw [assignmentArgs]
    funext position
    let split := Fin.cast payload.boundarySplit position
    have recover : Fin.cast payload.boundarySplit.symm split = position := by
      apply Fin.ext
      rfl
    rw [← recover]
    refine Fin.addCases (fun argument => ?_) (fun parameter => ?_) split
    · simp [preliminaryAssignment, Concrete.Splice.Input.patternAttachmentAssignment,
        BoundaryAssignment.map, spliceInput, instantiateSpliceInput]
    · simpa [preliminaryAssignment,
        Concrete.Splice.Input.patternAttachmentAssignment, BoundaryAssignment.map,
        spliceInput, instantiateSpliceInput] using
        (congrFun quotientParameters parameter).symm
  have quotientAssignmentsAgree : preliminaryAssignment.args =
      finalAssignment.args := by
    funext position
    have sourceVisible := spliceInput.quotientAttachment_visible hadmissible
      position
    obtain ⟨sourceIndex, sourceIndexLookup⟩ :=
      Concrete.Elaboration.WireContext.lookup?_complete
        ((sourceExact.mem_iff _).2 sourceVisible)
    have sourceIndexWire :=
      Concrete.Elaboration.WireContext.lookup?_sound sourceIndexLookup
    have preliminaryEq := quotientAtSource sourceIndex
    have finalEq := siteQuotientEnvironment_of_frameMap spliceInput
      sourceContext targetContext sourceExact targetExact wireMap wireSpec
      sourceEnv targetEnv environmentEq fallback sourceIndex
    change quotientValues
        (spliceInput.quotientWire (spliceInput.attachment position)) =
      finalQuotientValues
        (spliceInput.quotientWire (spliceInput.attachment position))
    rw [← sourceIndexWire]
    exact preliminaryEq.trans finalEq.symm
  have assignmentClasses : assignment.classes = finalAssignment.classes :=
    BoundaryAssignment.classes_eq_of_args_eq assignment finalAssignment
      (preliminaryAssignmentArgs.trans quotientAssignmentsAgree)
  let hostRelations : RelationRenaming host.intrinsicPath.toFocus.holeRels
      targetRels := fun relation =>
    layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
      outputWitness outputLeaf relation
  have hostProxies : ProxyRelationsAt payload state host.compilerLeaf.binders
      (RelEnv.pullback hostRelations targetRelEnv) values :=
    proxyRelationsAt_host_pullback comprehension attachments binders payload
      state atom tail site arguments hadmissible host.intrinsicPath
      host.compilerLeaf outputWitness outputLeaf model values targetRelEnv
      targetProxies
  let terminalRelationMap : RelationRenaming
      pattern.witness.toFocus.holeRels targetRels := fun relation =>
    hostRelations (layout.coalescedTerminalRelationRenaming hadmissible
      host.intrinsicPath host.compilerLeaf pattern.witness pattern.leaf
      hnonempty relation)
  have targetTerminalRelations : TerminalRelationsMatch payload state site
      arguments hnonempty values
      (RelEnv.pullback terminalRelationMap targetRelEnv) := by
    exact terminalOutputRelations_match payload state site arguments hnonempty
      hadmissible values outputWitness outputLeaf targetRelEnv hostProxies
  have terminalRelEnvEq : terminalRelEnv =
      RelEnv.pullback terminalRelationMap targetRelEnv :=
    terminalRelationsMatch_unique payload state site arguments hnonempty values
      terminalRelEnv (RelEnv.pullback terminalRelationMap targetRelEnv)
      terminalRelations targetTerminalRelations
  have canonicalSeamEq := patternTerminalExtendedEnvironment_seam spliceInput
    hadmissible host pattern.witness pattern.leaf outputWitness outputLeaf
    hnonempty targetEnv fallback
  let canonicalInherited : Fin pattern.leaf.inheritedWires.length →
      model.Carrier := fun index =>
    finalAssignment.classes (Concrete.Splice.Input.PlugLayout.exposedWireIndex spliceInput
      (pattern.leaf.inheritedWires.get index)
      ((layout.terminalBody_inherited_mem_iff_exposed pattern.witness
        pattern.leaf hnonempty (pattern.leaf.inheritedWires.get index)).1
          (List.get_mem _ index)))
  let canonicalLocal : Fin (Concrete.Elaboration.exactScopeWires
      comprehension.val.diagram payload.binderSpine.bodyContainer).length →
      model.Carrier := fun index =>
    targetEnv (layout.patternSeamWireMapOfNonempty hadmissible host
      pattern.witness pattern.leaf outputWitness outputLeaf hnonempty
      (Fin.cast
        (Concrete.Elaboration.WireContext.length_extend
          pattern.leaf.inheritedWires payload.binderSpine.bodyContainer).symm
        (Fin.natAdd pattern.leaf.inheritedWires.length index)))
  have canonicalLocalEq : canonicalLocal = patternLocal := by
    funext index
    exact siteTargetEnvironment_patternLocalOfNonempty layout hadmissible host
      pattern.witness pattern.leaf outputWitness outputLeaf hnonempty
      targetOuterEnv sourceLocal patternLocal index
  have inheritedEq :
      terminalInheritedEnvironment payload state site arguments hnonempty
          assignment = canonicalInherited := by
    funext index
    simp only [terminalInheritedEnvironment, canonicalInherited,
      finalAssignment]
    exact congrFun assignmentClasses _
  have terminalEnvironmentEq :
      Concrete.Elaboration.extendedEnvironment pattern.leaf.inheritedWires
          payload.binderSpine.bodyContainer
          (terminalInheritedEnvironment payload state site arguments hnonempty
            assignment) patternLocal =
        targetEnv ∘ layout.patternSeamWireMapOfNonempty hadmissible host
          pattern.witness pattern.leaf outputWitness outputLeaf hnonempty := by
    rw [inheritedEq, ← canonicalLocalEq]
    simpa [canonicalInherited, canonicalLocal, finalAssignment,
      finalQuotientValues, targetContext] using canonicalSeamEq
  have terminalItemsTarget : denoteItemSeq model
      (targetEnv ∘ layout.patternSeamWireMapOfNonempty hadmissible host
        pattern.witness pattern.leaf outputWitness outputLeaf hnonempty)
      (RelEnv.pullback terminalRelationMap targetRelEnv) pattern.leaf.items := by
    rw [← terminalEnvironmentEq, ← terminalRelEnvEq]
    exact terminalItemsDenote
  exact advance_site_items_denote_forward comprehension attachments binders
    payload state atom tail site arguments hadmissible sourceFuel targetFuel
    sourceContext targetContext sourceBinders targetBinders model  sourceEnv
    targetEnv (RelEnv.pullback relationMap targetRelEnv) targetRelEnv sourceItems
    targetItems sourceCompiled targetCompiled sourceDenotes
    (by
      intro occurrence member notCurrent sourceItem targetItem sourceAt targetAt
        sourceItemDenotes
      cases occurrence with
      | node node =>
          have nodeRegion :=
            (Concrete.Elaboration.mem_localOccurrences_node _ _ _).1
              (List.mem_filter.mp member).1
          have simulation := frameNode_simulation_of_mapped spliceInput
            hadmissible site sourceContext targetContext sourceExact targetExact
            sourceBinders targetBinders sourceCover sourceEnumeration wireMap
            wireSpec relationMap relationSpec node nodeRegion model  .forward
            sourceItem targetItem
            (by simpa [Concrete.Elaboration.compileOccurrenceWith?] using sourceAt)
            (by simpa [layout, Concrete.Splice.Input.PlugLayout.mapFrameOccurrence,
              Concrete.Elaboration.compileOccurrenceWith?] using targetAt)
          apply simulation sourceEnv targetEnv targetRelEnv
            (by simpa using environmentEq)
          exact (denoteItem_renameRelations model  relationMap
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
             relationValue values parameterValues sourceEnv targetEnv
            targetRelEnv environmentEq targetFixed targetProxies
            (ParameterValuesAt.extend next targetOuter targetOuterEnv
              parameterValues targetParameters (layout.frameRegion site)
              targetLocal)
            childSimulation child member sourceItem targetItem sourceAt targetAt
            sourceItemDenotes)
    (by
      intro occurrence member targetItem targetAt
      obtain ⟨occurrenceIndex, occurrenceIndexEq⟩ := indexOf?_complete member
      have occurrenceEq := indexOf?_sound occurrenceIndexEq
      have patternLength := Concrete.Elaboration.compileOccurrencesWith?_length
        (Concrete.Elaboration.compileRegion?  comprehension.val.diagram
          pattern.leaf.fuel)
        (pattern.leaf.inheritedWires.extend payload.binderSpine.bodyContainer)
        pattern.leaf.binders pattern.leaf.itemsComputation
      let sourceIndex := Fin.cast patternLength.symm occurrenceIndex
      have sourceAt := Concrete.Elaboration.compileOccurrencesWith?_get
        (Concrete.Elaboration.compileRegion?  comprehension.val.diagram
          pattern.leaf.fuel)
        (pattern.leaf.inheritedWires.extend payload.binderSpine.bodyContainer)
        pattern.leaf.binders pattern.leaf.itemsComputation occurrenceIndex
      have sourceAt' : Concrete.Elaboration.compileOccurrenceWith?
          comprehension.val.diagram
          (Concrete.Elaboration.compileRegion?
            comprehension.val.diagram pattern.leaf.fuel)
          (pattern.leaf.inheritedWires.extend payload.binderSpine.bodyContainer)
          pattern.leaf.binders occurrence =
            some (pattern.leaf.items.get sourceIndex) := by
        rw [← occurrenceEq]
        simpa [sourceIndex] using sourceAt
      have sourceItemDenotes :=
        (denoteItemSeq_iff_get model
          (targetEnv ∘ layout.patternSeamWireMapOfNonempty hadmissible host
            pattern.witness pattern.leaf outputWitness outputLeaf hnonempty)
          (RelEnv.pullback terminalRelationMap targetRelEnv)
          pattern.leaf.items).mp terminalItemsTarget sourceIndex
      apply advance_pattern_item_denotes_nonempty_forward comprehension
        attachments binders payload state atom tail site arguments hadmissible
        host pattern.witness pattern.leaf outputWitness outputLeaf hnonempty
        model  targetEnv targetRelEnv occurrence member
        (pattern.leaf.items.get sourceIndex) targetItem sourceAt' targetAt
      simpa [Concrete.Splice.Input.PlugLayout.patternSeamWireMapOfNonempty,
        terminalRelationMap, hostRelations, Function.comp_def] using
        sourceItemDenotes)

end InstantiationSemantic

end VisualProof.Rule
