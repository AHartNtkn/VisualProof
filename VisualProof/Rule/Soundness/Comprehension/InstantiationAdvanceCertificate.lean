import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvancePatternEmpty

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- Reconstruct the native terminal region from already-extracted terminal
items.  This separates semantic seam recovery from the stronger (and here
unavailable) premise that every retained host item also denotes. -/
theorem patternTerminalRegion_denotes_of_native_items
    {signature : List Nat}
    (input : Splice.Input signature)
    (hadmissible : input.Admissible)
    (host : Splice.SiteView (input.coalesceFrame hadmissible) input.site)
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Splice.Region.ContextPath.CompilerLeaf
      input.pattern.val.diagram input.binderSpine.bodyContainer patternWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Splice.Region.ContextPath.CompilerLeaf input.plugLayout.plugRaw
      (input.plugLayout.frameRegion input.site) outputWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin (outputLeaf.inheritedWires.extend
      (input.plugLayout.frameRegion input.site)).length → model.Carrier)
    (relEnv : RelEnv model.Carrier outputWitness.toFocus.holeRels)
    (fallback : model.Carrier)
    (nativeItems :
      let targetEq := ConcreteElaboration.WireContext.length_extend
        outputLeaf.inheritedWires (input.plugLayout.frameRegion input.site)
      let combined := input.plugLayout.siteCombinedWireEquivOfNonempty
        hadmissible host outputWitness outputLeaf hnonempty
      let targetEnv : Fin
          (outputLeaf.inheritedWires.length +
            (ConcreteElaboration.exactScopeWires input.plugLayout.plugRaw
              (input.plugLayout.frameRegion input.site)).length) →
          model.Carrier := env ∘ Fin.cast targetEq.symm
      let sourceEnv := targetEnv ∘ combined
      let terminalRelations : RelationRenaming
          patternWitness.toFocus.holeRels outputWitness.toFocus.holeRels :=
        fun relation =>
          input.plugLayout.hostRelationRenaming host.intrinsicPath
            host.compilerLeaf outputWitness outputLeaf
            (input.plugLayout.coalescedTerminalRelationRenaming hadmissible
              host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
              hnonempty relation)
      denoteItemSeq model named
        (sourceEnv ∘ input.plugLayout.patternSeamPreparedWireOfNonempty
          hadmissible host patternWitness patternLeaf hnonempty)
        (RelEnv.pullback terminalRelations relEnv) patternLeaf.items) :
    let context := outputLeaf.inheritedWires.extend
      (input.plugLayout.frameRegion input.site)
    let values := Splice.Input.siteQuotientEnvironment input context
      outputLeaf.wiresExact env fallback
    let assignment := input.patternAttachmentAssignment.map values
    let inheritedEnv : Fin patternLeaf.inheritedWires.length → model.Carrier :=
      fun index =>
        assignment.classes (Splice.Input.PlugLayout.exposedWireIndex input
          (patternLeaf.inheritedWires.get index)
          ((input.plugLayout.terminalBody_inherited_mem_iff_exposed patternWitness
            patternLeaf hnonempty (patternLeaf.inheritedWires.get index)).1
              (List.get_mem _ index)))
    let terminalRelations : RelationRenaming
        patternWitness.toFocus.holeRels outputWitness.toFocus.holeRels :=
      fun relation =>
        input.plugLayout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf
          (input.plugLayout.coalescedTerminalRelationRenaming hadmissible
            host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
            hnonempty relation)
    denoteRegion model named inheritedEnv
      (RelEnv.pullback terminalRelations relEnv)
      (ConcreteElaboration.finishRegion input.pattern.val.diagram
        patternLeaf.inheritedWires input.binderSpine.bodyContainer
        patternLeaf.items) := by
  dsimp only
  let context := outputLeaf.inheritedWires.extend
    (input.plugLayout.frameRegion input.site)
  let values := Splice.Input.siteQuotientEnvironment input context
    outputLeaf.wiresExact env fallback
  let assignment := input.patternAttachmentAssignment.map values
  let inheritedEnv : Fin patternLeaf.inheritedWires.length → model.Carrier :=
    fun index =>
      assignment.classes (Splice.Input.PlugLayout.exposedWireIndex input
        (patternLeaf.inheritedWires.get index)
        ((input.plugLayout.terminalBody_inherited_mem_iff_exposed patternWitness
          patternLeaf hnonempty (patternLeaf.inheritedWires.get index)).1
            (List.get_mem _ index)))
  let localEnv : Fin (ConcreteElaboration.exactScopeWires
      input.pattern.val.diagram input.binderSpine.bodyContainer).length →
      model.Carrier := fun index =>
    env (input.plugLayout.patternSeamWireMapOfNonempty hadmissible host
      patternWitness patternLeaf outputWitness outputLeaf hnonempty
      (Fin.cast
        (ConcreteElaboration.WireContext.length_extend
          patternLeaf.inheritedWires input.binderSpine.bodyContainer).symm
        (Fin.natAdd patternLeaf.inheritedWires.length index)))
  let terminalRelations : RelationRenaming
      patternWitness.toFocus.holeRels outputWitness.toFocus.holeRels :=
    fun relation =>
      input.plugLayout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf
        (input.plugLayout.coalescedTerminalRelationRenaming hadmissible
          host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
          hnonempty relation)
  have seamItems : denoteItemSeq model named
      (env ∘ input.plugLayout.patternSeamWireMapOfNonempty hadmissible host
        patternWitness patternLeaf outputWitness outputLeaf hnonempty)
      (RelEnv.pullback terminalRelations relEnv) patternLeaf.items := by
    simpa [terminalRelations,
      Splice.Input.PlugLayout.patternSeamWireMapOfNonempty,
      Function.comp_def] using nativeItems
  have environmentEq := patternTerminalExtendedEnvironment_seam input
    hadmissible host patternWitness patternLeaf outputWitness outputLeaf hnonempty
    env fallback
  change ConcreteElaboration.extendedEnvironment patternLeaf.inheritedWires
      input.binderSpine.bodyContainer inheritedEnv localEnv =
    env ∘ input.plugLayout.patternSeamWireMapOfNonempty hadmissible host
      patternWitness patternLeaf outputWitness outputLeaf hnonempty
    at environmentEq
  rw [← environmentEq] at seamItems
  unfold ConcreteElaboration.finishRegion
  simp only [denoteRegion_mk]
  refine ⟨localEnv, ?_⟩
  rw [ItemSeq.castWiresEq_eq_renameWires, denoteItemSeq_renameWires]
  exact seamItems

/-- A denoting next-state survivor block certifies the same fixed terminal
relation as a full splice output, without requiring previously processed host
atoms to be reintroduced. -/
theorem terminalRelationOfValues_of_survivor
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
    (hnonempty : payload.binderSpine.proxyCount ≠ 0)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (values : ∀ index,
      Relation model.Carrier (payload.binderSpine.arity index))
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Splice.Region.ContextPath.CompilerLeaf
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site) outputWitness)
    (env : Fin (outputLeaf.inheritedWires.extend
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site)).length → model.Carrier)
    (outputRelEnv : RelEnv model.Carrier outputWitness.toFocus.holeRels)
    (fallback : model.Carrier)
    (survivorItems : ItemSeq signature
      (outputLeaf.inheritedWires.extend
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion site)).length
      outputWitness.toFocus.holeRels)
    (survivorCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val
      (compileSurvivorRegion? signature
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible) outputLeaf.fuel)
      (outputLeaf.inheritedWires.extend
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion site))
      outputLeaf.binders
      ((ConcreteElaboration.localOccurrences
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible).diagram.val
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion site)).filter
        (dropOccurrenceSurvives
          (advanceInstantiationState comprehension attachments binders payload
            state atom tail site arguments hadmissible))) = some survivorItems)
    (survivorDenotes : denoteItemSeq model named env outputRelEnv survivorItems)
    (fixed :
      let spliceInput := instantiateSpliceInput comprehension attachments binders
        payload state site arguments
      let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
      let hostRelations : RelationRenaming host.intrinsicPath.toFocus.holeRels
          outputWitness.toFocus.holeRels := fun relation =>
        spliceInput.plugLayout.hostRelationRenaming host.intrinsicPath
          host.compilerLeaf outputWitness outputLeaf relation
      ProxyRelationsAt payload state host.compilerLeaf.binders
        (RelEnv.pullback hostRelations outputRelEnv) values) :
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let context := outputLeaf.inheritedWires.extend
      (spliceInput.plugLayout.frameRegion site)
    let quotientValues := Splice.Input.siteQuotientEnvironment spliceInput context
      outputLeaf.wiresExact env fallback
    let wireValue : Fin state.diagram.val.wireCount → model.Carrier :=
      fun wire => quotientValues (spliceInput.quotientWire wire)
    terminalRelationOfValues payload state site arguments hnonempty model named
      wireValue values (wireValue ∘ arguments) := by
  dsimp only
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
  let context := outputLeaf.inheritedWires.extend (layout.frameRegion site)
  let quotientValues := Splice.Input.siteQuotientEnvironment spliceInput context
    outputLeaf.wiresExact env fallback
  let wireValue : Fin state.diagram.val.wireCount → model.Carrier :=
    fun wire => quotientValues (spliceInput.quotientWire wire)
  let assignment := spliceInput.patternAttachmentAssignment.map quotientValues
  let hostRelations : RelationRenaming host.intrinsicPath.toFocus.holeRels
      outputWitness.toFocus.holeRels := fun relation =>
    layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
      outputWitness outputLeaf relation
  let terminalRelations : RelationRenaming pattern.witness.toFocus.holeRels
      outputWitness.toFocus.holeRels := fun relation =>
    hostRelations (layout.coalescedTerminalRelationRenaming hadmissible
      host.intrinsicPath host.compilerLeaf pattern.witness pattern.leaf hnonempty
      relation)
  let terminalRelEnv := RelEnv.pullback terminalRelations outputRelEnv
  change ∃ assignment : BoundaryAssignment comprehension.elaborate model.Carrier,
    assignment.args =
        Fin.addCases (wireValue ∘ arguments) (wireValue ∘ state.parameters) ∘
          Fin.cast payload.boundarySplit ∧
      ∃ relEnv : RelEnv model.Carrier pattern.witness.toFocus.holeRels,
        TerminalRelationsMatch payload state site arguments hnonempty values
            relEnv ∧
          denoteRegion model named
            (terminalInheritedEnvironment payload state site arguments hnonempty
              assignment)
            relEnv
            (ConcreteElaboration.finishRegion comprehension.val.diagram
              pattern.leaf.inheritedWires payload.binderSpine.bodyContainer
              pattern.leaf.items)
  refine ⟨assignment, ?_, terminalRelEnv, ?_, ?_⟩
  · funext position
    let split : Fin (payload.arity + attachments.length) :=
      Fin.cast payload.boundarySplit position
    change quotientValues
        (spliceInput.quotientWire
          (Fin.addCases arguments state.parameters split)) =
      Fin.addCases
        (fun index => quotientValues
          (spliceInput.quotientWire (arguments index)))
        (fun index => quotientValues
          (spliceInput.quotientWire (state.parameters index))) split
    exact Fin.addCases
      (fun index => by simp only [Fin.addCases_left])
      (fun index => by simp only [Fin.addCases_right]) split
  · exact terminalOutputRelations_match payload state site arguments hnonempty
      hadmissible values outputWitness outputLeaf outputRelEnv fixed
  · have nativeItems := advance_terminalItems_denotes_nonempty comprehension
      attachments binders payload state atom tail site arguments hadmissible host
      pattern.witness pattern.leaf outputWitness outputLeaf hnonempty model named
      env outputRelEnv survivorItems survivorCompiled survivorDenotes
    have recovered := patternTerminalRegion_denotes_of_native_items spliceInput
      hadmissible host pattern.witness pattern.leaf outputWitness outputLeaf
      hnonempty model named env outputRelEnv fallback nativeItems
    simpa [terminalRelEnv, terminalRelations, terminalInheritedEnvironment,
      assignment, quotientValues, context, pattern, layout, Function.comp_def]
      using recovered

/-- Zero-spine survivor extraction directly certifies the payload's
authoritative interpreted relation at the executor-recorded argument vector. -/
theorem interpretedRelation_of_survivor_empty
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
    (hzero : payload.binderSpine.proxyCount = 0)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Splice.Region.ContextPath.CompilerLeaf
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.plugRaw
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site) outputWitness)
    (env : Fin (outputLeaf.inheritedWires.extend
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site)).length → model.Carrier)
    (outputRelEnv : RelEnv model.Carrier outputWitness.toFocus.holeRels)
    (fallback : model.Carrier)
    (survivorItems : ItemSeq signature
      (outputLeaf.inheritedWires.extend
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion site)).length
      outputWitness.toFocus.holeRels)
    (survivorCompiled : ConcreteElaboration.compileOccurrencesWith? signature
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val
      (compileSurvivorRegion? signature
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible) outputLeaf.fuel)
      (outputLeaf.inheritedWires.extend
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion site))
      outputLeaf.binders
      ((ConcreteElaboration.localOccurrences
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible).diagram.val
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion site)).filter
        (dropOccurrenceSurvives
          (advanceInstantiationState comprehension attachments binders payload
            state atom tail site arguments hadmissible))) = some survivorItems)
    (survivorDenotes : denoteItemSeq model named env outputRelEnv survivorItems) :
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let context := outputLeaf.inheritedWires.extend
      (spliceInput.plugLayout.frameRegion site)
    let quotientValues := Splice.Input.siteQuotientEnvironment spliceInput
      context outputLeaf.wiresExact env fallback
    let wireValue : Fin state.diagram.val.wireCount → model.Carrier :=
      fun wire => quotientValues (spliceInput.quotientWire wire)
    payload.interpretedRelation model named (wireValue ∘ state.parameters)
      (wireValue ∘ arguments) := by
  dsimp only
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  let context := outputLeaf.inheritedWires.extend (layout.frameRegion site)
  let quotientValues := Splice.Input.siteQuotientEnvironment spliceInput
    context outputLeaf.wiresExact env fallback
  let wireValue : Fin state.diagram.val.wireCount → model.Carrier :=
    fun wire => quotientValues (spliceInput.quotientWire wire)
  have nativeItems := advance_patternRootItems_denotes_empty comprehension
    attachments binders payload state atom tail site arguments hadmissible host
    outputWitness outputLeaf hzero model named env outputRelEnv survivorItems
    survivorCompiled survivorDenotes
  dsimp only at nativeItems
  let targetEq := ConcreteElaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion site)
  let targetEnv : Fin
      (outputLeaf.inheritedWires.length +
        (ConcreteElaboration.exactScopeWires layout.plugRaw
          (layout.frameRegion site)).length) → model.Carrier :=
    env ∘ Fin.cast targetEq.symm
  let combined := layout.siteCombinedWireEquivOfEmpty hadmissible host
    outputWitness outputLeaf hzero
  let sourceEnv := targetEnv ∘ combined
  have seamEq := layout.patternRootSeamWireMapOfEmpty_eq hadmissible host
    outputWitness outputLeaf hzero
  have environmentEq :
      sourceEnv ∘ layout.patternRootSeamPreparedWireOfEmpty hadmissible host =
        env ∘ layout.patternRootWireIndexMap hadmissible hzero outputWitness
          outputLeaf := by
    funext index
    exact congrArg env (congrFun seamEq index)
  have nativeItems' : denoteItemSeq (relCtx := []) model named
      (sourceEnv ∘ layout.patternRootSeamPreparedWireOfEmpty hadmissible host)
      PUnit.unit
      (Splice.Input.compiledSpliceOpenRootItems comprehension).items := by
    simpa [sourceEnv, targetEnv, combined, layout, spliceInput]
      using nativeItems
  rw [environmentEq] at nativeItems'
  have patternDenotes := Splice.Input.pattern_denote_of_patternRootItems
    spliceInput hadmissible outputWitness outputLeaf hzero model named env
    fallback nativeItems'
  have argumentValues :
      (fun position => quotientValues
        (spliceInput.quotientWire (spliceInput.attachment position))) =
      Fin.addCases (wireValue ∘ arguments) (wireValue ∘ state.parameters) ∘
        Fin.cast payload.boundarySplit := by
    funext position
    let split := Fin.cast payload.boundarySplit position
    have recover : Fin.cast payload.boundarySplit.symm split = position := by
      apply Fin.ext
      rfl
    rw [← recover]
    refine Fin.addCases (fun argument => ?_) (fun parameter => ?_) split
    · simp [spliceInput, instantiateSpliceInput, wireValue,
        Function.comp_def]
    · simp [spliceInput, instantiateSpliceInput, wireValue,
        Function.comp_def]
  change comprehension.denote model named
    (Fin.addCases (wireValue ∘ arguments) (wireValue ∘ state.parameters) ∘
      Fin.cast payload.boundarySplit)
  rw [← argumentValues]
  exact patternDenotes

end InstantiationSemantic

end VisualProof.Rule
