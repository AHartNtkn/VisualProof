import VisualProof.Rule.Soundness.Comprehension.InstantiationCoalescedState

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- The actual nonzero-spine next-state survivor receipt reconstructs the
selected source atom.  Both the certificate and the source atom are evaluated
through the same quotient valuation and the same fixed relation witness. -/
theorem advance_current_atom_denotes_nonempty
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
    (outputEnv : Fin (outputLeaf.inheritedWires.extend
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
    (survivorDenotes : denoteItemSeq model named outputEnv outputRelEnv
      survivorItems)
    (proxyFixed :
      let spliceInput := instantiateSpliceInput comprehension attachments binders
        payload state site arguments
      let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
      let hostRelations : RelationRenaming host.intrinsicPath.toFocus.holeRels
          outputWitness.toFocus.holeRels := fun relation =>
        spliceInput.plugLayout.hostRelationRenaming host.intrinsicPath
          host.compilerLeaf outputWitness outputLeaf relation
      ProxyRelationsAt payload state host.compilerLeaf.binders
        (RelEnv.pullback hostRelations outputRelEnv) values)
    {sourceRels : RelCtx}
    (sourceContext : ConcreteElaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw)
    (sourceBinders : ConcreteElaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceRels)
    (sourceRelEnv : RelEnv model.Carrier sourceRels)
    (sourceFixed :
      let spliceInput := instantiateSpliceInput comprehension attachments binders
        payload state site arguments
      let outputContext := outputLeaf.inheritedWires.extend
        (spliceInput.plugLayout.frameRegion site)
      let quotientValues := Splice.Input.siteQuotientEnvironment spliceInput
        outputContext outputLeaf.wiresExact outputEnv fallback
      FixedRelationAt payload
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible)
        (terminalRelationOfValues payload state site arguments hnonempty model
          named (fun wire => quotientValues (spliceInput.quotientWire wire))
          values)
        sourceBinders sourceRelEnv)
    (sourceRelation : RelVar sourceRels payload.arity)
    (sourceLookup : sourceBinders state.bubble =
      some ⟨payload.arity, sourceRelation⟩)
    (sourceEnv : Fin sourceContext.length → model.Carrier)
    (sourceEnvEq :
      let spliceInput := instantiateSpliceInput comprehension attachments binders
        payload state site arguments
      let outputContext := outputLeaf.inheritedWires.extend
        (spliceInput.plugLayout.frameRegion site)
      let quotientValues := Splice.Input.siteQuotientEnvironment spliceInput
        outputContext outputLeaf.wiresExact outputEnv fallback
      ∀ index, sourceEnv index = quotientValues (sourceContext.get index))
    (sourceItem : Item signature sourceContext.length sourceRels)
    (sourceCompiled : ConcreteElaboration.compileNode? signature
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceContext sourceBinders atom =
      some sourceItem) :
    denoteItem model named sourceEnv sourceRelEnv sourceItem := by
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let outputContext := outputLeaf.inheritedWires.extend
    (spliceInput.plugLayout.frameRegion site)
  let quotientValues := Splice.Input.siteQuotientEnvironment spliceInput
    outputContext outputLeaf.wiresExact outputEnv fallback
  have terminal := terminalRelationOfValues_of_survivor comprehension attachments
    binders payload state atom tail site arguments hnonempty hadmissible model
    named values outputWitness outputLeaf outputEnv outputRelEnv fallback
    survivorItems survivorCompiled survivorDenotes proxyFixed
  exact coalesced_current_atom_denotes_of_terminal comprehension attachments
    binders payload state atom site arguments node_eq arguments_eq hnonempty
    hadmissible model named quotientValues values sourceContext sourceBinders
    sourceRelEnv sourceFixed sourceRelation sourceLookup sourceEnv sourceEnvEq
    sourceItem sourceCompiled terminal

/-- Zero-spine counterpart: the authoritative interpreted comprehension
extracted from the next survivor reconstructs the selected source atom. -/
theorem advance_current_atom_denotes_empty
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
    (outputEnv : Fin (outputLeaf.inheritedWires.extend
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
    (survivorDenotes : denoteItemSeq model named outputEnv outputRelEnv
      survivorItems)
    {sourceRels : RelCtx}
    (sourceContext : ConcreteElaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw)
    (sourceBinders : ConcreteElaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceRels)
    (sourceRelEnv : RelEnv model.Carrier sourceRels)
    (sourceFixed :
      let spliceInput := instantiateSpliceInput comprehension attachments binders
        payload state site arguments
      let outputContext := outputLeaf.inheritedWires.extend
        (spliceInput.plugLayout.frameRegion site)
      let quotientValues := Splice.Input.siteQuotientEnvironment spliceInput
        outputContext outputLeaf.wiresExact outputEnv fallback
      FixedRelationAt payload
        (coalescedInstantiationState comprehension attachments binders payload
          state site arguments hadmissible)
        (payload.interpretedRelation model named
          (fun index => quotientValues
            (spliceInput.quotientWire (state.parameters index))))
        sourceBinders sourceRelEnv)
    (sourceRelation : RelVar sourceRels payload.arity)
    (sourceLookup : sourceBinders state.bubble =
      some ⟨payload.arity, sourceRelation⟩)
    (sourceEnv : Fin sourceContext.length → model.Carrier)
    (sourceEnvEq :
      let spliceInput := instantiateSpliceInput comprehension attachments binders
        payload state site arguments
      let outputContext := outputLeaf.inheritedWires.extend
        (spliceInput.plugLayout.frameRegion site)
      let quotientValues := Splice.Input.siteQuotientEnvironment spliceInput
        outputContext outputLeaf.wiresExact outputEnv fallback
      ∀ index, sourceEnv index = quotientValues (sourceContext.get index))
    (sourceItem : Item signature sourceContext.length sourceRels)
    (sourceCompiled : ConcreteElaboration.compileNode? signature
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceContext sourceBinders atom =
      some sourceItem) :
    denoteItem model named sourceEnv sourceRelEnv sourceItem := by
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let outputContext := outputLeaf.inheritedWires.extend
    (spliceInput.plugLayout.frameRegion site)
  let quotientValues := Splice.Input.siteQuotientEnvironment spliceInput
    outputContext outputLeaf.wiresExact outputEnv fallback
  have interpreted := interpretedRelation_of_survivor_empty comprehension
    attachments binders payload state atom tail site arguments hzero hadmissible
    model named outputWitness outputLeaf outputEnv outputRelEnv fallback
    survivorItems survivorCompiled survivorDenotes
  exact coalesced_current_atom_denotes_of_interpreted comprehension attachments
    binders payload state atom site arguments node_eq arguments_eq hadmissible
    model named quotientValues sourceContext sourceBinders sourceRelEnv
    sourceFixed sourceRelation sourceLookup sourceEnv sourceEnvEq sourceItem
    sourceCompiled interpreted

end InstantiationSemantic

end VisualProof.Rule
