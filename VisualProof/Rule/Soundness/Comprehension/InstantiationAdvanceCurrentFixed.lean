import VisualProof.Rule.Soundness.Comprehension.InstantiationBubbleInvariant
import VisualProof.Rule.Soundness.Comprehension.InstantiationFixedSimulation

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- Fixed-relation form of current-atom recovery for a nonempty binder spine.
All lexical fixedness premises are derived from the target compiler receipt;
the caller supplies only the trace-stable equality identifying the selected
relation with the terminal comprehension relation. -/
theorem advance_current_atom_denotes_nonempty_fixed
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
    (shape : BubbleHasPayloadArity payload state)
    (hnonempty : payload.binderSpine.proxyCount ≠ 0)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (relationValue : Relation model.Carrier payload.arity)
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
    (targetFixed : FixedRelationAt payload
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible)
      relationValue outputLeaf.binders outputRelEnv)
    (targetProxies : ProxyRelationsAt payload
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible)
      outputLeaf.binders outputRelEnv values)
    {sourceRels : RelCtx}
    (sourceContext : ConcreteElaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw)
    (sourceBinders : ConcreteElaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceRels)
    (sourceCover : sourceBinders.Covers site)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceBinders site)
    (relationMap : RelationRenaming sourceRels
      outputWitness.toFocus.holeRels)
    (relationSpec : ∀ {arity} (relation : RelVar sourceRels arity),
      outputLeaf.binders
          ((instantiateSpliceInput comprehension attachments binders payload
            state site arguments).plugLayout.frameRegion
            (sourceEnumeration.binder relation.index)) =
        some ⟨arity, relationMap relation⟩)
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
      some sourceItem)
    (relationEq :
      let spliceInput := instantiateSpliceInput comprehension attachments binders
        payload state site arguments
      let outputContext := outputLeaf.inheritedWires.extend
        (spliceInput.plugLayout.frameRegion site)
      let quotientValues := Splice.Input.siteQuotientEnvironment spliceInput
        outputContext outputLeaf.wiresExact outputEnv fallback
      relationValue = terminalRelationOfValues payload state site arguments
        hnonempty model named
        (fun wire => quotientValues (spliceInput.quotientWire wire)) values) :
    denoteItem model named sourceEnv
      (RelEnv.pullback relationMap outputRelEnv) sourceItem := by
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  obtain ⟨sourceRelation, sourceLookup⟩ :=
    coalesced_bubbleRelation_exists comprehension attachments binders payload
      state atom site arguments node_eq hadmissible shape sourceBinders
      sourceCover
  have sourceFixed := fixedRelationAt_pullback_frame comprehension attachments
    binders payload state atom tail site arguments hadmissible site sourceBinders
    outputLeaf.binders sourceEnumeration relationMap relationSpec model
    relationValue outputRelEnv targetFixed
  have proxyFixed := proxyRelationsAt_host_pullback comprehension attachments
    binders payload state atom tail site arguments hadmissible
    host.intrinsicPath host.compilerLeaf outputWitness outputLeaf model values
    outputRelEnv targetProxies
  have recovered := advance_current_atom_denotes_nonempty comprehension
    attachments binders payload state atom tail site arguments node_eq
    arguments_eq hnonempty hadmissible model named values outputWitness
    outputLeaf outputEnv outputRelEnv fallback survivorItems survivorCompiled
    survivorDenotes proxyFixed sourceContext sourceBinders
    (RelEnv.pullback relationMap outputRelEnv) (by
      simpa only [relationEq] using sourceFixed)
    sourceRelation sourceLookup sourceEnv sourceEnvEq sourceItem sourceCompiled
  exact recovered

/-- Zero-spine counterpart: the fixed moving relation is the payload's
authoritative interpreted open comprehension, so the target receipt again
supplies all remaining lexical evidence. -/
theorem advance_current_atom_denotes_empty_fixed
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
    (shape : BubbleHasPayloadArity payload state)
    (hzero : payload.binderSpine.proxyCount = 0)
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (relationValue : Relation model.Carrier payload.arity)
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
    (targetFixed : FixedRelationAt payload
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible)
      relationValue outputLeaf.binders outputRelEnv)
    {sourceRels : RelCtx}
    (sourceContext : ConcreteElaboration.WireContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw)
    (sourceBinders : ConcreteElaboration.BinderContext
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceRels)
    (sourceCover : sourceBinders.Covers site)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      (instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrameRaw sourceBinders site)
    (relationMap : RelationRenaming sourceRels
      outputWitness.toFocus.holeRels)
    (relationSpec : ∀ {arity} (relation : RelVar sourceRels arity),
      outputLeaf.binders
          ((instantiateSpliceInput comprehension attachments binders payload
            state site arguments).plugLayout.frameRegion
            (sourceEnumeration.binder relation.index)) =
        some ⟨arity, relationMap relation⟩)
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
      some sourceItem)
    (relationEq :
      let spliceInput := instantiateSpliceInput comprehension attachments binders
        payload state site arguments
      let outputContext := outputLeaf.inheritedWires.extend
        (spliceInput.plugLayout.frameRegion site)
      let quotientValues := Splice.Input.siteQuotientEnvironment spliceInput
        outputContext outputLeaf.wiresExact outputEnv fallback
      relationValue = payload.interpretedRelation model named
        (fun index => quotientValues
          (spliceInput.quotientWire (state.parameters index)))) :
    denoteItem model named sourceEnv
      (RelEnv.pullback relationMap outputRelEnv) sourceItem := by
  obtain ⟨sourceRelation, sourceLookup⟩ :=
    coalesced_bubbleRelation_exists comprehension attachments binders payload
      state atom site arguments node_eq hadmissible shape sourceBinders
      sourceCover
  have sourceFixed := fixedRelationAt_pullback_frame comprehension attachments
    binders payload state atom tail site arguments hadmissible site sourceBinders
    outputLeaf.binders sourceEnumeration relationMap relationSpec model
    relationValue outputRelEnv targetFixed
  have recovered := advance_current_atom_denotes_empty comprehension attachments
    binders payload state atom tail site arguments node_eq arguments_eq hzero
    hadmissible model named outputWitness outputLeaf outputEnv outputRelEnv
    fallback survivorItems survivorCompiled survivorDenotes sourceContext
    sourceBinders (RelEnv.pullback relationMap outputRelEnv) (by
      simpa only [relationEq] using sourceFixed)
    sourceRelation sourceLookup sourceEnv sourceEnvEq sourceItem sourceCompiled
  exact recovered

end InstantiationSemantic

end VisualProof.Rule
