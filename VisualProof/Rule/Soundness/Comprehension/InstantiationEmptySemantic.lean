import VisualProof.Rule.Soundness.Comprehension.InstantiationTerminalFixed

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- A denoting post-splice compiler leaf in the zero-spine branch contains
the open pattern's complete root conjunction under the authoritative seam
map. -/
theorem patternRootItems_denotes_of_output
    {signature : List Nat}
    (input : Splice.Input signature)
    (hadmissible : input.Admissible)
    (host : Splice.SiteView (input.coalesceFrame hadmissible) input.site)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Splice.Region.ContextPath.CompilerLeaf input.plugLayout.plugRaw
      (input.plugLayout.frameRegion input.site) outputWitness)
    (hzero : input.binderSpine.proxyCount = 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin (outputLeaf.inheritedWires.extend
      (input.plugLayout.frameRegion input.site)).length → model.Carrier)
    (relEnv : RelEnv model.Carrier outputWitness.toFocus.holeRels)
    (denotes : denoteItemSeq model named env relEnv outputLeaf.items) :
    let pattern := Splice.Input.compiledSpliceOpenRootItems input.pattern
    denoteItemSeq (relCtx := []) model named
      (env ∘ input.plugLayout.patternRootWireIndexMap hadmissible hzero
        outputWitness outputLeaf)
      (PUnit.unit : RelEnv model.Carrier []) pattern.items := by
  dsimp only
  let layout := input.plugLayout
  let pattern := Splice.Input.compiledSpliceOpenRootItems input.pattern
  let targetEq := ConcreteElaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  let targetEnv : Fin
      (outputLeaf.inheritedWires.length +
        (ConcreteElaboration.exactScopeWires layout.plugRaw
          (layout.frameRegion input.site)).length) → model.Carrier :=
    env ∘ Fin.cast targetEq.symm
  let combined := layout.siteCombinedWireEquivOfEmpty hadmissible host
    outputWitness outputLeaf hzero
  let sourceEnv := targetEnv ∘ combined
  let patternRelations : RelationRenaming []
      outputWitness.toFocus.holeRels :=
    Splice.Input.PlugLayout.emptyRelationRenaming
      outputWitness.toFocus.holeRels
  let patternPrepared :=
    (pattern.items.renameWires
      (layout.patternRootSeamPreparedWireOfEmpty hadmissible host))
        |>.renameRelations patternRelations
  have targetDenotes : denoteItemSeq model named targetEnv relEnv
      (outputLeaf.items.castWiresEq targetEq) := by
    rw [ItemSeq.castWiresEq_eq_renameWires,
      denoteItemSeq_renameWires]
    simpa [targetEnv, targetEq, Function.comp_def] using denotes
  have itemsIso := layout.compiledSiteItemsIsoOfEmpty signature input
    hadmissible host outputWitness outputLeaf hzero pattern.items
    pattern.computation
  have preparedDenotes : denoteItemSeq model named sourceEnv relEnv
      (((host.compilerLeaf.items.renameWires
        (layout.hostSeamPreparedWireOfEmpty hadmissible host)).renameRelations
          (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
            outputWitness outputLeaf)).append patternPrepared) := by
    apply (itemsIso.denotation model named sourceEnv targetEnv relEnv ?_).mpr
    · exact targetDenotes
    · intro index
      rfl
  rw [denoteItemSeq_append] at preparedDenotes
  have patternPreparedDenotes := preparedDenotes.2
  change denoteItemSeq model named sourceEnv relEnv
      ((pattern.items.renameWires
        (layout.patternRootSeamPreparedWireOfEmpty hadmissible host))
          |>.renameRelations patternRelations) at patternPreparedDenotes
  rw [denoteItemSeq_renameRelations model named patternRelations
    (PUnit.unit : RelEnv model.Carrier []) relEnv
    (RelEnv.pullback_agrees patternRelations relEnv)] at patternPreparedDenotes
  rw [denoteItemSeq_renameWires] at patternPreparedDenotes
  have seamEq := layout.patternRootSeamWireMapOfEmpty_eq hadmissible host
    outputWitness outputLeaf hzero
  have environmentEq :
      sourceEnv ∘
          layout.patternRootSeamPreparedWireOfEmpty hadmissible host =
        env ∘ layout.patternRootWireIndexMap hadmissible hzero outputWitness
          outputLeaf := by
    funext index
    exact congrArg env (congrFun seamEq index)
  rw [environmentEq] at patternPreparedDenotes
  exact patternPreparedDenotes

/-- Converse seam transport for the zero-spine branch.  A denoting retained
host block together with the complete prepared open-pattern root block
constructs the authoritative post-splice compiler conjunction. -/
theorem output_denotes_of_host_and_patternRootPrepared
    {signature : List Nat}
    (input : Splice.Input signature)
    (hadmissible : input.Admissible)
    (host : Splice.SiteView (input.coalesceFrame hadmissible) input.site)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Splice.Region.ContextPath.CompilerLeaf input.plugLayout.plugRaw
      (input.plugLayout.frameRegion input.site) outputWitness)
    (hzero : input.binderSpine.proxyCount = 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin (outputLeaf.inheritedWires.extend
      (input.plugLayout.frameRegion input.site)).length → model.Carrier)
    (relEnv : RelEnv model.Carrier outputWitness.toFocus.holeRels)
    (hostDenotes :
      let layout := input.plugLayout
      let targetEq := ConcreteElaboration.WireContext.length_extend
        outputLeaf.inheritedWires (layout.frameRegion input.site)
      let targetEnv : Fin
          (outputLeaf.inheritedWires.length +
            (ConcreteElaboration.exactScopeWires layout.plugRaw
              (layout.frameRegion input.site)).length) → model.Carrier :=
        env ∘ Fin.cast targetEq.symm
      let combined := layout.siteCombinedWireEquivOfEmpty hadmissible host
        outputWitness outputLeaf hzero
      let sourceEnv := targetEnv ∘ combined
      let hostPrepared :=
        (host.compilerLeaf.items.renameWires
          (layout.hostSeamPreparedWireOfEmpty hadmissible host)).renameRelations
          (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
            outputWitness outputLeaf)
      denoteItemSeq model named sourceEnv relEnv hostPrepared)
    (patternDenotes :
      let layout := input.plugLayout
      let pattern := Splice.Input.compiledSpliceOpenRootItems input.pattern
      let targetEq := ConcreteElaboration.WireContext.length_extend
        outputLeaf.inheritedWires (layout.frameRegion input.site)
      let targetEnv : Fin
          (outputLeaf.inheritedWires.length +
            (ConcreteElaboration.exactScopeWires layout.plugRaw
              (layout.frameRegion input.site)).length) → model.Carrier :=
        env ∘ Fin.cast targetEq.symm
      let combined := layout.siteCombinedWireEquivOfEmpty hadmissible host
        outputWitness outputLeaf hzero
      let sourceEnv := targetEnv ∘ combined
      let patternRelations : RelationRenaming []
          outputWitness.toFocus.holeRels :=
        Splice.Input.PlugLayout.emptyRelationRenaming
          outputWitness.toFocus.holeRels
      let patternPrepared :=
        (pattern.items.renameWires
          (layout.patternRootSeamPreparedWireOfEmpty hadmissible host))
          |>.renameRelations patternRelations
      denoteItemSeq model named sourceEnv relEnv patternPrepared) :
    denoteItemSeq model named env relEnv outputLeaf.items := by
  dsimp only at hostDenotes patternDenotes
  let layout := input.plugLayout
  let pattern := Splice.Input.compiledSpliceOpenRootItems input.pattern
  let targetEq := ConcreteElaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  let targetEnv : Fin
      (outputLeaf.inheritedWires.length +
        (ConcreteElaboration.exactScopeWires layout.plugRaw
          (layout.frameRegion input.site)).length) → model.Carrier :=
    env ∘ Fin.cast targetEq.symm
  let combined := layout.siteCombinedWireEquivOfEmpty hadmissible host
    outputWitness outputLeaf hzero
  let sourceEnv := targetEnv ∘ combined
  let hostPrepared :=
    (host.compilerLeaf.items.renameWires
      (layout.hostSeamPreparedWireOfEmpty hadmissible host)).renameRelations
      (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf)
  let patternRelations : RelationRenaming [] outputWitness.toFocus.holeRels :=
    Splice.Input.PlugLayout.emptyRelationRenaming
      outputWitness.toFocus.holeRels
  let patternPrepared :=
    (pattern.items.renameWires
      (layout.patternRootSeamPreparedWireOfEmpty hadmissible host))
      |>.renameRelations patternRelations
  have preparedDenotes : denoteItemSeq model named sourceEnv relEnv
      (hostPrepared.append patternPrepared) := by
    rw [denoteItemSeq_append]
    exact ⟨hostDenotes, patternDenotes⟩
  have itemsIso := layout.compiledSiteItemsIsoOfEmpty signature input
    hadmissible host outputWitness outputLeaf hzero pattern.items
    pattern.computation
  have targetCastDenotes : denoteItemSeq model named targetEnv relEnv
      (outputLeaf.items.castWiresEq targetEq) := by
    exact (itemsIso.denotation model named sourceEnv targetEnv relEnv
      (fun _ => rfl)).mp preparedDenotes
  rw [ItemSeq.castWiresEq_eq_renameWires,
    denoteItemSeq_renameWires] at targetCastDenotes
  simpa [targetEnv, targetEq, Function.comp_def] using targetCastDenotes

/-- Zero-spine output extraction in checked-open form.  The valuation is the
same quotient valuation used by the executor, so repeated boundary aliases
remain repeated rather than being silently separated. -/
theorem pattern_denote_of_output
    {signature : List Nat}
    (input : Splice.Input signature)
    (hadmissible : input.Admissible)
    (host : Splice.SiteView (input.coalesceFrame hadmissible) input.site)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Splice.Region.ContextPath.CompilerLeaf input.plugLayout.plugRaw
      (input.plugLayout.frameRegion input.site) outputWitness)
    (hzero : input.binderSpine.proxyCount = 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin (outputLeaf.inheritedWires.extend
      (input.plugLayout.frameRegion input.site)).length → model.Carrier)
    (relEnv : RelEnv model.Carrier outputWitness.toFocus.holeRels)
    (fallback : model.Carrier)
    (denotes : denoteItemSeq model named env relEnv outputLeaf.items) :
    let context := outputLeaf.inheritedWires.extend
      (input.plugLayout.frameRegion input.site)
    let values := Splice.Input.siteQuotientEnvironment input context
      outputLeaf.wiresExact env fallback
    input.pattern.denote model named (fun position =>
      values (input.quotientWire (input.attachment position))) := by
  dsimp only
  let context := outputLeaf.inheritedWires.extend
    (input.plugLayout.frameRegion input.site)
  let values := Splice.Input.siteQuotientEnvironment input context
    outputLeaf.wiresExact env fallback
  apply Splice.Input.pattern_denote_of_patternRootItems input hadmissible
    outputWitness outputLeaf hzero model named env fallback
  exact patternRootItems_denotes_of_output input hadmissible host outputWitness
    outputLeaf hzero model named env relEnv denotes

/-- In the zero-spine executor branch, every denoting splice output certifies
the payload's authoritative interpreted relation at the receipt-recorded
argument vector. -/
theorem interpretedRelation_of_output_empty
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
    (denotes : denoteItemSeq model named env outputRelEnv outputLeaf.items) :
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
  let host := Splice.Input.compiledSpliceHostView spliceInput hadmissible
  let context := outputLeaf.inheritedWires.extend
    (spliceInput.plugLayout.frameRegion site)
  let quotientValues := Splice.Input.siteQuotientEnvironment spliceInput
    context outputLeaf.wiresExact env fallback
  let wireValue : Fin state.diagram.val.wireCount → model.Carrier :=
    fun wire => quotientValues (spliceInput.quotientWire wire)
  have patternDenotes := pattern_denote_of_output spliceInput hadmissible host
    outputWitness outputLeaf hzero model named env outputRelEnv fallback denotes
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
