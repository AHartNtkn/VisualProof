import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvancePatternCompiler

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- Zero-spine counterpart of `advance_pattern_item_denotes_nonempty`.  The
source item is compiled at the checked-open sheet root, while the target item
is located in the executor's actual survivor occurrence list. -/
theorem advance_pattern_root_item_denotes_empty
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
    (host : Splice.SiteView
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrame hadmissible) site)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Splice.Region.ContextPath.CompilerLeaf
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site) outputWitness)
    (hzero : payload.binderSpine.proxyCount = 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin (outputLeaf.inheritedWires.extend
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site)).length → model.Carrier)
    (relEnv : RelEnv model.Carrier outputWitness.toFocus.holeRels)
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
    (survivorDenotes : denoteItemSeq model named env relEnv survivorItems)
    (occurrence : ConcreteElaboration.LocalOccurrence
      comprehension.val.diagram.regionCount comprehension.val.diagram.nodeCount)
    (occurrenceMember : occurrence ∈ ConcreteElaboration.localOccurrences
      comprehension.val.diagram comprehension.val.diagram.root)
    (sourceItem : Item signature
      (comprehension.val.exposedWires ++ comprehension.val.hiddenWires).length [])
    (sourceCompiled : ConcreteElaboration.compileOccurrenceWith? signature
      comprehension.val.diagram
      (ConcreteElaboration.compileRegion? signature comprehension.val.diagram
        comprehension.val.diagram.regionCount)
      (comprehension.val.exposedWires ++ comprehension.val.hiddenWires)
      ConcreteElaboration.BinderContext.empty occurrence = some sourceItem) :
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let layout := spliceInput.plugLayout
    let targetEq := ConcreteElaboration.WireContext.length_extend
      outputLeaf.inheritedWires (layout.frameRegion site)
    let combined := layout.siteCombinedWireEquivOfEmpty hadmissible host
      outputWitness outputLeaf hzero
    let targetEnv : Fin
        (outputLeaf.inheritedWires.length +
          (ConcreteElaboration.exactScopeWires layout.plugRaw
            (layout.frameRegion site)).length) → model.Carrier :=
      env ∘ Fin.cast targetEq.symm
    let sourceEnv := targetEnv ∘ combined
    let relationMap : RelationRenaming []
        outputWitness.toFocus.holeRels :=
      Splice.Input.PlugLayout.emptyRelationRenaming
        outputWitness.toFocus.holeRels
    denoteItem model named sourceEnv relEnv
      ((sourceItem.renameWires
        (layout.patternRootSeamPreparedWireOfEmpty hadmissible host))
          |>.renameRelations relationMap) := by
  dsimp only
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let next := advanceInstantiationState comprehension attachments binders
    payload state atom tail site arguments hadmissible
  let occurrences :=
    (ConcreteElaboration.localOccurrences next.diagram.val
      (layout.frameRegion site)).filter (dropOccurrenceSurvives next)
  have bodyRoot : payload.binderSpine.bodyContainer =
      comprehension.val.diagram.root :=
    payload.binderSpine.body_eq_root_of_empty hzero
  have bodyMember : occurrence ∈ ConcreteElaboration.localOccurrences
      comprehension.val.diagram payload.binderSpine.bodyContainer := by
    simpa [bodyRoot] using occurrenceMember
  have mappedMember : layout.mapPatternOccurrence occurrence ∈ occurrences := by
    apply (advance_site_survivor_occurrences_iff comprehension attachments
      binders payload state atom tail site arguments hadmissible
      (layout.mapPatternOccurrence occurrence)).2
    exact Or.inr ⟨occurrence, bodyMember, rfl⟩
  obtain ⟨occurrenceIndex, occurrenceIndexEq⟩ := indexOf?_complete mappedMember
  have occurrenceEq : occurrences.get occurrenceIndex =
      layout.mapPatternOccurrence occurrence :=
    indexOf?_sound occurrenceIndexEq
  let itemIndex := Fin.cast
    (ConcreteElaboration.compileOccurrencesWith?_length
      (compileSurvivorRegion? signature next outputLeaf.fuel)
      (outputLeaf.inheritedWires.extend (layout.frameRegion site))
      outputLeaf.binders survivorCompiled).symm occurrenceIndex
  have targetCompiledSurvivor :
      ConcreteElaboration.compileOccurrenceWith? signature next.diagram.val
        (compileSurvivorRegion? signature next outputLeaf.fuel)
        (outputLeaf.inheritedWires.extend (layout.frameRegion site))
        outputLeaf.binders (layout.mapPatternOccurrence occurrence) =
          some (survivorItems.get itemIndex) := by
    have atIndex := ConcreteElaboration.compileOccurrencesWith?_get
      (compileSurvivorRegion? signature next outputLeaf.fuel)
      (outputLeaf.inheritedWires.extend (layout.frameRegion site))
      outputLeaf.binders survivorCompiled occurrenceIndex
    rw [occurrenceEq] at atIndex
    exact atIndex
  have targetCompiledAuthoritative :
      ConcreteElaboration.compileOccurrenceWith? signature layout.plugRaw
        (ConcreteElaboration.compileRegion? signature layout.plugRaw
          outputLeaf.fuel)
        (outputLeaf.inheritedWires.extend (layout.frameRegion site))
        outputLeaf.binders (layout.mapPatternOccurrence occurrence) =
          some (survivorItems.get itemIndex) := by
    have compilerEq := advance_compilePatternOccurrence_eq comprehension
      attachments binders payload state atom tail site arguments hadmissible
      outputLeaf.fuel
      (outputLeaf.inheritedWires.extend (layout.frameRegion site))
      outputLeaf.binders occurrence bodyMember
    have targetInNext := compilerEq ▸ targetCompiledSurvivor
    simpa [next, layout, spliceInput] using targetInNext
  have itemIso := layout.compilePatternRootOccurrence_at_seam_iso signature
    spliceInput hadmissible host outputWitness outputLeaf hzero occurrence
    occurrenceMember sourceItem (survivorItems.get itemIndex) sourceCompiled
    targetCompiledAuthoritative
  have targetDenotes : denoteItem model named env relEnv
      (survivorItems.get itemIndex) :=
    (denoteItemSeq_iff_get model named env relEnv survivorItems).mp
      survivorDenotes itemIndex
  let targetEq := ConcreteElaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion site)
  let targetEnv : Fin
      (outputLeaf.inheritedWires.length +
        (ConcreteElaboration.exactScopeWires layout.plugRaw
          (layout.frameRegion site)).length) → model.Carrier :=
    env ∘ Fin.cast targetEq.symm
  have targetCastDenotes : denoteItem model named targetEnv relEnv
      ((survivorItems.get itemIndex).castWiresEq targetEq) := by
    rw [Item.castWiresEq_eq_renameWires, denoteItem_renameWires]
    simpa [targetEnv, targetEq, Function.comp_def] using targetDenotes
  let combined := layout.siteCombinedWireEquivOfEmpty hadmissible host
    outputWitness outputLeaf hzero
  let sourceEnv := targetEnv ∘ combined
  exact (itemIso.denotation model named sourceEnv targetEnv relEnv
    (fun _ => rfl)).mpr targetCastDenotes

/-- A denoting zero-spine next survivor block contains the entire native open
pattern root conjunction under the receipt-recorded repeated-alias valuation. -/
theorem advance_patternRootItems_denotes_empty
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
    (host : Splice.SiteView
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrame hadmissible) site)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Splice.Region.ContextPath.CompilerLeaf
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site) outputWitness)
    (hzero : payload.binderSpine.proxyCount = 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin (outputLeaf.inheritedWires.extend
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site)).length → model.Carrier)
    (relEnv : RelEnv model.Carrier outputWitness.toFocus.holeRels)
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
    (survivorDenotes : denoteItemSeq model named env relEnv survivorItems) :
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let layout := spliceInput.plugLayout
    let pattern := Splice.Input.compiledSpliceOpenRootItems comprehension
    let targetEq := ConcreteElaboration.WireContext.length_extend
      outputLeaf.inheritedWires (layout.frameRegion site)
    let combined := layout.siteCombinedWireEquivOfEmpty hadmissible host
      outputWitness outputLeaf hzero
    let targetEnv : Fin
        (outputLeaf.inheritedWires.length +
          (ConcreteElaboration.exactScopeWires layout.plugRaw
            (layout.frameRegion site)).length) → model.Carrier :=
      env ∘ Fin.cast targetEq.symm
    denoteItemSeq (relCtx := []) model named
      ((targetEnv ∘ combined) ∘
        layout.patternRootSeamPreparedWireOfEmpty hadmissible host)
      PUnit.unit pattern.items := by
  dsimp only
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let pattern := Splice.Input.compiledSpliceOpenRootItems comprehension
  let targetEq := ConcreteElaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion site)
  let combined := layout.siteCombinedWireEquivOfEmpty hadmissible host
    outputWitness outputLeaf hzero
  let targetEnv : Fin
      (outputLeaf.inheritedWires.length +
        (ConcreteElaboration.exactScopeWires layout.plugRaw
          (layout.frameRegion site)).length) → model.Carrier :=
    env ∘ Fin.cast targetEq.symm
  let sourceEnv := targetEnv ∘ combined
  let seam := layout.patternRootSeamPreparedWireOfEmpty hadmissible host
  let relationMap : RelationRenaming [] outputWitness.toFocus.holeRels :=
    Splice.Input.PlugLayout.emptyRelationRenaming
      outputWitness.toFocus.holeRels
  apply (denoteItemSeq_iff_get (relCtx := []) model named (sourceEnv ∘ seam)
    (PUnit.unit : RelEnv model.Carrier []) pattern.items).2
  intro sourceIndex
  have patternLength := ConcreteElaboration.compileOccurrencesWith?_length
    (ConcreteElaboration.compileRegion? signature comprehension.val.diagram
      comprehension.val.diagram.regionCount)
    (comprehension.val.exposedWires ++ comprehension.val.hiddenWires)
    ConcreteElaboration.BinderContext.empty pattern.computation
  let occurrenceIndex := Fin.cast patternLength sourceIndex
  let occurrence := (ConcreteElaboration.localOccurrences
    comprehension.val.diagram comprehension.val.diagram.root).get
      occurrenceIndex
  have occurrenceMember : occurrence ∈ ConcreteElaboration.localOccurrences
      comprehension.val.diagram comprehension.val.diagram.root :=
    List.get_mem _ occurrenceIndex
  have sourceCompiled := ConcreteElaboration.compileOccurrencesWith?_get
    (ConcreteElaboration.compileRegion? signature comprehension.val.diagram
      comprehension.val.diagram.regionCount)
    (comprehension.val.exposedWires ++ comprehension.val.hiddenWires)
    ConcreteElaboration.BinderContext.empty pattern.computation occurrenceIndex
  have preparedDenotes := advance_pattern_root_item_denotes_empty comprehension
    attachments binders payload state atom tail site arguments hadmissible host
    outputWitness outputLeaf hzero model named env relEnv survivorItems
    survivorCompiled survivorDenotes occurrence occurrenceMember
    (pattern.items.get sourceIndex) sourceCompiled
  change denoteItem model named sourceEnv relEnv
      (((pattern.items.get sourceIndex).renameWires seam).renameRelations
        relationMap) at preparedDenotes
  have wireRenamedDenotes :=
    (denoteItem_renameRelations model named relationMap
      (PUnit.unit : RelEnv model.Carrier []) relEnv
      (RelEnv.pullback_agrees relationMap relEnv) sourceEnv
      ((pattern.items.get sourceIndex).renameWires seam)).mp preparedDenotes
  exact (denoteItem_renameWires (relCtx := []) model named seam sourceEnv
    (PUnit.unit : RelEnv model.Carrier [])
    (pattern.items.get sourceIndex)).mp wireRenamedDenotes

end InstantiationSemantic

end VisualProof.Rule
