import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvancePatternCompiler

namespace VisualProof.Rule

open VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- Zero-spine counterpart of `advance_pattern_item_denotes_nonempty`.  The
source item is compiled at the checked-open sheet root, while the target item
is located in the executor's actual survivor occurrence list. -/
theorem advance_pattern_root_item_denotes_empty
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
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (host : Concrete.Splice.SiteView
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrame hadmissible) site)
    {outputBody : Region  outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site) outputWitness)
    (hzero : payload.binderSpine.proxyCount = 0)
    (model : Model)
    (env : Fin (outputLeaf.inheritedWires.extend
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site)).length → model.Carrier)
    (relEnv : RelEnv model.Carrier outputWitness.toFocus.holeRels)
    (survivorItems : ItemSeq
      (outputLeaf.inheritedWires.extend
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion site)).length
      outputWitness.toFocus.holeRels)
    (survivorCompiled : Concrete.Elaboration.compileOccurrencesWith?
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val
      (compileSurvivorRegion?
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible) outputLeaf.fuel)
      (outputLeaf.inheritedWires.extend
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion site))
      outputLeaf.binders
      ((Concrete.Elaboration.localOccurrences
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible).diagram.val
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion site)).filter
        (dropOccurrenceSurvives
          (advanceInstantiationState comprehension attachments binders payload
            state atom tail site arguments hadmissible))) = some survivorItems)
    (survivorDenotes : denoteItemSeq model  env relEnv survivorItems)
    (occurrence : Concrete.Elaboration.LocalOccurrence
      comprehension.val.diagram.regionCount comprehension.val.diagram.nodeCount)
    (occurrenceMember : occurrence ∈ Concrete.Elaboration.localOccurrences
      comprehension.val.diagram comprehension.val.diagram.root)
    (sourceItem : Item
      (comprehension.val.exposedWires ++ comprehension.val.hiddenWires).length [])
    (sourceCompiled : Concrete.Elaboration.compileOccurrenceWith?
      comprehension.val.diagram
      (Concrete.Elaboration.compileRegion?  comprehension.val.diagram
        comprehension.val.diagram.regionCount)
      (comprehension.val.exposedWires ++ comprehension.val.hiddenWires)
      Concrete.Elaboration.BinderContext.empty occurrence = some sourceItem) :
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let layout := spliceInput.plugLayout
    let targetEq := Concrete.Elaboration.WireContext.length_extend
      outputLeaf.inheritedWires (layout.frameRegion site)
    let combined := layout.siteCombinedWireEquivOfEmpty hadmissible host
      outputWitness outputLeaf hzero
    let targetEnv : Fin
        (outputLeaf.inheritedWires.length +
          (Concrete.Elaboration.exactScopeWires layout.plugRaw
            (layout.frameRegion site)).length) → model.Carrier :=
      env ∘ Fin.cast targetEq.symm
    let sourceEnv := targetEnv ∘ combined
    let relationMap : RelationRenaming []
        outputWitness.toFocus.holeRels :=
      Concrete.Splice.Input.PlugLayout.emptyRelationRenaming
        outputWitness.toFocus.holeRels
    denoteItem model  sourceEnv relEnv
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
    (Concrete.Elaboration.localOccurrences next.diagram.val
      (layout.frameRegion site)).filter (dropOccurrenceSurvives next)
  have bodyRoot : payload.binderSpine.bodyContainer =
      comprehension.val.diagram.root :=
    payload.binderSpine.body_eq_root_of_empty hzero
  have bodyMember : occurrence ∈ Concrete.Elaboration.localOccurrences
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
    (Concrete.Elaboration.compileOccurrencesWith?_length
      (compileSurvivorRegion?  next outputLeaf.fuel)
      (outputLeaf.inheritedWires.extend (layout.frameRegion site))
      outputLeaf.binders survivorCompiled).symm occurrenceIndex
  have targetCompiledSurvivor :
      Concrete.Elaboration.compileOccurrenceWith?  next.diagram.val
        (compileSurvivorRegion?  next outputLeaf.fuel)
        (outputLeaf.inheritedWires.extend (layout.frameRegion site))
        outputLeaf.binders (layout.mapPatternOccurrence occurrence) =
          some (survivorItems.get itemIndex) := by
    have atIndex := Concrete.Elaboration.compileOccurrencesWith?_get
      (compileSurvivorRegion?  next outputLeaf.fuel)
      (outputLeaf.inheritedWires.extend (layout.frameRegion site))
      outputLeaf.binders survivorCompiled occurrenceIndex
    rw [occurrenceEq] at atIndex
    exact atIndex
  have targetCompiledAuthoritative :
      Concrete.Elaboration.compileOccurrenceWith?  layout.plugRaw
        (Concrete.Elaboration.compileRegion?  layout.plugRaw
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
  have itemIso := layout.compilePatternRootOccurrence_at_seam_iso
    spliceInput hadmissible host outputWitness outputLeaf hzero occurrence
    occurrenceMember sourceItem (survivorItems.get itemIndex) sourceCompiled
    targetCompiledAuthoritative
  have targetDenotes : denoteItem model  env relEnv
      (survivorItems.get itemIndex) :=
    (denoteItemSeq_iff_get model  env relEnv survivorItems).mp
      survivorDenotes itemIndex
  let targetEq := Concrete.Elaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion site)
  let targetEnv : Fin
      (outputLeaf.inheritedWires.length +
        (Concrete.Elaboration.exactScopeWires layout.plugRaw
          (layout.frameRegion site)).length) → model.Carrier :=
    env ∘ Fin.cast targetEq.symm
  have targetCastDenotes : denoteItem model  targetEnv relEnv
      ((survivorItems.get itemIndex).castWiresEq targetEq) := by
    rw [Item.castWiresEq_eq_renameWires, denoteItem_renameWires]
    simpa [targetEnv, targetEq, Function.comp_def] using targetDenotes
  let combined := layout.siteCombinedWireEquivOfEmpty hadmissible host
    outputWitness outputLeaf hzero
  let sourceEnv := targetEnv ∘ combined
  exact (itemIso.denotation model  sourceEnv targetEnv relEnv
    (fun _ => rfl)).mpr targetCastDenotes

/-- A denoting zero-spine next survivor block contains the entire native open
pattern root conjunction under the receipt-recorded repeated-alias valuation. -/
theorem advance_patternRootItems_denotes_empty
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
    (hadmissible : (instantiateSpliceInput comprehension attachments binders
      payload state site arguments).Admissible)
    (host : Concrete.Splice.SiteView
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).coalesceFrame hadmissible) site)
    {outputBody : Region  outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site) outputWitness)
    (hzero : payload.binderSpine.proxyCount = 0)
    (model : Model)
    (env : Fin (outputLeaf.inheritedWires.extend
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site)).length → model.Carrier)
    (relEnv : RelEnv model.Carrier outputWitness.toFocus.holeRels)
    (survivorItems : ItemSeq
      (outputLeaf.inheritedWires.extend
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion site)).length
      outputWitness.toFocus.holeRels)
    (survivorCompiled : Concrete.Elaboration.compileOccurrencesWith?
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val
      (compileSurvivorRegion?
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible) outputLeaf.fuel)
      (outputLeaf.inheritedWires.extend
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion site))
      outputLeaf.binders
      ((Concrete.Elaboration.localOccurrences
        (advanceInstantiationState comprehension attachments binders payload
          state atom tail site arguments hadmissible).diagram.val
        ((instantiateSpliceInput comprehension attachments binders payload state
          site arguments).plugLayout.frameRegion site)).filter
        (dropOccurrenceSurvives
          (advanceInstantiationState comprehension attachments binders payload
            state atom tail site arguments hadmissible))) = some survivorItems)
    (survivorDenotes : denoteItemSeq model  env relEnv survivorItems) :
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let layout := spliceInput.plugLayout
    let pattern := Concrete.Splice.Input.compiledSpliceOpenRootItems comprehension
    let targetEq := Concrete.Elaboration.WireContext.length_extend
      outputLeaf.inheritedWires (layout.frameRegion site)
    let combined := layout.siteCombinedWireEquivOfEmpty hadmissible host
      outputWitness outputLeaf hzero
    let targetEnv : Fin
        (outputLeaf.inheritedWires.length +
          (Concrete.Elaboration.exactScopeWires layout.plugRaw
            (layout.frameRegion site)).length) → model.Carrier :=
      env ∘ Fin.cast targetEq.symm
    denoteItemSeq (relCtx := []) model
      ((targetEnv ∘ combined) ∘
        layout.patternRootSeamPreparedWireOfEmpty hadmissible host)
      PUnit.unit pattern.items := by
  dsimp only
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let pattern := Concrete.Splice.Input.compiledSpliceOpenRootItems comprehension
  let targetEq := Concrete.Elaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion site)
  let combined := layout.siteCombinedWireEquivOfEmpty hadmissible host
    outputWitness outputLeaf hzero
  let targetEnv : Fin
      (outputLeaf.inheritedWires.length +
        (Concrete.Elaboration.exactScopeWires layout.plugRaw
          (layout.frameRegion site)).length) → model.Carrier :=
    env ∘ Fin.cast targetEq.symm
  let sourceEnv := targetEnv ∘ combined
  let seam := layout.patternRootSeamPreparedWireOfEmpty hadmissible host
  let relationMap : RelationRenaming [] outputWitness.toFocus.holeRels :=
    Concrete.Splice.Input.PlugLayout.emptyRelationRenaming
      outputWitness.toFocus.holeRels
  apply (denoteItemSeq_iff_get (relCtx := []) model  (sourceEnv ∘ seam)
    (PUnit.unit : RelEnv model.Carrier []) pattern.items).2
  intro sourceIndex
  have patternLength := Concrete.Elaboration.compileOccurrencesWith?_length
    (Concrete.Elaboration.compileRegion?  comprehension.val.diagram
      comprehension.val.diagram.regionCount)
    (comprehension.val.exposedWires ++ comprehension.val.hiddenWires)
    Concrete.Elaboration.BinderContext.empty pattern.computation
  let occurrenceIndex := Fin.cast patternLength sourceIndex
  let occurrence := (Concrete.Elaboration.localOccurrences
    comprehension.val.diagram comprehension.val.diagram.root).get
      occurrenceIndex
  have occurrenceMember : occurrence ∈ Concrete.Elaboration.localOccurrences
      comprehension.val.diagram comprehension.val.diagram.root :=
    List.get_mem _ occurrenceIndex
  have sourceCompiled := Concrete.Elaboration.compileOccurrencesWith?_get
    (Concrete.Elaboration.compileRegion?  comprehension.val.diagram
      comprehension.val.diagram.regionCount)
    (comprehension.val.exposedWires ++ comprehension.val.hiddenWires)
    Concrete.Elaboration.BinderContext.empty pattern.computation occurrenceIndex
  have preparedDenotes := advance_pattern_root_item_denotes_empty comprehension
    attachments binders payload state atom tail site arguments hadmissible host
    outputWitness outputLeaf hzero model  env relEnv survivorItems
    survivorCompiled survivorDenotes occurrence occurrenceMember
    (pattern.items.get sourceIndex) sourceCompiled
  change denoteItem model  sourceEnv relEnv
      (((pattern.items.get sourceIndex).renameWires seam).renameRelations
        relationMap) at preparedDenotes
  have wireRenamedDenotes :=
    (denoteItem_renameRelations model  relationMap
      (PUnit.unit : RelEnv model.Carrier []) relEnv
      (RelEnv.pullback_agrees relationMap relEnv) sourceEnv
      ((pattern.items.get sourceIndex).renameWires seam)).mp preparedDenotes
  exact (denoteItem_renameWires (relCtx := []) model  seam sourceEnv
    (PUnit.unit : RelEnv model.Carrier [])
    (pattern.items.get sourceIndex)).mp wireRenamedDenotes

end InstantiationSemantic

end VisualProof.Rule
