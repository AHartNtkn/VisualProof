import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvanceClean

namespace VisualProof.Rule

open VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

namespace InstantiationSemantic

/-- Pattern occurrences inserted by one executor step compile identically
with the next survivor recursion and with the authoritative recursion.  Nodes
do not recurse; direct children of the body container are retained material,
where the two recursive compilers coincide. -/
theorem advance_compilePatternOccurrence_eq
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
    {rels : RelCtx}
    (fuel : Nat)
    (context : Concrete.Elaboration.WireContext
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val)
    (relBinders : Concrete.Elaboration.BinderContext
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val rels)
    (occurrence : Concrete.Elaboration.LocalOccurrence
      comprehension.val.diagram.regionCount
      comprehension.val.diagram.nodeCount)
    (member : occurrence ∈ Concrete.Elaboration.localOccurrences
      comprehension.val.diagram payload.binderSpine.bodyContainer) :
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let layout := spliceInput.plugLayout
    let next := advanceInstantiationState comprehension attachments binders
      payload state atom tail site arguments hadmissible
    Concrete.Elaboration.compileOccurrenceWith?  next.diagram.val
        (compileSurvivorRegion?  next fuel) context relBinders
        (layout.mapPatternOccurrence occurrence) =
      Concrete.Elaboration.compileOccurrenceWith?  next.diagram.val
        (Concrete.Elaboration.compileRegion?  next.diagram.val fuel)
        context relBinders (layout.mapPatternOccurrence occurrence) := by
  dsimp only
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let next := advanceInstantiationState comprehension attachments binders
    payload state atom tail site arguments hadmissible
  change Concrete.Elaboration.compileOccurrenceWith?  layout.plugRaw
      (compileSurvivorRegion?  next fuel) context relBinders
      (layout.mapPatternOccurrence occurrence) =
    Concrete.Elaboration.compileOccurrenceWith?  layout.plugRaw
      (Concrete.Elaboration.compileRegion?  layout.plugRaw fuel)
      context relBinders (layout.mapPatternOccurrence occurrence)
  cases occurrence with
  | node node => rfl
  | child child =>
      have parent := (Concrete.Elaboration.mem_localOccurrences_child
        comprehension.val.diagram payload.binderSpine.bodyContainer child).1
          member
      have material :=
        Concrete.Splice.Input.PlugLayout.directChildOfBody_material spliceInput child
          parent
      cases childKind : comprehension.val.diagram.regions child with
      | sheet =>
          have childRoot :=
            comprehension.property.diagram_well_formed.only_root_is_sheet
              child childKind
          subst child
          rw [comprehension.property.diagram_well_formed.root_is_sheet]
            at parent
          simp [CRegion.parent?] at parent
      | cut sourceParent =>
          have targetKind := layout.plugRaw_bodyRegion_cut child sourceParent
            material childKind
          simp only [Concrete.Elaboration.compileOccurrenceWith?,
            Concrete.Splice.Input.PlugLayout.mapPatternOccurrence, targetKind]
          have recurseEq : compileSurvivorRegion?  next fuel
              (layout.bodyRegion child) context relBinders =
            Concrete.Elaboration.compileRegion?  layout.plugRaw fuel
              (layout.bodyRegion child) context relBinders := by
            simpa [next, layout, spliceInput] using
              (advance_compileSurvivorRegion_eq_material comprehension
                attachments binders payload state atom tail site arguments
                hadmissible fuel child material context relBinders)
          exact congrArg (fun result => result.bind fun body =>
            some (Item.cut body)) recurseEq
      | bubble sourceParent arity =>
          have targetKind := layout.plugRaw_bodyRegion_bubble child sourceParent
            arity material childKind
          simp only [Concrete.Elaboration.compileOccurrenceWith?,
            Concrete.Splice.Input.PlugLayout.mapPatternOccurrence, targetKind]
          have recurseEq : compileSurvivorRegion?  next fuel
              (layout.bodyRegion child) context
                (relBinders.push (layout.bodyRegion child) arity) =
            Concrete.Elaboration.compileRegion?  layout.plugRaw fuel
              (layout.bodyRegion child) context
                (relBinders.push (layout.bodyRegion child) arity) := by
            simpa [next, layout, spliceInput] using
              (advance_compileSurvivorRegion_eq_material comprehension
                attachments binders payload state atom tail site arguments
                hadmissible fuel child material context
                (relBinders.push (layout.bodyRegion child) arity))
          exact congrArg (fun result => result.bind fun body =>
            some (Item.bubble arity body)) recurseEq

/-- A denoting next-state survivor conjunction entails every prepared item of
the inserted terminal pattern.  The item is located through the executor's
actual filtered occurrence list, then transported by the authoritative seam
isomorphism. -/
theorem advance_pattern_item_denotes_nonempty
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
    {patternBody : Region  patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf
      comprehension.val.diagram payload.binderSpine.bodyContainer
      patternWitness)
    {outputBody : Region  outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site) outputWitness)
    (hnonempty : payload.binderSpine.proxyCount ≠ 0)
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
      comprehension.val.diagram payload.binderSpine.bodyContainer)
    (sourceItem : Item
      (patternLeaf.inheritedWires.extend
        payload.binderSpine.bodyContainer).length
      patternWitness.toFocus.holeRels)
    (sourceCompiled : Concrete.Elaboration.compileOccurrenceWith?
      comprehension.val.diagram
      (Concrete.Elaboration.compileRegion?  comprehension.val.diagram
        patternLeaf.fuel)
      (patternLeaf.inheritedWires.extend payload.binderSpine.bodyContainer)
      patternLeaf.binders occurrence = some sourceItem) :
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let layout := spliceInput.plugLayout
    let targetEq := Concrete.Elaboration.WireContext.length_extend
      outputLeaf.inheritedWires (layout.frameRegion site)
    let combined := layout.siteCombinedWireEquivOfNonempty hadmissible host
      outputWitness outputLeaf hnonempty
    let targetEnv : Fin
        (outputLeaf.inheritedWires.length +
          (Concrete.Elaboration.exactScopeWires layout.plugRaw
            (layout.frameRegion site)).length) → model.Carrier :=
      env ∘ Fin.cast targetEq.symm
    let sourceEnv := targetEnv ∘ combined
    let relationMap : RelationRenaming patternWitness.toFocus.holeRels
        outputWitness.toFocus.holeRels := fun relation =>
      layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf
        (layout.coalescedTerminalRelationRenaming hadmissible
          host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
          hnonempty relation)
    denoteItem model  sourceEnv relEnv
      ((sourceItem.renameWires
        (layout.patternSeamPreparedWireOfNonempty hadmissible host
          patternWitness patternLeaf hnonempty)).renameRelations relationMap) := by
  dsimp only
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let next := advanceInstantiationState comprehension attachments binders
    payload state atom tail site arguments hadmissible
  let occurrences :=
    (Concrete.Elaboration.localOccurrences next.diagram.val
      (layout.frameRegion site)).filter (dropOccurrenceSurvives next)
  have mappedMember : layout.mapPatternOccurrence occurrence ∈ occurrences := by
    apply (advance_site_survivor_occurrences_iff comprehension attachments
      binders payload state atom tail site arguments hadmissible
      (layout.mapPatternOccurrence occurrence)).2
    exact Or.inr ⟨occurrence, occurrenceMember, rfl⟩
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
      outputLeaf.binders occurrence occurrenceMember
    have targetInNext := compilerEq ▸ targetCompiledSurvivor
    simpa [next, layout, spliceInput] using targetInNext
  have itemIso := layout.compilePatternOccurrence_at_seam_iso
    spliceInput hadmissible host patternWitness patternLeaf outputWitness
    outputLeaf hnonempty occurrence occurrenceMember sourceItem
    (survivorItems.get itemIndex) sourceCompiled targetCompiledAuthoritative
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
  let combined := layout.siteCombinedWireEquivOfNonempty hadmissible host
    outputWitness outputLeaf hnonempty
  let sourceEnv := targetEnv ∘ combined
  exact (itemIso.denotation model  sourceEnv targetEnv relEnv
    (fun _ => rfl)).mpr targetCastDenotes

/-- Sequence form of `advance_pattern_item_denotes_nonempty`: the denoting
next survivor block contains the complete native terminal-pattern conjunction
under the receipt's seam valuation and relation pullback. -/
theorem advance_terminalItems_denotes_nonempty
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
    {patternBody : Region  patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf
      comprehension.val.diagram payload.binderSpine.bodyContainer
      patternWitness)
    {outputBody : Region  outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Concrete.Splice.Region.ContextPath.CompilerLeaf
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site) outputWitness)
    (hnonempty : payload.binderSpine.proxyCount ≠ 0)
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
    let targetEq := Concrete.Elaboration.WireContext.length_extend
      outputLeaf.inheritedWires (layout.frameRegion site)
    let combined := layout.siteCombinedWireEquivOfNonempty hadmissible host
      outputWitness outputLeaf hnonempty
    let targetEnv : Fin
        (outputLeaf.inheritedWires.length +
          (Concrete.Elaboration.exactScopeWires layout.plugRaw
            (layout.frameRegion site)).length) → model.Carrier :=
      env ∘ Fin.cast targetEq.symm
    let relationMap : RelationRenaming patternWitness.toFocus.holeRels
        outputWitness.toFocus.holeRels := fun relation =>
      layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf
        (layout.coalescedTerminalRelationRenaming hadmissible
          host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
          hnonempty relation)
    denoteItemSeq model
      ((targetEnv ∘ combined) ∘
        layout.patternSeamPreparedWireOfNonempty hadmissible host
          patternWitness patternLeaf hnonempty)
      (RelEnv.pullback relationMap relEnv) patternLeaf.items := by
  dsimp only
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let targetEq := Concrete.Elaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion site)
  let combined := layout.siteCombinedWireEquivOfNonempty hadmissible host
    outputWitness outputLeaf hnonempty
  let targetEnv : Fin
      (outputLeaf.inheritedWires.length +
        (Concrete.Elaboration.exactScopeWires layout.plugRaw
          (layout.frameRegion site)).length) → model.Carrier :=
    env ∘ Fin.cast targetEq.symm
  let sourceEnv := targetEnv ∘ combined
  let seam := layout.patternSeamPreparedWireOfNonempty hadmissible host
    patternWitness patternLeaf hnonempty
  let relationMap : RelationRenaming patternWitness.toFocus.holeRels
      outputWitness.toFocus.holeRels := fun relation =>
    layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
      outputWitness outputLeaf
      (layout.coalescedTerminalRelationRenaming hadmissible
        host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
        hnonempty relation)
  apply (denoteItemSeq_iff_get model  (sourceEnv ∘ seam)
    (RelEnv.pullback relationMap relEnv) patternLeaf.items).2
  intro sourceIndex
  have patternLength := Concrete.Elaboration.compileOccurrencesWith?_length
    (Concrete.Elaboration.compileRegion?  comprehension.val.diagram
      patternLeaf.fuel)
    (patternLeaf.inheritedWires.extend payload.binderSpine.bodyContainer)
    patternLeaf.binders patternLeaf.itemsComputation
  let occurrenceIndex := Fin.cast patternLength sourceIndex
  let occurrence := (Concrete.Elaboration.localOccurrences
    comprehension.val.diagram payload.binderSpine.bodyContainer).get
      occurrenceIndex
  have occurrenceMember : occurrence ∈ Concrete.Elaboration.localOccurrences
      comprehension.val.diagram payload.binderSpine.bodyContainer :=
    List.get_mem _ occurrenceIndex
  have sourceCompiled := Concrete.Elaboration.compileOccurrencesWith?_get
    (Concrete.Elaboration.compileRegion?  comprehension.val.diagram
      patternLeaf.fuel)
    (patternLeaf.inheritedWires.extend payload.binderSpine.bodyContainer)
    patternLeaf.binders patternLeaf.itemsComputation occurrenceIndex
  have preparedDenotes := advance_pattern_item_denotes_nonempty comprehension
    attachments binders payload state atom tail site arguments hadmissible host
    patternWitness patternLeaf outputWitness outputLeaf hnonempty model  env
    relEnv survivorItems survivorCompiled survivorDenotes occurrence
    occurrenceMember (patternLeaf.items.get sourceIndex) sourceCompiled
  change denoteItem model  sourceEnv relEnv
      (((patternLeaf.items.get sourceIndex).renameWires seam).renameRelations
        relationMap) at preparedDenotes
  have wireRenamedDenotes :=
    (denoteItem_renameRelations model  relationMap
      (RelEnv.pullback relationMap relEnv) relEnv
      (RelEnv.pullback_agrees relationMap relEnv) sourceEnv
      ((patternLeaf.items.get sourceIndex).renameWires seam)).mp preparedDenotes
  exact (denoteItem_renameWires model  seam sourceEnv
    (RelEnv.pullback relationMap relEnv)
    (patternLeaf.items.get sourceIndex)).mp wireRenamedDenotes

end InstantiationSemantic

end VisualProof.Rule
