import VisualProof.Rule.Soundness.Comprehension.InstantiationAdvanceClean

namespace VisualProof.Rule

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
    {rels : RelCtx}
    (fuel : Nat)
    (context : ConcreteElaboration.WireContext
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val)
    (relBinders : ConcreteElaboration.BinderContext
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val rels)
    (occurrence : ConcreteElaboration.LocalOccurrence
      comprehension.val.diagram.regionCount
      comprehension.val.diagram.nodeCount)
    (member : occurrence ∈ ConcreteElaboration.localOccurrences
      comprehension.val.diagram payload.binderSpine.bodyContainer) :
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let layout := spliceInput.plugLayout
    let next := advanceInstantiationState comprehension attachments binders
      payload state atom tail site arguments hadmissible
    ConcreteElaboration.compileOccurrenceWith? signature next.diagram.val
        (compileSurvivorRegion? signature next fuel) context relBinders
        (layout.mapPatternOccurrence occurrence) =
      ConcreteElaboration.compileOccurrenceWith? signature next.diagram.val
        (ConcreteElaboration.compileRegion? signature next.diagram.val fuel)
        context relBinders (layout.mapPatternOccurrence occurrence) := by
  dsimp only
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let next := advanceInstantiationState comprehension attachments binders
    payload state atom tail site arguments hadmissible
  change ConcreteElaboration.compileOccurrenceWith? signature layout.plugRaw
      (compileSurvivorRegion? signature next fuel) context relBinders
      (layout.mapPatternOccurrence occurrence) =
    ConcreteElaboration.compileOccurrenceWith? signature layout.plugRaw
      (ConcreteElaboration.compileRegion? signature layout.plugRaw fuel)
      context relBinders (layout.mapPatternOccurrence occurrence)
  cases occurrence with
  | node node => rfl
  | child child =>
      have parent := (ConcreteElaboration.mem_localOccurrences_child
        comprehension.val.diagram payload.binderSpine.bodyContainer child).1
          member
      have material :=
        Splice.Input.PlugLayout.directChildOfBody_material spliceInput child
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
          simp only [ConcreteElaboration.compileOccurrenceWith?,
            Splice.Input.PlugLayout.mapPatternOccurrence, targetKind]
          have recurseEq : compileSurvivorRegion? signature next fuel
              (layout.bodyRegion child) context relBinders =
            ConcreteElaboration.compileRegion? signature layout.plugRaw fuel
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
          simp only [ConcreteElaboration.compileOccurrenceWith?,
            Splice.Input.PlugLayout.mapPatternOccurrence, targetKind]
          have recurseEq : compileSurvivorRegion? signature next fuel
              (layout.bodyRegion child) context
                (relBinders.push (layout.bodyRegion child) arity) =
            ConcreteElaboration.compileRegion? signature layout.plugRaw fuel
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
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Splice.Region.ContextPath.CompilerLeaf
      comprehension.val.diagram payload.binderSpine.bodyContainer
      patternWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Splice.Region.ContextPath.CompilerLeaf
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site) outputWitness)
    (hnonempty : payload.binderSpine.proxyCount ≠ 0)
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
      comprehension.val.diagram payload.binderSpine.bodyContainer)
    (sourceItem : Item signature
      (patternLeaf.inheritedWires.extend
        payload.binderSpine.bodyContainer).length
      patternWitness.toFocus.holeRels)
    (sourceCompiled : ConcreteElaboration.compileOccurrenceWith? signature
      comprehension.val.diagram
      (ConcreteElaboration.compileRegion? signature comprehension.val.diagram
        patternLeaf.fuel)
      (patternLeaf.inheritedWires.extend payload.binderSpine.bodyContainer)
      patternLeaf.binders occurrence = some sourceItem) :
    let spliceInput := instantiateSpliceInput comprehension attachments binders
      payload state site arguments
    let layout := spliceInput.plugLayout
    let targetEq := ConcreteElaboration.WireContext.length_extend
      outputLeaf.inheritedWires (layout.frameRegion site)
    let combined := layout.siteCombinedWireEquivOfNonempty hadmissible host
      outputWitness outputLeaf hnonempty
    let targetEnv : Fin
        (outputLeaf.inheritedWires.length +
          (ConcreteElaboration.exactScopeWires layout.plugRaw
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
    denoteItem model named sourceEnv relEnv
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
    (ConcreteElaboration.localOccurrences next.diagram.val
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
      outputLeaf.binders occurrence occurrenceMember
    have targetInNext := compilerEq ▸ targetCompiledSurvivor
    simpa [next, layout, spliceInput] using targetInNext
  have itemIso := layout.compilePatternOccurrence_at_seam_iso signature
    spliceInput hadmissible host patternWitness patternLeaf outputWitness
    outputLeaf hnonempty occurrence occurrenceMember sourceItem
    (survivorItems.get itemIndex) sourceCompiled targetCompiledAuthoritative
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
  let combined := layout.siteCombinedWireEquivOfNonempty hadmissible host
    outputWitness outputLeaf hnonempty
  let sourceEnv := targetEnv ∘ combined
  exact (itemIso.denotation model named sourceEnv targetEnv relEnv
    (fun _ => rfl)).mpr targetCastDenotes

/-- Sequence form of `advance_pattern_item_denotes_nonempty`: the denoting
next survivor block contains the complete native terminal-pattern conjunction
under the receipt's seam valuation and relation pullback. -/
theorem advance_terminalItems_denotes_nonempty
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
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Splice.Region.ContextPath.CompilerLeaf
      comprehension.val.diagram payload.binderSpine.bodyContainer
      patternWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Splice.Region.ContextPath.CompilerLeaf
      (advanceInstantiationState comprehension attachments binders payload
        state atom tail site arguments hadmissible).diagram.val
      ((instantiateSpliceInput comprehension attachments binders payload state
        site arguments).plugLayout.frameRegion site) outputWitness)
    (hnonempty : payload.binderSpine.proxyCount ≠ 0)
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
    let targetEq := ConcreteElaboration.WireContext.length_extend
      outputLeaf.inheritedWires (layout.frameRegion site)
    let combined := layout.siteCombinedWireEquivOfNonempty hadmissible host
      outputWitness outputLeaf hnonempty
    let targetEnv : Fin
        (outputLeaf.inheritedWires.length +
          (ConcreteElaboration.exactScopeWires layout.plugRaw
            (layout.frameRegion site)).length) → model.Carrier :=
      env ∘ Fin.cast targetEq.symm
    let relationMap : RelationRenaming patternWitness.toFocus.holeRels
        outputWitness.toFocus.holeRels := fun relation =>
      layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf
        (layout.coalescedTerminalRelationRenaming hadmissible
          host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
          hnonempty relation)
    denoteItemSeq model named
      ((targetEnv ∘ combined) ∘
        layout.patternSeamPreparedWireOfNonempty hadmissible host
          patternWitness patternLeaf hnonempty)
      (RelEnv.pullback relationMap relEnv) patternLeaf.items := by
  dsimp only
  let spliceInput := instantiateSpliceInput comprehension attachments binders
    payload state site arguments
  let layout := spliceInput.plugLayout
  let targetEq := ConcreteElaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion site)
  let combined := layout.siteCombinedWireEquivOfNonempty hadmissible host
    outputWitness outputLeaf hnonempty
  let targetEnv : Fin
      (outputLeaf.inheritedWires.length +
        (ConcreteElaboration.exactScopeWires layout.plugRaw
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
  apply (denoteItemSeq_iff_get model named (sourceEnv ∘ seam)
    (RelEnv.pullback relationMap relEnv) patternLeaf.items).2
  intro sourceIndex
  have patternLength := ConcreteElaboration.compileOccurrencesWith?_length
    (ConcreteElaboration.compileRegion? signature comprehension.val.diagram
      patternLeaf.fuel)
    (patternLeaf.inheritedWires.extend payload.binderSpine.bodyContainer)
    patternLeaf.binders patternLeaf.itemsComputation
  let occurrenceIndex := Fin.cast patternLength sourceIndex
  let occurrence := (ConcreteElaboration.localOccurrences
    comprehension.val.diagram payload.binderSpine.bodyContainer).get
      occurrenceIndex
  have occurrenceMember : occurrence ∈ ConcreteElaboration.localOccurrences
      comprehension.val.diagram payload.binderSpine.bodyContainer :=
    List.get_mem _ occurrenceIndex
  have sourceCompiled := ConcreteElaboration.compileOccurrencesWith?_get
    (ConcreteElaboration.compileRegion? signature comprehension.val.diagram
      patternLeaf.fuel)
    (patternLeaf.inheritedWires.extend payload.binderSpine.bodyContainer)
    patternLeaf.binders patternLeaf.itemsComputation occurrenceIndex
  have preparedDenotes := advance_pattern_item_denotes_nonempty comprehension
    attachments binders payload state atom tail site arguments hadmissible host
    patternWitness patternLeaf outputWitness outputLeaf hnonempty model named env
    relEnv survivorItems survivorCompiled survivorDenotes occurrence
    occurrenceMember (patternLeaf.items.get sourceIndex) sourceCompiled
  change denoteItem model named sourceEnv relEnv
      (((patternLeaf.items.get sourceIndex).renameWires seam).renameRelations
        relationMap) at preparedDenotes
  have wireRenamedDenotes :=
    (denoteItem_renameRelations model named relationMap
      (RelEnv.pullback relationMap relEnv) relEnv
      (RelEnv.pullback_agrees relationMap relEnv) sourceEnv
      ((patternLeaf.items.get sourceIndex).renameWires seam)).mp preparedDenotes
  exact (denoteItem_renameWires model named seam sourceEnv
    (RelEnv.pullback relationMap relEnv)
    (patternLeaf.items.get sourceIndex)).mp wireRenamedDenotes

end InstantiationSemantic

end VisualProof.Rule
