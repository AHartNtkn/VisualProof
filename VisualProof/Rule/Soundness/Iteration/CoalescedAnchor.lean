import VisualProof.Rule.Soundness.Iteration.DiscreteQuotient
import VisualProof.Rule.Soundness.Iteration.SelectionPartition
import VisualProof.Rule.Soundness.Iteration.ExtractionTerminalSemantic

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Rule.ModalSoundness

/-- Canonical compiler evidence at the selection anchor inside the coalesced
frame.  This is distinct from the splice-site view when iteration copies an
ancestor occurrence into a proper descendant. -/
noncomputable def iterationCoalescedAnchorView
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible) :
    Splice.SiteView
      ((iterationInput input selection target).coalesceFrame hadmissible)
      selection.val.anchor :=
  Classical.choice (Splice.siteView_complete
    ((iterationInput input selection target).coalesceFrame hadmissible)
    selection.val.anchor)

/-- The selected compiler block at the canonical coalesced splice site is
isomorphic to a compiler block over the original diagram at the same anchor.
The target context is exactly the pointwise image of the authoritative splice
context, so the theorem retains every lexical wire value. -/
theorem coalescedAnchorSelected_iso
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible) :
    let spliceInput := iterationInput input selection target
    let anchorView := iterationCoalescedAnchorView input selection target
      hadmissible
    let sourceLeaf := anchorView.compilerLeaf
    let sourceContext := sourceLeaf.inheritedWires.extend selection.val.anchor
    let iso := iterationCoalescedFrameIso input selection target
    let targetContext := sourceContext.map iso.wires
    let targetBinders : ConcreteElaboration.BinderContext input.val
        anchorView.focus.holeRels := fun binder => sourceLeaf.binders binder
    let wireEquiv : FiniteEquiv (Fin sourceContext.length)
        (Fin targetContext.length) :=
      FiniteEquiv.finCast (List.length_map iso.wires).symm
    ∃ (sourceItems : ItemSeq signature sourceContext.length
        anchorView.focus.holeRels)
      (targetItems : ItemSeq signature targetContext.length
        anchorView.focus.holeRels)
      (targetFuel : Nat),
      ConcreteElaboration.compileOccurrencesWith? signature
          spliceInput.coalesceFrameRaw
          (ConcreteElaboration.compileRegion? signature
            spliceInput.coalesceFrameRaw sourceLeaf.fuel)
          sourceContext sourceLeaf.binders
          (selectedOccurrences input.val selection) = some sourceItems ∧
        ConcreteElaboration.compileOccurrencesWith? signature input.val
          (ConcreteElaboration.compileRegion? signature input.val targetFuel)
          targetContext targetBinders
          (selectedOccurrences input.val selection) = some targetItems ∧
        ItemSeqIso signature wireEquiv anchorView.focus.holeRels
          sourceItems targetItems := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let anchorView := iterationCoalescedAnchorView input selection target
    hadmissible
  let sourceLeaf := anchorView.compilerLeaf
  let sourceContext := sourceLeaf.inheritedWires.extend selection.val.anchor
  let iso := iterationCoalescedFrameIso input selection target
  let targetContext := sourceContext.map iso.wires
  let targetBinders : ConcreteElaboration.BinderContext input.val
      anchorView.focus.holeRels := fun binder => sourceLeaf.binders binder
  let wireEquiv : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length) :=
    FiniteEquiv.finCast (List.length_map iso.wires).symm
  let hereLeaf :=
    Splice.Region.ContextPath.CompilerLeaf.hereOfItemsComputation
      spliceInput.coalesceFrameRaw selection.val.anchor sourceLeaf.inheritedWires
      sourceLeaf.binders sourceLeaf.fuel sourceLeaf.items
      sourceLeaf.itemsComputation sourceLeaf.wiresExact
      sourceLeaf.bindersCover sourceLeaf.binderEnumeration
  have partition :
      (keptOccurrences input.val selection ++
          selectedOccurrences input.val selection).Perm
        (ConcreteElaboration.localOccurrences spliceInput.coalesceFrameRaw
          selection.val.anchor) := by
    change (keptOccurrences input.val selection ++
      selectedOccurrences input.val selection).Perm
        (ConcreteElaboration.localOccurrences input.val selection.val.anchor)
    exact anchorOccurrences_perm_partition input.val selection
  obtain ⟨keptItems, sourceItems, keptCompiled, sourceCompiled,
      sourceDenotation⟩ :=
    compilerLeaf_partition_of_perm
      (spliceInput.coalesceFrame hadmissible) selection.val.anchor hereLeaf
      (keptOccurrences input.val selection)
      (selectedOccurrences input.val selection) partition
  obtain ⟨steps, hsteps⟩ :=
    input.property.all_regions_reach_root selection.val.anchor
  let targetFuel := input.val.regionCount - steps.val
  have targetFuelEnough : steps.val + 1 + targetFuel =
      input.val.regionCount + 1 := by
    dsimp only [targetFuel]
    omega
  have targetExact : ConcreteElaboration.WireContext.Exact targetContext
      selection.val.anchor := by
    exact sourceLeaf.wiresExact.mapIso iso
  have targetCovers :
      targetBinders.Covers selection.val.anchor := by
    intro binder parent arity hbubble hencloses
    apply sourceLeaf.bindersCover binder parent arity
    · simpa only [spliceInput,
        Splice.Input.coalesceFrameRaw_regions] using hbubble
    · exact (spliceInput.coalesceFrameRaw_encloses_iff binder
        selection.val.anchor).2
        hencloses
  have targetLocal : ∀ occurrence,
      occurrence ∈ selectedOccurrences input.val selection →
      occurrence ∈ ConcreteElaboration.localOccurrences input.val
        selection.val.anchor := by
    intro occurrence member
    rw [selectedOccurrences, List.mem_filter] at member
    exact member.1
  obtain ⟨targetItems, targetCompiled⟩ :=
    ConcreteElaboration.compileDirectOccurrences?_complete input.property
      hsteps targetFuelEnough targetExact targetCovers
      (selectedOccurrences input.val selection) targetLocal
  have sourceLocal : ∀ occurrence,
      occurrence ∈ selectedOccurrences input.val selection →
      occurrence ∈ ConcreteElaboration.localOccurrences
        spliceInput.coalesceFrameRaw selection.val.anchor := by
    intro occurrence member
    have original := targetLocal occurrence member
    simpa only [spliceInput, Splice.Input.coalesceFrameRaw_regions,
      Splice.Input.coalesceFrameRaw_nodes] using original
  have wireAgreement : ConcreteElaboration.WireContextsAgree iso
      sourceContext targetContext wireEquiv := by
    intro index
    simp only [targetContext, wireEquiv, List.get_eq_getElem,
      List.getElem_map]
    rfl
  have binderAgreement : ConcreteElaboration.BinderContextsAgree iso
      sourceLeaf.binders targetBinders := by
    intro binder
    rfl
  have renamedSelected :
      (selectedOccurrences input.val selection).map
          (ConcreteElaboration.renameOccurrence iso) =
        selectedOccurrences input.val selection := by
    induction selectedOccurrences input.val selection with
    | nil => rfl
    | cons occurrence tail induction =>
        cases occurrence with
        | node node =>
            change ConcreteElaboration.LocalOccurrence.node (iso.nodes node) ::
                tail.map (ConcreteElaboration.renameOccurrence iso) =
              ConcreteElaboration.LocalOccurrence.node node :: tail
            rw [show iso.nodes node = node by rfl, induction]
        | child child =>
            change ConcreteElaboration.LocalOccurrence.child
                  (iso.regions child) ::
                tail.map (ConcreteElaboration.renameOccurrence iso) =
              ConcreteElaboration.LocalOccurrence.child child :: tail
            rw [show iso.regions child = child by rfl, induction]
  have targetCompiledRenamed :
      ConcreteElaboration.compileOccurrencesWith? signature input.val
          (ConcreteElaboration.compileRegion? signature input.val targetFuel)
          targetContext targetBinders
          ((selectedOccurrences input.val selection).map
            (ConcreteElaboration.renameOccurrence iso)) = some targetItems := by
    rwa [renamedSelected]
  have selectedIso :=
    ConcreteElaboration.compileOccurrencesWith?_equivariant iso input.property
      wireAgreement targetExact binderAgreement
      (selectedOccurrences input.val selection) sourceLocal sourceCompiled
      targetCompiledRenamed
  exact ⟨sourceItems, targetItems, targetFuel, sourceCompiled,
    targetCompiled, selectedIso⟩

/-- The selected coalesced anchor block semantically supplies the extracted
terminal material.  The statement exposes exactly the environment relation
needed later to identify extraction's lexical coordinates with the splice
wire and binder maps. -/
theorem coalescedAnchorSelected_entails_terminal
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0) :
    let spliceInput := iterationInput input selection target
    let layout : FragmentLayout input.val selection := {}
    let anchorView := iterationCoalescedAnchorView input selection target
      hadmissible
    let sourceLeaf := anchorView.compilerLeaf
    let sourceContext := sourceLeaf.inheritedWires.extend selection.val.anchor
    let iso := iterationCoalescedFrameIso input selection target
    let targetContext := sourceContext.map iso.wires
    let targetBinders : ConcreteElaboration.BinderContext input.val
        anchorView.focus.holeRels := fun binder => sourceLeaf.binders binder
    let wireEquiv : FiniteEquiv (Fin sourceContext.length)
        (Fin targetContext.length) :=
      FiniteEquiv.finCast (List.length_map iso.wires).symm
    let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
    let targetCover : targetBinders.Covers selection.val.anchor :=
      sourceLeaf.bindersCover.mapIso iso (by intro binder; rfl)
    let binderWitness := ExtractionBinderWitness.terminal input selection layout
      pattern.leaf.binders pattern.leaf.binderEnumeration targetBinders
      targetCover
    ∃ sourceItems : ItemSeq signature sourceContext.length
        anchorView.focus.holeRels,
      ConcreteElaboration.compileOccurrencesWith? signature
          spliceInput.coalesceFrameRaw
          (ConcreteElaboration.compileRegion? signature
            spliceInput.coalesceFrameRaw sourceLeaf.fuel)
          sourceContext sourceLeaf.binders
          (selectedOccurrences input.val selection) = some sourceItems ∧
      ∀ (model : Lambda.LambdaModel)
        (named : NamedEnv model.Carrier signature)
        (sourceEnv : Fin sourceContext.length → model.Carrier)
        (relEnv : RelEnv model.Carrier anchorView.focus.holeRels)
        (fragmentEnv : Fin pattern.leaf.inheritedWires.length → model.Carrier),
        (extractionContextRelation input selection layout
          pattern.leaf.inheritedWires targetContext).EnvironmentsAgree
            fragmentEnv (fun index => sourceEnv (wireEquiv.symm index)) →
        denoteItemSeq model named sourceEnv relEnv sourceItems →
        denoteRegion model named fragmentEnv relEnv
          ((ConcreteElaboration.finishRegion
              (input.val.extractDiagramRaw selection layout)
              pattern.leaf.inheritedWires layout.bodyContainer
              pattern.leaf.items).renameRelations
            binderWitness.relationMap) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let layout : FragmentLayout input.val selection := {}
  let anchorView := iterationCoalescedAnchorView input selection target
    hadmissible
  let sourceLeaf := anchorView.compilerLeaf
  let sourceContext := sourceLeaf.inheritedWires.extend selection.val.anchor
  let iso := iterationCoalescedFrameIso input selection target
  let targetContext := sourceContext.map iso.wires
  let targetBinders : ConcreteElaboration.BinderContext input.val
      anchorView.focus.holeRels := fun binder => sourceLeaf.binders binder
  let wireEquiv : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length) :=
    FiniteEquiv.finCast (List.length_map iso.wires).symm
  let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
  have binderAgreement : ConcreteElaboration.BinderContextsAgree iso
      sourceLeaf.binders targetBinders := by
    intro binder
    rfl
  let targetCover : targetBinders.Covers selection.val.anchor :=
    sourceLeaf.bindersCover.mapIso iso binderAgreement
  let targetEnumeration : ConcreteElaboration.BinderContext.Enumeration
      input.val targetBinders selection.val.anchor :=
    sourceLeaf.binderEnumeration.mapIso iso binderAgreement
  let binderWitness := ExtractionBinderWitness.terminal input selection layout
    pattern.leaf.binders pattern.leaf.binderEnumeration targetBinders
    targetCover
  obtain ⟨sourceItems, targetItems, targetFuel, sourceCompiled,
      targetCompiled, selectedIso⟩ :=
    coalescedAnchorSelected_iso input selection target hadmissible
  have targetExact : ConcreteElaboration.WireContext.Exact targetContext
      selection.val.anchor := sourceLeaf.wiresExact.mapIso iso
  refine ⟨sourceItems, sourceCompiled, ?_⟩
  intro model named sourceEnv relEnv fragmentEnv environments sourceDenotes
  let targetEnv : Fin targetContext.length → model.Carrier :=
    fun index => sourceEnv (wireEquiv.symm index)
  have isoEnvironments : EnvironmentsAgree wireEquiv sourceEnv targetEnv := by
    intro index
    exact congrArg sourceEnv (wireEquiv.left_inv index)
  have targetDenotes : denoteItemSeq model named targetEnv relEnv targetItems :=
    (selectedIso.denotation model named sourceEnv targetEnv relEnv
      isoEnvironments).mp sourceDenotes
  have targetRegion : denoteRegion model named targetEnv relEnv
      (Region.mk 0 targetItems) :=
    (denoteRegion_mk_zero_iff model named targetEnv relEnv targetItems).2
      targetDenotes
  have terminalSimulation := extractionCompileTerminal_selected_denote
    input selection layout model named pattern.leaf.fuel targetFuel
    pattern.leaf.inheritedWires targetContext pattern.leaf.binders targetBinders
    pattern.leaf.binderEnumeration targetEnumeration targetCover
    pattern.leaf.wiresExact targetExact pattern.leaf.items targetItems
    pattern.leaf.itemsComputation targetCompiled
  exact terminalSimulation fragmentEnv targetEnv relEnv environments targetRegion

end VisualProof.Rule.IterationSoundness
