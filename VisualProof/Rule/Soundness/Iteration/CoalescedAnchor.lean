import VisualProof.Rule.Soundness.Iteration.DiscreteQuotient
import VisualProof.Rule.Soundness.Iteration.SelectionPartition
import VisualProof.Rule.Soundness.Iteration.ExtractionTerminalSemantic

namespace VisualProof.Rule.IterationSoundness

open VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Rule.ModalSoundness

/-- Canonical compiler evidence at the selection anchor inside the coalesced
frame.  This is distinct from the splice-site view when iteration copies an
ancestor occurrence into a proper descendant. -/
noncomputable def iterationCoalescedAnchorView
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible) :
    Concrete.Splice.SiteView
      ((iterationInput input selection target).coalesceFrame hadmissible)
      selection.val.anchor :=
  Classical.choice (Concrete.Splice.siteView_complete
    ((iterationInput input selection target).coalesceFrame hadmissible)
    selection.val.anchor)

/-- The selected compiler block at the canonical coalesced splice site is
isomorphic to a compiler block over the original diagram at the same anchor.
The target context is exactly the pointwise image of the authoritative splice
context, so the theorem retains every lexical wire value. -/
theorem coalescedAnchorSelected_iso
    (input : Concrete.Checked )
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
    let targetBinders : Concrete.Elaboration.BinderContext input.val
        anchorView.focus.holeRels := fun binder => sourceLeaf.binders binder
    let wireEquiv : FiniteEquiv (Fin sourceContext.length)
        (Fin targetContext.length) :=
      FiniteEquiv.finCast (List.length_map iso.wires).symm
    ∃ (sourceItems : ItemSeq  sourceContext.length
        anchorView.focus.holeRels)
      (targetItems : ItemSeq  targetContext.length
        anchorView.focus.holeRels)
      (targetFuel : Nat),
      Concrete.Elaboration.compileOccurrencesWith?
          spliceInput.coalesceFrameRaw
          (Concrete.Elaboration.compileRegion?
            spliceInput.coalesceFrameRaw sourceLeaf.fuel)
          sourceContext sourceLeaf.binders
          (selectedOccurrences input.val selection) = some sourceItems ∧
        Concrete.Elaboration.compileOccurrencesWith?  input.val
          (Concrete.Elaboration.compileRegion?  input.val targetFuel)
          targetContext targetBinders
          (selectedOccurrences input.val selection) = some targetItems ∧
        ItemSeqIso  wireEquiv anchorView.focus.holeRels
          sourceItems targetItems := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let anchorView := iterationCoalescedAnchorView input selection target
    hadmissible
  let sourceLeaf := anchorView.compilerLeaf
  let sourceContext := sourceLeaf.inheritedWires.extend selection.val.anchor
  let iso := iterationCoalescedFrameIso input selection target
  let targetContext := sourceContext.map iso.wires
  let targetBinders : Concrete.Elaboration.BinderContext input.val
      anchorView.focus.holeRels := fun binder => sourceLeaf.binders binder
  let wireEquiv : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length) :=
    FiniteEquiv.finCast (List.length_map iso.wires).symm
  let hereLeaf :=
    Concrete.Splice.Region.ContextPath.CompilerLeaf.hereOfItemsComputation
      spliceInput.coalesceFrameRaw selection.val.anchor sourceLeaf.inheritedWires
      sourceLeaf.binders sourceLeaf.fuel sourceLeaf.items
      sourceLeaf.itemsComputation sourceLeaf.wiresExact
      sourceLeaf.bindersCover sourceLeaf.binderEnumeration
  have partition :
      (keptOccurrences input.val selection ++
          selectedOccurrences input.val selection).Perm
        (Concrete.Elaboration.localOccurrences spliceInput.coalesceFrameRaw
          selection.val.anchor) := by
    change (keptOccurrences input.val selection ++
      selectedOccurrences input.val selection).Perm
        (Concrete.Elaboration.localOccurrences input.val selection.val.anchor)
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
  have targetExact : Concrete.Elaboration.WireContext.Exact targetContext
      selection.val.anchor := by
    exact sourceLeaf.wiresExact.mapIso iso
  have targetCovers :
      targetBinders.Covers selection.val.anchor := by
    intro binder parent arity hbubble hencloses
    apply sourceLeaf.bindersCover binder parent arity
    · simpa only [spliceInput,
        Concrete.Splice.Input.coalesceFrameRaw_regions] using hbubble
    · exact (spliceInput.coalesceFrameRaw_encloses_iff binder
        selection.val.anchor).2
        hencloses
  have targetLocal : ∀ occurrence,
      occurrence ∈ selectedOccurrences input.val selection →
      occurrence ∈ Concrete.Elaboration.localOccurrences input.val
        selection.val.anchor := by
    intro occurrence member
    rw [selectedOccurrences, List.mem_filter] at member
    exact member.1
  obtain ⟨targetItems, targetCompiled⟩ :=
    Concrete.Elaboration.compileDirectOccurrences?_complete input.property
      hsteps targetFuelEnough targetExact targetCovers
      (selectedOccurrences input.val selection) targetLocal
  have sourceLocal : ∀ occurrence,
      occurrence ∈ selectedOccurrences input.val selection →
      occurrence ∈ Concrete.Elaboration.localOccurrences
        spliceInput.coalesceFrameRaw selection.val.anchor := by
    intro occurrence member
    have original := targetLocal occurrence member
    simpa only [spliceInput, Concrete.Splice.Input.coalesceFrameRaw_regions,
      Concrete.Splice.Input.coalesceFrameRaw_nodes] using original
  have wireAgreement : Concrete.Elaboration.WireContextsAgree iso
      sourceContext targetContext wireEquiv := by
    intro index
    simp only [targetContext, wireEquiv, List.get_eq_getElem,
      List.getElem_map]
    rfl
  have binderAgreement : Concrete.Elaboration.BinderContextsAgree iso
      sourceLeaf.binders targetBinders := by
    intro binder
    rfl
  have renamedSelected :
      (selectedOccurrences input.val selection).map
          (Concrete.Elaboration.renameOccurrence iso) =
        selectedOccurrences input.val selection := by
    induction selectedOccurrences input.val selection with
    | nil => rfl
    | cons occurrence tail induction =>
        cases occurrence with
        | node node =>
            change Concrete.Elaboration.LocalOccurrence.node (iso.nodes node) ::
                tail.map (Concrete.Elaboration.renameOccurrence iso) =
              Concrete.Elaboration.LocalOccurrence.node node :: tail
            rw [show iso.nodes node = node by rfl, induction]
        | child child =>
            change Concrete.Elaboration.LocalOccurrence.child
                  (iso.regions child) ::
                tail.map (Concrete.Elaboration.renameOccurrence iso) =
              Concrete.Elaboration.LocalOccurrence.child child :: tail
            rw [show iso.regions child = child by rfl, induction]
  have targetCompiledRenamed :
      Concrete.Elaboration.compileOccurrencesWith?  input.val
          (Concrete.Elaboration.compileRegion?  input.val targetFuel)
          targetContext targetBinders
          ((selectedOccurrences input.val selection).map
            (Concrete.Elaboration.renameOccurrence iso)) = some targetItems := by
    rwa [renamedSelected]
  have selectedIso :=
    Concrete.Elaboration.compileOccurrencesWith?_equivariant iso input.property
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
    (input : Concrete.Checked )
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
    let targetBinders : Concrete.Elaboration.BinderContext input.val
        anchorView.focus.holeRels := fun binder => sourceLeaf.binders binder
    let wireEquiv : FiniteEquiv (Fin sourceContext.length)
        (Fin targetContext.length) :=
      FiniteEquiv.finCast (List.length_map iso.wires).symm
    let pattern := Concrete.Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
    let targetCover : targetBinders.Covers selection.val.anchor :=
      sourceLeaf.bindersCover.mapIso iso (by intro binder; rfl)
    let binderWitness := ExtractionBinderWitness.terminal input selection layout
      pattern.leaf.binders pattern.leaf.binderEnumeration targetBinders
      targetCover
    ∃ sourceItems : ItemSeq  sourceContext.length
        anchorView.focus.holeRels,
      Concrete.Elaboration.compileOccurrencesWith?
          spliceInput.coalesceFrameRaw
          (Concrete.Elaboration.compileRegion?
            spliceInput.coalesceFrameRaw sourceLeaf.fuel)
          sourceContext sourceLeaf.binders
          (selectedOccurrences input.val selection) = some sourceItems ∧
      ∀ (model : Model)
        (sourceEnv : Fin sourceContext.length → model.Carrier)
        (relEnv : RelEnv model.Carrier anchorView.focus.holeRels)
        (fragmentEnv : Fin pattern.leaf.inheritedWires.length → model.Carrier),
        (extractionContextRelation input selection layout
          pattern.leaf.inheritedWires targetContext).EnvironmentsAgree
            fragmentEnv (fun index => sourceEnv (wireEquiv.symm index)) →
        denoteItemSeq model  sourceEnv relEnv sourceItems →
        denoteRegion model  fragmentEnv relEnv
          ((Concrete.Elaboration.finishRegion
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
  let targetBinders : Concrete.Elaboration.BinderContext input.val
      anchorView.focus.holeRels := fun binder => sourceLeaf.binders binder
  let wireEquiv : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length) :=
    FiniteEquiv.finCast (List.length_map iso.wires).symm
  let pattern := Concrete.Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
  have binderAgreement : Concrete.Elaboration.BinderContextsAgree iso
      sourceLeaf.binders targetBinders := by
    intro binder
    rfl
  let targetCover : targetBinders.Covers selection.val.anchor :=
    sourceLeaf.bindersCover.mapIso iso binderAgreement
  let targetEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      input.val targetBinders selection.val.anchor :=
    sourceLeaf.binderEnumeration.mapIso iso binderAgreement
  let binderWitness := ExtractionBinderWitness.terminal input selection layout
    pattern.leaf.binders pattern.leaf.binderEnumeration targetBinders
    targetCover
  obtain ⟨sourceItems, targetItems, targetFuel, sourceCompiled,
      targetCompiled, selectedIso⟩ :=
    coalescedAnchorSelected_iso input selection target hadmissible
  have targetExact : Concrete.Elaboration.WireContext.Exact targetContext
      selection.val.anchor := sourceLeaf.wiresExact.mapIso iso
  refine ⟨sourceItems, sourceCompiled, ?_⟩
  intro model  sourceEnv relEnv fragmentEnv environments sourceDenotes
  let targetEnv : Fin targetContext.length → model.Carrier :=
    fun index => sourceEnv (wireEquiv.symm index)
  have isoEnvironments : EnvironmentsAgree wireEquiv sourceEnv targetEnv := by
    intro index
    exact congrArg sourceEnv (wireEquiv.left_inv index)
  have targetDenotes : denoteItemSeq model  targetEnv relEnv targetItems :=
    (selectedIso.denotation model  sourceEnv targetEnv relEnv
      isoEnvironments).mp sourceDenotes
  have targetRegion : denoteRegion model  targetEnv relEnv
      (Region.mk 0 targetItems) :=
    (denoteRegion_mk_zero_iff model  targetEnv relEnv targetItems).2
      targetDenotes
  have terminalSimulation := extractionCompileTerminal_selected_denote
    input selection layout model  pattern.leaf.fuel targetFuel
    pattern.leaf.inheritedWires targetContext pattern.leaf.binders targetBinders
    pattern.leaf.binderEnumeration targetEnumeration targetCover
    pattern.leaf.wiresExact targetExact pattern.leaf.items targetItems
    pattern.leaf.itemsComputation targetCompiled
  exact terminalSimulation fragmentEnv targetEnv relEnv environments targetRegion

/-- The selected coalesced anchor block semantically supplies the extracted
open root when the binder spine is empty.  Exposed positions remain ambient;
hidden root wires are provided by the root simulation's existential local
environment. -/
theorem coalescedAnchorSelected_entails_root
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hzero : (iterationInput input selection target).binderSpine.proxyCount =
      0) :
    let spliceInput := iterationInput input selection target
    let layout : FragmentLayout input.val selection := {}
    let anchorView := iterationCoalescedAnchorView input selection target
      hadmissible
    let sourceLeaf := anchorView.compilerLeaf
    let sourceContext := sourceLeaf.inheritedWires.extend selection.val.anchor
    let iso := iterationCoalescedFrameIso input selection target
    let targetContext := sourceContext.map iso.wires
    let targetBinders : Concrete.Elaboration.BinderContext input.val
        anchorView.focus.holeRels := fun binder => sourceLeaf.binders binder
    let wireEquiv : FiniteEquiv (Fin sourceContext.length)
        (Fin targetContext.length) :=
      FiniteEquiv.finCast (List.length_map iso.wires).symm
    let pattern := Concrete.Splice.Input.compiledSpliceOpenRootItems spliceInput.pattern
    ∃ sourceItems : ItemSeq  sourceContext.length
        anchorView.focus.holeRels,
      Concrete.Elaboration.compileOccurrencesWith?
          spliceInput.coalesceFrameRaw
          (Concrete.Elaboration.compileRegion?
            spliceInput.coalesceFrameRaw sourceLeaf.fuel)
          sourceContext sourceLeaf.binders
          (selectedOccurrences input.val selection) = some sourceItems ∧
      ∀ (model : Model)
        (sourceEnv : Fin sourceContext.length → model.Carrier)
        (relEnv : RelEnv model.Carrier anchorView.focus.holeRels)
        (fragmentEnv : Fin spliceInput.pattern.val.exposedWires.length →
          model.Carrier),
        (extractionContextRelation input selection layout
          spliceInput.pattern.val.exposedWires targetContext).EnvironmentsAgree
            fragmentEnv (fun index => sourceEnv (wireEquiv.symm index)) →
        denoteItemSeq model  sourceEnv relEnv sourceItems →
        denoteRegion model  fragmentEnv relEnv
          ((Concrete.Elaboration.finishRoot
              spliceInput.pattern.val.exposedWires
              spliceInput.pattern.val.hiddenWires pattern.items
            ).renameRelations
              (Concrete.Splice.Input.PlugLayout.emptyRelationRenaming
                anchorView.focus.holeRels)) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let layout : FragmentLayout input.val selection := {}
  let anchorView := iterationCoalescedAnchorView input selection target
    hadmissible
  let sourceLeaf := anchorView.compilerLeaf
  let sourceContext := sourceLeaf.inheritedWires.extend selection.val.anchor
  let iso := iterationCoalescedFrameIso input selection target
  let targetContext := sourceContext.map iso.wires
  let targetBinders : Concrete.Elaboration.BinderContext input.val
      anchorView.focus.holeRels := fun binder => sourceLeaf.binders binder
  have binderAgreement : Concrete.Elaboration.BinderContextsAgree iso
      sourceLeaf.binders targetBinders := by
    intro binder
    rfl
  let targetCover : targetBinders.Covers selection.val.anchor :=
    sourceLeaf.bindersCover.mapIso iso binderAgreement
  let targetEnumeration : Concrete.Elaboration.BinderContext.Enumeration
      input.val targetBinders selection.val.anchor :=
    sourceLeaf.binderEnumeration.mapIso iso binderAgreement
  let wireEquiv : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length) :=
    FiniteEquiv.finCast (List.length_map iso.wires).symm
  let pattern := Concrete.Splice.Input.compiledSpliceOpenRootItems spliceInput.pattern
  obtain ⟨sourceItems, targetItems, targetFuel, sourceCompiled,
      targetCompiled, selectedIso⟩ :=
    coalescedAnchorSelected_iso input selection target hadmissible
  have targetExact : Concrete.Elaboration.WireContext.Exact targetContext
      selection.val.anchor := sourceLeaf.wiresExact.mapIso iso
  refine ⟨sourceItems, sourceCompiled, ?_⟩
  intro model  sourceEnv relEnv fragmentEnv environments sourceDenotes
  let targetEnv : Fin targetContext.length → model.Carrier :=
    fun index => sourceEnv (wireEquiv.symm index)
  have isoEnvironments : EnvironmentsAgree wireEquiv sourceEnv targetEnv := by
    intro index
    exact congrArg sourceEnv (wireEquiv.left_inv index)
  have targetDenotes : denoteItemSeq model  targetEnv relEnv targetItems :=
    (selectedIso.denotation model  sourceEnv targetEnv relEnv
      isoEnvironments).mp sourceDenotes
  have targetRegion : denoteRegion model  targetEnv relEnv
      (Region.mk 0 targetItems) :=
    (denoteRegion_mk_zero_iff model  targetEnv relEnv targetItems).2
      targetDenotes
  have rootSimulation := extractionCompileRoot_selected_denote
    input selection layout hzero model  targetFuel targetContext
    targetBinders targetEnumeration targetCover targetExact pattern.items
    targetItems pattern.computation targetCompiled
  exact rootSimulation fragmentEnv targetEnv relEnv environments targetRegion

end VisualProof.Rule.IterationSoundness
