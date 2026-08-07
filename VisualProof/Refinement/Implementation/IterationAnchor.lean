import VisualProof.Refinement.Implementation.IterationPartition
import VisualProof.Refinement.Implementation.IterationQuotient

namespace VisualProof.Refinement.Implementation.IterationAnchor

open VisualProof
open VisualProof.Concrete
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Refinement.Implementation.IterationPartition

noncomputable def coalescedAnchorView
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (admissible : (iterationInput input selection target).Admissible) :
    Concrete.Splice.SiteView
      ((iterationInput input selection target).coalesceFrame admissible)
      selection.val.anchor :=
  Classical.choice (Concrete.Splice.siteView_complete
    ((iterationInput input selection target).coalesceFrame admissible)
    selection.val.anchor)

theorem selected_iso
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (admissible : (iterationInput input selection target).Admissible) :
    let spliceInput := iterationInput input selection target
    let anchorView := coalescedAnchorView input selection target admissible
    let sourceLeaf := anchorView.compilerLeaf
    let sourceContext := sourceLeaf.inheritedWires.extend selection.val.anchor
    let iso := IterationQuotient.coalescedFrameIso input selection target
    let targetContext := sourceContext.map iso.wires
    let targetBinders : Concrete.Elaboration.BinderContext input.val
        anchorView.focus.holeRels := fun binder => sourceLeaf.binders binder
    let wireEquiv : FiniteEquiv (Fin sourceContext.length)
        (Fin targetContext.length) :=
      FiniteEquiv.finCast (List.length_map iso.wires).symm
    ∃ (sourceItems : ItemSeq sourceContext.length anchorView.focus.holeRels)
      (targetItems : ItemSeq targetContext.length anchorView.focus.holeRels)
      (targetFuel : Nat),
      Concrete.Elaboration.compileOccurrencesWith?
          spliceInput.coalesceFrameRaw
          (Concrete.Elaboration.compileRegion? spliceInput.coalesceFrameRaw
            sourceLeaf.fuel)
          sourceContext sourceLeaf.binders
          (selectedOccurrences input.val selection) = some sourceItems ∧
        Concrete.Elaboration.compileOccurrencesWith? input.val
          (Concrete.Elaboration.compileRegion? input.val targetFuel)
          targetContext targetBinders
          (selectedOccurrences input.val selection) = some targetItems ∧
        ItemSeqIso wireEquiv anchorView.focus.holeRels
          sourceItems targetItems := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let anchorView := coalescedAnchorView input selection target admissible
  let sourceLeaf := anchorView.compilerLeaf
  let sourceContext := sourceLeaf.inheritedWires.extend selection.val.anchor
  let iso := IterationQuotient.coalescedFrameIso input selection target
  let targetContext := sourceContext.map iso.wires
  let targetBinders : Concrete.Elaboration.BinderContext input.val
      anchorView.focus.holeRels := fun binder => sourceLeaf.binders binder
  let wireEquiv : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length) :=
    FiniteEquiv.finCast (List.length_map iso.wires).symm
  let hereLeaf :=
    Concrete.Splice.Region.ContextPath.CompilerLeaf.hereOfItemsComputation
      spliceInput.coalesceFrameRaw selection.val.anchor
      sourceLeaf.inheritedWires sourceLeaf.binders sourceLeaf.fuel
      sourceLeaf.items sourceLeaf.itemsComputation sourceLeaf.wiresExact
      sourceLeaf.bindersCover sourceLeaf.binderEnumeration
  have partition :
      (selectedOccurrences input.val selection ++
          keptOccurrences input.val selection).Perm
        (Concrete.Elaboration.localOccurrences spliceInput.coalesceFrameRaw
          selection.val.anchor) := by
    change (selectedOccurrences input.val selection ++
      keptOccurrences input.val selection).Perm
        (Concrete.Elaboration.localOccurrences input.val selection.val.anchor)
    exact occurrences_perm input.val selection
  obtain ⟨sourceItems, keptItems, sourceCompiled, _keptCompiled,
      _partitionIso⟩ :=
    partition_complete_of_perm (spliceInput.coalesceFrame admissible)
      selection.val.anchor hereLeaf
      (selectedOccurrences input.val selection)
      (keptOccurrences input.val selection) partition
  obtain ⟨steps, stepsEq⟩ :=
    input.property.all_regions_reach_root selection.val.anchor
  let targetFuel := input.val.regionCount - steps.val
  have targetFuelEnough : steps.val + 1 + targetFuel =
      input.val.regionCount + 1 := by
    dsimp only [targetFuel]
    omega
  have targetExact : Concrete.Elaboration.WireContext.Exact targetContext
      selection.val.anchor := sourceLeaf.wiresExact.mapIso iso
  have targetCovers : targetBinders.Covers selection.val.anchor := by
    intro binder parent arity bubble encloses
    apply sourceLeaf.bindersCover binder parent arity
    · simpa only [spliceInput,
        Concrete.Splice.Input.coalesceFrameRaw_regions] using bubble
    · exact (spliceInput.coalesceFrameRaw_encloses_iff binder
        selection.val.anchor).2 encloses
  have targetLocal : ∀ occurrence,
      occurrence ∈ selectedOccurrences input.val selection →
      occurrence ∈ Concrete.Elaboration.localOccurrences input.val
        selection.val.anchor := by
    intro occurrence member
    rw [selectedOccurrences, List.mem_filter] at member
    exact member.1
  obtain ⟨targetItems, targetCompiled⟩ :=
    Concrete.Elaboration.compileDirectOccurrences?_complete input.property
      stepsEq targetFuelEnough targetExact targetCovers
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
      Concrete.Elaboration.compileOccurrencesWith? input.val
          (Concrete.Elaboration.compileRegion? input.val targetFuel)
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

end VisualProof.Refinement.Implementation.IterationAnchor
