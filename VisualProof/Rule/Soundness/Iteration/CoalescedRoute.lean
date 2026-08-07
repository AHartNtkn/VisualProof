import VisualProof.Rule.Soundness.Iteration.CoalescedAnchor
import VisualProof.Rule.Soundness.Iteration.KeptRoute

namespace VisualProof.Rule.IterationSoundness

open VisualProof.Concrete

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Rule.ModalSoundness

/-- A route between distinct concrete regions has a proper intrinsic path. -/
theorem Concrete.Splice.RegionRoute.path_ne_nil
    (route : Concrete.Splice.RegionRoute diagram start target path)
    (distinct : start ≠ target) : path ≠ [] := by
  cases route with
  | here => exact False.elim (distinct rfl)
  | step => simp

/-- The root path obtained by composing the canonical anchor view with an
anchor-relative route is exactly the executor's canonical host path. -/
theorem iterationAnchorRoute_hostPath
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    {path : List Nat}
    (route : Concrete.Splice.RegionRoute
      (iterationInput input selection target).coalesceFrameRaw
      selection.val.anchor target path) :
    (iterationCoalescedAnchorView input selection target hadmissible).path ++
        path =
      (Concrete.Splice.Input.compiledSpliceHostView
        (iterationInput input selection target) hadmissible).path := by
  let spliceInput := iterationInput input selection target
  let anchorView := iterationCoalescedAnchorView input selection target
    hadmissible
  let host := Concrete.Splice.Input.compiledSpliceHostView spliceInput hadmissible
  have composed : Concrete.Splice.RegionRoute spliceInput.coalesceFrameRaw
      spliceInput.coalesceFrameRaw.root target (anchorView.path ++ path) :=
    anchorView.route.trans route
  exact Concrete.Splice.Input.RegionRoute.path_unique
    (spliceInput.coalesceFrameRaw_wellFormed hadmissible) composed host.route

/-- At the coalesced selection anchor, the compiler factors into the selected
copy resource and an unselected block containing a complete intrinsic route to
the iteration target. -/
theorem coalescedAnchor_factor_and_route
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hencloses : input.val.Encloses selection.val.anchor target)
    (targetNotSelected : ¬ selection.val.SelectsRegion target) :
    let spliceInput := iterationInput input selection target
    let anchorView := iterationCoalescedAnchorView input selection target
      hadmissible
    let leaf := anchorView.compilerLeaf
    let hereLeaf :=
      Concrete.Splice.Region.ContextPath.CompilerLeaf.hereOfItemsComputation
        spliceInput.coalesceFrameRaw selection.val.anchor leaf.inheritedWires
        leaf.binders leaf.fuel leaf.items leaf.itemsComputation leaf.wiresExact
        leaf.bindersCover leaf.binderEnumeration
    ∃ (keptItems selectedItems : ItemSeq
        (leaf.inheritedWires.extend selection.val.anchor).length
        anchorView.focus.holeRels)
      (path : List Nat)
      (route : Concrete.Splice.RegionRoute spliceInput.coalesceFrameRaw
        selection.val.anchor target path),
      Concrete.Elaboration.compileOccurrencesWith?
          spliceInput.coalesceFrameRaw
          (Concrete.Elaboration.compileRegion?
            spliceInput.coalesceFrameRaw leaf.fuel)
          (leaf.inheritedWires.extend selection.val.anchor) leaf.binders
          (keptOccurrences input.val selection) = some keptItems ∧
        Concrete.Elaboration.compileOccurrencesWith?
          spliceInput.coalesceFrameRaw
          (Concrete.Elaboration.compileRegion?
            spliceInput.coalesceFrameRaw leaf.fuel)
          (leaf.inheritedWires.extend selection.val.anchor) leaf.binders
          (selectedOccurrences input.val selection) = some selectedItems ∧
        Nonempty (CompiledRouteResult
          (spliceInput.coalesceFrame hadmissible) hereLeaf
          (keptOccurrences input.val selection) keptItems route) ∧
        ∀ (model : Model)
          (env : Fin (leaf.inheritedWires.extend
            selection.val.anchor).length → model.Carrier)
          (relEnv : RelEnv model.Carrier anchorView.focus.holeRels),
          denoteItemSeq model  env relEnv leaf.items ↔
            denoteRegion model  env relEnv (Region.mk 0 selectedItems) ∧
            denoteRegion model  env relEnv (Region.mk 0 keptItems) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let anchorView := iterationCoalescedAnchorView input selection target
    hadmissible
  let leaf := anchorView.compilerLeaf
  let hereLeaf :=
    Concrete.Splice.Region.ContextPath.CompilerLeaf.hereOfItemsComputation
      spliceInput.coalesceFrameRaw selection.val.anchor leaf.inheritedWires
      leaf.binders leaf.fuel leaf.items leaf.itemsComputation leaf.wiresExact
      leaf.bindersCover leaf.binderEnumeration
  have partition :
      (keptOccurrences input.val selection ++
          selectedOccurrences input.val selection).Perm
        (Concrete.Elaboration.localOccurrences spliceInput.coalesceFrameRaw
          selection.val.anchor) := by
    change (keptOccurrences input.val selection ++
      selectedOccurrences input.val selection).Perm
        (Concrete.Elaboration.localOccurrences input.val selection.val.anchor)
    exact anchorOccurrences_perm_partition input.val selection
  obtain ⟨keptItems, selectedItems, keptCompiled, selectedCompiled,
      factor⟩ :=
    compilerLeaf_partition_of_perm
      (spliceInput.coalesceFrame hadmissible) selection.val.anchor hereLeaf
      (keptOccurrences input.val selection)
      (selectedOccurrences input.val selection) partition
  have coalescedEncloses : spliceInput.coalesceFrameRaw.Encloses
      selection.val.anchor target :=
    (spliceInput.coalesceFrameRaw_encloses_iff selection.val.anchor target).2
      hencloses
  obtain ⟨path, ⟨route⟩⟩ :=
    Concrete.Splice.regionRoute_complete_of_encloses spliceInput.coalesceFrameRaw
      selection.val.anchor target coalescedEncloses
  have firstChildOccurs : ∀ child,
      (spliceInput.coalesceFrameRaw.regions child).parent? =
          some selection.val.anchor →
      spliceInput.coalesceFrameRaw.Encloses child target →
      Concrete.Elaboration.LocalOccurrence.child child ∈
        keptOccurrences input.val selection := by
    intro child parent childEncloses
    simp only [Concrete.Splice.Input.coalesceFrameRaw_regionCount,
      Concrete.Splice.Input.coalesceFrameRaw_nodeCount] at child ⊢
    change Fin input.val.regionCount at child
    change Concrete.Elaboration.LocalOccurrence.child child ∈
      keptOccurrences input.val selection
    have originalParent : (input.val.regions child).parent? =
        some selection.val.anchor := by
      simpa only [spliceInput, Concrete.Splice.Input.coalesceFrameRaw_regions]
        using parent
    have originalEncloses : input.val.Encloses child target :=
      (spliceInput.coalesceFrameRaw_encloses_iff child target).1 childEncloses
    have localMember : Concrete.Elaboration.LocalOccurrence.child child ∈
        Concrete.Elaboration.localOccurrences input.val selection.val.anchor :=
      (Concrete.Elaboration.mem_localOccurrences_child input.val
        selection.val.anchor child).2 originalParent
    rw [keptOccurrences, List.mem_filter]
    refine ⟨localMember, ?_⟩
    simp only [occurrenceSelected]
    rw [Bool.not_eq_true']
    apply decide_eq_false
    intro childSelected
    apply targetNotSelected
    exact ⟨child, childSelected, originalEncloses⟩
  obtain ⟨routeResult⟩ := compiledOccurrences_route_complete
    (spliceInput.coalesceFrame hadmissible) hereLeaf
    (keptOccurrences input.val selection) keptItems keptCompiled route
    firstChildOccurs
  refine ⟨keptItems, selectedItems, path, route, keptCompiled,
    selectedCompiled, ⟨routeResult⟩, ?_⟩
  intro model  env relEnv
  change denoteItemSeq model  env relEnv hereLeaf.items ↔ _
  calc
    denoteItemSeq model  env relEnv hereLeaf.items ↔
        denoteItemSeq model  env relEnv
          (keptItems.append selectedItems) := factor model  env relEnv
    _ ↔ denoteItemSeq model  env relEnv keptItems ∧
        denoteItemSeq model  env relEnv selectedItems :=
      denoteItemSeq_append model  env relEnv keptItems selectedItems
    _ ↔ denoteRegion model  env relEnv (Region.mk 0 selectedItems) ∧
        denoteRegion model  env relEnv (Region.mk 0 keptItems) := by
      rw [denoteRegion_mk_zero_iff, denoteRegion_mk_zero_iff]
      exact and_comm

/-- The retained compiler path is carried by the selection partition to the
exact authoritative anchor-relative route. -/
theorem coalescedRoute_partition_alignment
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (targetNe : target ≠ selection.val.anchor)
    {keptItems selectedItems : ItemSeq
      ((iterationCoalescedAnchorView input selection target hadmissible)
        |>.compilerLeaf.inheritedWires.extend selection.val.anchor).length
      (iterationCoalescedAnchorView input selection target hadmissible
        ).focus.holeRels}
    (keptCompiled :
      Concrete.Elaboration.compileOccurrencesWith?
          (iterationInput input selection target).coalesceFrameRaw
          (Concrete.Elaboration.compileRegion?
            (iterationInput input selection target).coalesceFrameRaw
            (iterationCoalescedAnchorView input selection target hadmissible
              ).compilerLeaf.fuel)
          ((iterationCoalescedAnchorView input selection target hadmissible)
            |>.compilerLeaf.inheritedWires.extend selection.val.anchor)
          (iterationCoalescedAnchorView input selection target hadmissible
            ).compilerLeaf.binders
          (keptOccurrences input.val selection) = some keptItems)
    (selectedCompiled :
      Concrete.Elaboration.compileOccurrencesWith?
          (iterationInput input selection target).coalesceFrameRaw
          (Concrete.Elaboration.compileRegion?
            (iterationInput input selection target).coalesceFrameRaw
            (iterationCoalescedAnchorView input selection target hadmissible
              ).compilerLeaf.fuel)
          ((iterationCoalescedAnchorView input selection target hadmissible)
            |>.compilerLeaf.inheritedWires.extend selection.val.anchor)
          (iterationCoalescedAnchorView input selection target hadmissible
            ).compilerLeaf.binders
          (selectedOccurrences input.val selection) = some selectedItems)
    {path : List Nat}
    (route : Concrete.Splice.RegionRoute
      (iterationInput input selection target).coalesceFrameRaw
      selection.val.anchor target path)
    (result : CompiledRouteResult
      ((iterationInput input selection target).coalesceFrame hadmissible)
      (Concrete.Splice.Region.ContextPath.CompilerLeaf.hereOfItemsComputation
        (iterationInput input selection target).coalesceFrameRaw
        selection.val.anchor
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.inheritedWires
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.binders
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.fuel
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.items
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.itemsComputation
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.wiresExact
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.bindersCover
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.binderEnumeration)
      (keptOccurrences input.val selection) keptItems route) :
    let leaf :=
      (iterationCoalescedAnchorView input selection target hadmissible
        ).compilerLeaf
    let hereLeaf :=
      Concrete.Splice.Region.ContextPath.CompilerLeaf.hereOfItemsComputation
        (iterationInput input selection target).coalesceFrameRaw
        selection.val.anchor leaf.inheritedWires leaf.binders leaf.fuel
        leaf.items leaf.itemsComputation leaf.wiresExact leaf.bindersCover
        leaf.binderEnumeration
    ∃ (compiledPosition : Fin
        (keptOccurrences input.val selection).length)
      (rest : List Nat)
      (retained : Region.ContextPath (Region.mk 0 keptItems)
        (compiledPosition.val :: rest))
      (terminal : CompiledRouteTerminal
        ((iterationInput input selection target).coalesceFrame hadmissible)
        hereLeaf keptItems route (compiledPosition.val :: rest) retained)
      (iso : RegionIso
        (FiniteEquiv.refl
          (Fin (leaf.inheritedWires.extend selection.val.anchor).length))
        (iterationCoalescedAnchorView input selection target hadmissible
          ).focus.holeRels
        (Region.mk 0 (keptItems.append selectedItems))
        (Region.mk 0 leaf.items))
      (alignment : RegionIso.ContextPathAlignment iso
        (retained.appendRootItemsRight selectedItems)),
      HEq retained result.witness ∧ alignment.targetPath = path ∧
        ∀ index, (alignment.holeWire index).val = index.val := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let anchorView := iterationCoalescedAnchorView input selection target
    hadmissible
  have partition :
      (keptOccurrences input.val selection ++
          selectedOccurrences input.val selection).Perm
        (Concrete.Elaboration.localOccurrences spliceInput.coalesceFrameRaw
          selection.val.anchor) := by
    change (keptOccurrences input.val selection ++
      selectedOccurrences input.val selection).Perm
        (Concrete.Elaboration.localOccurrences input.val selection.val.anchor)
    exact anchorOccurrences_perm_partition input.val selection
  rcases result.headPositions with atStart | ⟨child, keptPosition,
      fullPosition, rest, compiledPath, routePath, keptAt, fullAt⟩
  · exact False.elim (targetNe atStart)
  · let retained : Region.ContextPath (Region.mk 0 keptItems)
        (keptPosition.val :: rest) := compiledPath ▸ result.witness
    have retainedHEq : HEq retained result.witness := by
      dsimp only [retained]
      exact eqRec_heq compiledPath result.witness
    obtain ⟨terminalData⟩ := Or.resolve_left result.terminal targetNe
    let retainedTerminal : CompiledRouteTerminal
        (spliceInput.coalesceFrame hadmissible)
        (Concrete.Splice.Region.ContextPath.CompilerLeaf.hereOfItemsComputation
          spliceInput.coalesceFrameRaw selection.val.anchor
          anchorView.compilerLeaf.inheritedWires
          anchorView.compilerLeaf.binders anchorView.compilerLeaf.fuel
          anchorView.compilerLeaf.items
          anchorView.compilerLeaf.itemsComputation
          anchorView.compilerLeaf.wiresExact
          anchorView.compilerLeaf.bindersCover
          anchorView.compilerLeaf.binderEnumeration)
        keptItems route (keptPosition.val :: rest) retained :=
      terminalData.castPath compiledPath
    obtain ⟨iso, alignment, alignmentPath, alignmentWire⟩ :=
      compilerLeaf_partition_alignRetainedOccurrence
        (spliceInput.coalesceFrame hadmissible) selection.val.anchor
        (Concrete.Splice.Region.ContextPath.CompilerLeaf.hereOfItemsComputation
          spliceInput.coalesceFrameRaw selection.val.anchor
          anchorView.compilerLeaf.inheritedWires
          anchorView.compilerLeaf.binders anchorView.compilerLeaf.fuel
          anchorView.compilerLeaf.items
          anchorView.compilerLeaf.itemsComputation
          anchorView.compilerLeaf.wiresExact
          anchorView.compilerLeaf.bindersCover
          anchorView.compilerLeaf.binderEnumeration)
        (keptOccurrences input.val selection)
        (selectedOccurrences input.val selection) partition keptCompiled
        selectedCompiled (.child child) keptPosition fullPosition keptAt fullAt
        retained
    exact ⟨keptPosition, rest, retained, retainedTerminal, iso, alignment,
      retainedHEq, alignmentPath.trans routePath.symm, alignmentWire⟩

/-- The retained route's terminal lexical state is the executable splice
compiler's canonical state at the same concrete target. -/
theorem coalescedRouteTerminal_hostLexical
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hencloses : input.val.Encloses selection.val.anchor target)
    {keptItems : ItemSeq
      ((iterationCoalescedAnchorView input selection target hadmissible)
        |>.compilerLeaf.inheritedWires.extend selection.val.anchor).length
      (iterationCoalescedAnchorView input selection target hadmissible
        ).focus.holeRels}
    {path : List Nat}
    (route : Concrete.Splice.RegionRoute
      (iterationInput input selection target).coalesceFrameRaw
      selection.val.anchor target path)
    {compiledPath : List Nat}
    {witness : Region.ContextPath (Region.mk 0 keptItems) compiledPath}
    (terminal : CompiledRouteTerminal
      ((iterationInput input selection target).coalesceFrame hadmissible)
      (Concrete.Splice.Region.ContextPath.CompilerLeaf.hereOfItemsComputation
        (iterationInput input selection target).coalesceFrameRaw
        selection.val.anchor
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.inheritedWires
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.binders
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.fuel
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.items
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.itemsComputation
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.wiresExact
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.bindersCover
        (iterationCoalescedAnchorView input selection target hadmissible
          ).compilerLeaf.binderEnumeration)
      keptItems route compiledPath witness) :
    let spliceInput := iterationInput input selection target
    let host := Concrete.Splice.Input.compiledSpliceHostView spliceInput hadmissible
    ∃ hrels : witness.toFocus.holeRels = host.focus.holeRels,
      HEq terminal.leaf.binders host.compilerLeaf.binders := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let anchorView := iterationCoalescedAnchorView input selection target
    hadmissible
  let host := Concrete.Splice.Input.compiledSpliceHostView spliceInput hadmissible
  have coalescedEncloses : spliceInput.coalesceFrameRaw.Encloses
      selection.val.anchor target :=
    (spliceInput.coalesceFrameRaw_encloses_iff selection.val.anchor target).2
      hencloses
  have rootBinders : anchorView.result.state.binders =
      host.result.state.binders :=
    anchorView.result.binders_eq.trans host.result.binders_eq.symm
  obtain ⟨tailPath, tailOuter, tailBody, tailRoute, tailWitness, tailState,
      tailTrace, tailStartBinders, tailRels, tailTerminalBinders⟩ :=
    Concrete.Splice.Input.CompilerTrace.tailAtEnclosed
      (spliceInput.coalesceFrameRaw_wellFormed hadmissible)
      anchorView.result.trace host.result.trace rootBinders coalescedEncloses
  have tailStartsAtAnchor : tailState.binders =
      (Concrete.Splice.Region.ContextPath.CompilerLeaf.hereOfItemsComputation
        spliceInput.coalesceFrameRaw selection.val.anchor
        anchorView.compilerLeaf.inheritedWires anchorView.compilerLeaf.binders
        anchorView.compilerLeaf.fuel anchorView.compilerLeaf.items
        anchorView.compilerLeaf.itemsComputation anchorView.compilerLeaf.wiresExact
        anchorView.compilerLeaf.bindersCover
        anchorView.compilerLeaf.binderEnumeration).binders := by
    simpa [anchorView, Concrete.Splice.SiteView.compilerLeaf] using tailStartBinders
  obtain ⟨routeRels, routeTerminalBinders⟩ :=
    terminal.terminalLexical tailTrace tailStartsAtAnchor
  refine ⟨routeRels.trans tailRels, ?_⟩
  exact (routeTerminalBinders.trans tailTerminalBinders)

end VisualProof.Rule.IterationSoundness
