import VisualProof.Rule.Soundness.Iteration.ActualTransport

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Rule.ModalSoundness

/-- A relation environment is determined by the values of all of its typed
variables.  This is the dependent-tuple extensionality needed when a retained
route transports the anchor's lexical environment to its terminal hole. -/
theorem RelEnv.eq_of_lookup
    {rels : RelCtx} {left right : RelEnv D rels}
    (equal : ∀ {arity : Nat} (relation : RelVar rels arity),
      left.lookup relation = right.lookup relation) :
    left = right := by
  induction rels with
  | nil => cases left; cases right; rfl
  | cons head tail induction =>
      rcases left with ⟨leftHead, leftTail⟩
      rcases right with ⟨rightHead, rightTail⟩
      have headEq : leftHead = rightHead := by
        simpa [RelEnv.lookup] using equal (⟨0, rfl⟩ : RelVar (head :: tail) head)
      have tailEq : leftTail = rightTail := by
        apply induction
        intro arity relation
        simpa [RelEnv.lookup] using
          equal (⟨relation.index.succ, relation.hasArity⟩ :
            RelVar (head :: tail) arity)
      rw [headEq, tailEq]

/-- Along the retained route, pulling a terminal relation valuation back by
the route's lexical embedding gives exactly the anchor relation valuation. -/
theorem reachable_pullback_outerRelation
    (context : DiagramContext signature outerWires holeWires outerRels holeRels)
    (outerEnv : Fin outerWires → D) (outerRelEnv : RelEnv D outerRels)
    (holeEnv : Fin holeWires → D) (holeRelEnv : RelEnv D holeRels)
    (reachable : context.Reachable outerEnv outerRelEnv holeEnv holeRelEnv) :
    RelEnv.pullback context.outerRelation holeRelEnv = outerRelEnv := by
  apply RelEnv.eq_of_lookup
  intro arity relation
  exact (RelEnv.pullback_agrees context.outerRelation holeRelEnv
    arity relation).trans
      (reachable.outerRelation arity relation).symm

/-- Every wire inherited by the extracted terminal body occurs in the full
selection-anchor context. -/
theorem iterationTerminalAnchorMember
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    (index : Fin (Splice.Input.compiledSpliceTerminalView
      (iterationInput input selection target) hnonempty
    ).leaf.inheritedWires.length) :
    input.val.fragmentWireOrigin selection
        ({} : FragmentLayout input.val selection)
        ((Splice.Input.compiledSpliceTerminalView
          (iterationInput input selection target) hnonempty
        ).leaf.inheritedWires.get index) ∈
      (((iterationCoalescedAnchorView input selection target hadmissible)
        |>.compilerLeaf.inheritedWires.extend selection.val.anchor).map
          (iterationCoalescedFrameIso input selection target).wires) := by
  let spliceInput := iterationInput input selection target
  let layout : FragmentLayout input.val selection := {}
  let anchorView := iterationCoalescedAnchorView input selection target
    hadmissible
  let sourceContext :=
    anchorView.compilerLeaf.inheritedWires.extend selection.val.anchor
  let targetContext := sourceContext.map
    (iterationCoalescedFrameIso input selection target).wires
  let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
  have targetExact : ConcreteElaboration.WireContext.Exact targetContext
      selection.val.anchor :=
    anchorView.compilerLeaf.wiresExact.mapIso
      (iterationCoalescedFrameIso input selection target)
  have patternVisible : spliceInput.pattern.val.diagram.Encloses
      (spliceInput.pattern.val.diagram.wires
        (pattern.leaf.inheritedWires.get index)).scope
      spliceInput.binderSpine.bodyContainer := by
    apply (pattern.leaf.wiresExact.mem_iff _).1
    apply List.mem_append.mpr
    exact Or.inl (List.get_mem _ index)
  have hostVisible := fragmentWireOrigin_scope_encloses_anchor input selection
    layout (pattern.leaf.inheritedWires.get index) patternVisible
  exact (targetExact.mem_iff _).2 hostVisible

/-- Canonical anchor-context index of a wire inherited by the extracted
terminal body. -/
noncomputable def iterationTerminalAnchorIndex
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    (index : Fin (Splice.Input.compiledSpliceTerminalView
      (iterationInput input selection target) hnonempty
    ).leaf.inheritedWires.length) :
    Fin (((iterationCoalescedAnchorView input selection target hadmissible)
      |>.compilerLeaf.inheritedWires.extend selection.val.anchor).map
        (iterationCoalescedFrameIso input selection target).wires).length :=
  Classical.choose (indexOf?_complete
    (iterationTerminalAnchorMember input selection target hadmissible
      hnonempty index))

theorem iterationTerminalAnchorIndex_get
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    (index : Fin (Splice.Input.compiledSpliceTerminalView
      (iterationInput input selection target) hnonempty
    ).leaf.inheritedWires.length) :
    (((iterationCoalescedAnchorView input selection target hadmissible)
      |>.compilerLeaf.inheritedWires.extend selection.val.anchor).map
        (iterationCoalescedFrameIso input selection target).wires).get
          (iterationTerminalAnchorIndex input selection target hadmissible
            hnonempty index) =
      input.val.fragmentWireOrigin selection
        ({} : FragmentLayout input.val selection)
        ((Splice.Input.compiledSpliceTerminalView
          (iterationInput input selection target) hnonempty
        ).leaf.inheritedWires.get index) := by
  classical
  unfold iterationTerminalAnchorIndex
  exact indexOf?_sound (Classical.choose_spec (indexOf?_complete
    (iterationTerminalAnchorMember input selection target hadmissible
      hnonempty index)))

theorem iterationTerminalAnchorIndex_related
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    (index : Fin (Splice.Input.compiledSpliceTerminalView
      (iterationInput input selection target) hnonempty
    ).leaf.inheritedWires.length) :
    (extractionContextRelation input selection
      ({} : FragmentLayout input.val selection)
      (Splice.Input.compiledSpliceTerminalView
        (iterationInput input selection target) hnonempty).leaf.inheritedWires
      (((iterationCoalescedAnchorView input selection target hadmissible)
        |>.compilerLeaf.inheritedWires.extend selection.val.anchor).map
          (iterationCoalescedFrameIso input selection target).wires)
    ).Rel index (iterationTerminalAnchorIndex input selection target
      hadmissible hnonempty index) := by
  unfold extractionContextRelation
  exact (iterationTerminalAnchorIndex_get input selection target hadmissible
    hnonempty index).symm

/-- Every exposed wire of an empty-spine extracted root occurs in the full
selection-anchor context. -/
theorem iterationRootAnchorMember
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hzero : (iterationInput input selection target).binderSpine.proxyCount =
      0)
    (index : Fin
      (iterationInput input selection target).pattern.val.exposedWires.length) :
    input.val.fragmentWireOrigin selection
        ({} : FragmentLayout input.val selection)
        ((iterationInput input selection target).pattern.val.exposedWires.get
          index) ∈
      (((iterationCoalescedAnchorView input selection target hadmissible)
        |>.compilerLeaf.inheritedWires.extend selection.val.anchor).map
          (iterationCoalescedFrameIso input selection target).wires) := by
  let spliceInput := iterationInput input selection target
  let layout : FragmentLayout input.val selection := {}
  let anchorView := iterationCoalescedAnchorView input selection target
    hadmissible
  let sourceContext :=
    anchorView.compilerLeaf.inheritedWires.extend selection.val.anchor
  let targetContext := sourceContext.map
    (iterationCoalescedFrameIso input selection target).wires
  have bodyEq : layout.bodyContainer = spliceInput.pattern.val.diagram.root :=
    layout.bodyContainer_eq_root_of_proxyCount_eq_zero hzero
  have fragmentExact : ConcreteElaboration.WireContext.Exact
      spliceInput.pattern.val.rootWires layout.bodyContainer := by
    rw [bodyEq]
    exact ConcreteElaboration.openRootWires_exact spliceInput.pattern.property
  have targetExact : ConcreteElaboration.WireContext.Exact targetContext
      selection.val.anchor :=
    anchorView.compilerLeaf.wiresExact.mapIso
      (iterationCoalescedFrameIso input selection target)
  apply (targetExact.mem_iff _).2
  apply fragmentWireOrigin_scope_encloses_anchor input selection layout
  apply (fragmentExact.mem_iff _).1
  apply List.mem_append.mpr
  exact Or.inl (List.get_mem _ index)

/-- Canonical anchor-context index of an exposed wire of the empty-spine
extracted root. -/
noncomputable def iterationRootAnchorIndex
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hzero : (iterationInput input selection target).binderSpine.proxyCount =
      0)
    (index : Fin
      (iterationInput input selection target).pattern.val.exposedWires.length) :
    Fin (((iterationCoalescedAnchorView input selection target hadmissible)
      |>.compilerLeaf.inheritedWires.extend selection.val.anchor).map
        (iterationCoalescedFrameIso input selection target).wires).length :=
  Classical.choose (indexOf?_complete
    (iterationRootAnchorMember input selection target hadmissible hzero index))

theorem iterationRootAnchorIndex_get
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hzero : (iterationInput input selection target).binderSpine.proxyCount =
      0)
    (index : Fin
      (iterationInput input selection target).pattern.val.exposedWires.length) :
    (((iterationCoalescedAnchorView input selection target hadmissible)
      |>.compilerLeaf.inheritedWires.extend selection.val.anchor).map
        (iterationCoalescedFrameIso input selection target).wires).get
          (iterationRootAnchorIndex input selection target hadmissible hzero
            index) =
      input.val.fragmentWireOrigin selection
        ({} : FragmentLayout input.val selection)
        ((iterationInput input selection target).pattern.val.exposedWires.get
          index) := by
  classical
  unfold iterationRootAnchorIndex
  exact indexOf?_sound (Classical.choose_spec (indexOf?_complete
    (iterationRootAnchorMember input selection target hadmissible hzero index)))

theorem iterationRootAnchorIndex_related
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hzero : (iterationInput input selection target).binderSpine.proxyCount =
      0)
    (index : Fin
      (iterationInput input selection target).pattern.val.exposedWires.length) :
    (extractionContextRelation input selection
      ({} : FragmentLayout input.val selection)
      (iterationInput input selection target).pattern.val.exposedWires
      (((iterationCoalescedAnchorView input selection target hadmissible)
        |>.compilerLeaf.inheritedWires.extend selection.val.anchor).map
          (iterationCoalescedFrameIso input selection target).wires)
    ).Rel index (iterationRootAnchorIndex input selection target hadmissible
      hzero index) := by
  unfold extractionContextRelation
  exact (iterationRootAnchorIndex_get input selection target hadmissible hzero
    index).symm

/-- Empty-spine counterpart of `partitionedRoute_copyTransport`: the selected
anchor supplies the extracted open root at every route-reachable valuation. -/
theorem partitionedRoute_rootCopyTransport
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hzero : (iterationInput input selection target).binderSpine.proxyCount =
      0)
    {selectedItems : ItemSeq signature
      ((iterationCoalescedAnchorView input selection target hadmissible)
        |>.compilerLeaf.inheritedWires.extend selection.val.anchor).length
      (iterationCoalescedAnchorView input selection target hadmissible
        ).focus.holeRels}
    (selectedCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature
          (iterationInput input selection target).coalesceFrameRaw
          (ConcreteElaboration.compileRegion? signature
            (iterationInput input selection target).coalesceFrameRaw
            (iterationCoalescedAnchorView input selection target hadmissible
              ).compilerLeaf.fuel)
          ((iterationCoalescedAnchorView input selection target hadmissible)
            |>.compilerLeaf.inheritedWires.extend selection.val.anchor)
          (iterationCoalescedAnchorView input selection target hadmissible
            ).compilerLeaf.binders
          (selectedOccurrences input.val selection) = some selectedItems)
    {keptItems : ItemSeq signature
      ((iterationCoalescedAnchorView input selection target hadmissible)
        |>.compilerLeaf.inheritedWires.extend selection.val.anchor).length
      (iterationCoalescedAnchorView input selection target hadmissible
        ).focus.holeRels}
    {path : List Nat}
    (route : Splice.RegionRoute
      (iterationInput input selection target).coalesceFrameRaw
      selection.val.anchor target path)
    {compiledPath : List Nat}
    {witness : Region.ContextPath (Region.mk 0 keptItems) compiledPath}
    (terminal : CompiledRouteTerminal
      ((iterationInput input selection target).coalesceFrame hadmissible)
      (Splice.Region.ContextPath.CompilerLeaf.hereOfItemsComputation
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
      keptItems route compiledPath witness)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature) :
    let spliceInput := iterationInput input selection target
    let layout : FragmentLayout input.val selection := {}
    let anchorView := iterationCoalescedAnchorView input selection target
      hadmissible
    let sourceContext := anchorView.compilerLeaf.inheritedWires.extend
      selection.val.anchor
    let iso := iterationCoalescedFrameIso input selection target
    let targetContext := sourceContext.map iso.wires
    let pattern := Splice.Input.compiledSpliceOpenRootItems spliceInput.pattern
    let hostIndex := iterationRootAnchorIndex input selection target
      hadmissible hzero
    let wireEquiv : FiniteEquiv (Fin sourceContext.length)
        (Fin targetContext.length) :=
      FiniteEquiv.finCast (List.length_map iso.wires).symm
    let routeWire : Fin spliceInput.pattern.val.exposedWires.length →
        Fin witness.toFocus.holeWires := fun index =>
      Fin.cast terminal.leaf.inheritedLength
        (terminal.inheritedIndex (wireEquiv.symm (hostIndex index)))
    let routeRelation : RelationRenaming [] witness.toFocus.holeRels :=
      Splice.Input.PlugLayout.emptyRelationRenaming witness.toFocus.holeRels
    ∀ (sourceEnv : Fin sourceContext.length → model.Carrier)
      (sourceRelEnv : RelEnv model.Carrier anchorView.focus.holeRels),
      denoteRegion model named sourceEnv sourceRelEnv
          (Region.mk 0 selectedItems) →
        ∀ (holeEnv : Fin witness.toFocus.holeWires → model.Carrier)
          (holeRelEnv : RelEnv model.Carrier witness.toFocus.holeRels),
          witness.toFocus.context.Reachable sourceEnv sourceRelEnv
              holeEnv holeRelEnv →
            denoteRegion model named (holeEnv ∘ routeWire)
              (RelEnv.pullback routeRelation holeRelEnv)
              (ConcreteElaboration.finishRoot
                spliceInput.pattern.val.exposedWires
                spliceInput.pattern.val.hiddenWires pattern.items) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let layout : FragmentLayout input.val selection := {}
  let anchorView := iterationCoalescedAnchorView input selection target
    hadmissible
  let sourceContext := anchorView.compilerLeaf.inheritedWires.extend
    selection.val.anchor
  let iso := iterationCoalescedFrameIso input selection target
  let targetContext := sourceContext.map iso.wires
  let pattern := Splice.Input.compiledSpliceOpenRootItems spliceInput.pattern
  let hostIndex := iterationRootAnchorIndex input selection target
    hadmissible hzero
  let wireEquiv : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length) :=
    FiniteEquiv.finCast (List.length_map iso.wires).symm
  let routeWire : Fin spliceInput.pattern.val.exposedWires.length →
      Fin witness.toFocus.holeWires := fun index =>
    Fin.cast terminal.leaf.inheritedLength
      (terminal.inheritedIndex (wireEquiv.symm (hostIndex index)))
  let routeRelation : RelationRenaming [] witness.toFocus.holeRels :=
    Splice.Input.PlugLayout.emptyRelationRenaming witness.toFocus.holeRels
  obtain ⟨semanticItems, semanticCompiled, selectedSemantic⟩ :=
    coalescedAnchorSelected_entails_root input selection target hadmissible
      hzero
  have itemsEq : semanticItems = selectedItems := by
    exact Option.some.inj (semanticCompiled.symm.trans selectedCompiled)
  subst semanticItems
  intro sourceEnv sourceRelEnv selectedDenotes holeEnv holeRelEnv reachable
  have outerValues := reachable.outerWire
  have environments :
      (extractionContextRelation input selection layout
        spliceInput.pattern.val.exposedWires targetContext).EnvironmentsAgree
        (holeEnv ∘ routeWire)
        (fun index => sourceEnv (wireEquiv.symm index)) := by
    intro patternIndex targetIndex related
    have targetExact : ConcreteElaboration.WireContext.Exact targetContext
        selection.val.anchor := anchorView.compilerLeaf.wiresExact.mapIso iso
    have targetIndexEq : hostIndex patternIndex = targetIndex := by
      apply Fin.ext
      apply (List.getElem_inj targetExact.nodup).mp
      have chosen := iterationRootAnchorIndex_related input selection target
        hadmissible hzero patternIndex
      exact chosen.symm.trans related
    subst targetIndex
    change holeEnv
        (Fin.cast terminal.leaf.inheritedLength
          (terminal.inheritedIndex (wireEquiv.symm (hostIndex patternIndex)))) =
      sourceEnv (wireEquiv.symm (hostIndex patternIndex))
    have intrinsic := terminal.inheritedIndex_intrinsic
      (wireEquiv.symm (hostIndex patternIndex))
    have retained := congrFun outerValues
      (wireEquiv.symm (hostIndex patternIndex))
    exact (congrArg holeEnv intrinsic).trans retained
  have renamedMaterial := selectedSemantic model named sourceEnv sourceRelEnv
    (holeEnv ∘ routeWire) environments
    ((denoteRegion_mk_zero_iff model named sourceEnv sourceRelEnv
      selectedItems).1 selectedDenotes)
  let anchorRelation : RelationRenaming [] anchorView.focus.holeRels :=
    Splice.Input.PlugLayout.emptyRelationRenaming anchorView.focus.holeRels
  have rawMaterial :=
    (denoteRegion_renameRelations model named anchorRelation
      (RelEnv.pullback anchorRelation sourceRelEnv) sourceRelEnv
      (RelEnv.pullback_agrees anchorRelation sourceRelEnv)
      (holeEnv ∘ routeWire)
      (ConcreteElaboration.finishRoot spliceInput.pattern.val.exposedWires
        spliceInput.pattern.val.hiddenWires pattern.items)).mp renamedMaterial
  have emptyPulled : RelEnv.pullback anchorRelation sourceRelEnv =
      RelEnv.pullback routeRelation holeRelEnv := by
    apply RelEnv.eq_of_lookup
    intro arity relation
    exact Fin.elim0 relation.index
  exact emptyPulled ▸ rawMaterial

/-- Contraction at the retained route for an empty binder spine.  The copied
material is the compiled open root, with exposed wires mapped into the route
hole and hidden root wires left existential. -/
theorem partitionedRoute_rootSplice_equiv
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hzero : (iterationInput input selection target).binderSpine.proxyCount =
      0)
    {selectedItems keptItems : ItemSeq signature
      ((iterationCoalescedAnchorView input selection target hadmissible)
        |>.compilerLeaf.inheritedWires.extend selection.val.anchor).length
      (iterationCoalescedAnchorView input selection target hadmissible
        ).focus.holeRels}
    (selectedCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature
          (iterationInput input selection target).coalesceFrameRaw
          (ConcreteElaboration.compileRegion? signature
            (iterationInput input selection target).coalesceFrameRaw
            (iterationCoalescedAnchorView input selection target hadmissible
              ).compilerLeaf.fuel)
          ((iterationCoalescedAnchorView input selection target hadmissible)
            |>.compilerLeaf.inheritedWires.extend selection.val.anchor)
          (iterationCoalescedAnchorView input selection target hadmissible
            ).compilerLeaf.binders
          (selectedOccurrences input.val selection) = some selectedItems)
    {path : List Nat}
    (route : Splice.RegionRoute
      (iterationInput input selection target).coalesceFrameRaw
      selection.val.anchor target path)
    {compiledPath : List Nat}
    {witness : Region.ContextPath (Region.mk 0 keptItems) compiledPath}
    (terminal : CompiledRouteTerminal
      ((iterationInput input selection target).coalesceFrame hadmissible)
      (Splice.Region.ContextPath.CompilerLeaf.hereOfItemsComputation
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
      keptItems route compiledPath witness)
    {hostLocal : Nat}
    {hostItems : ItemSeq signature (witness.toFocus.holeWires + hostLocal)
      witness.toFocus.holeRels}
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceEnv : Fin ((iterationCoalescedAnchorView input selection target
      hadmissible).compilerLeaf.inheritedWires.extend
        selection.val.anchor).length → model.Carrier)
    (sourceRelEnv : RelEnv model.Carrier
      (iterationCoalescedAnchorView input selection target hadmissible
        ).focus.holeRels) :
    let spliceInput := iterationInput input selection target
    let anchorView := iterationCoalescedAnchorView input selection target
      hadmissible
    let sourceContext := anchorView.compilerLeaf.inheritedWires.extend
      selection.val.anchor
    let iso := iterationCoalescedFrameIso input selection target
    let targetContext := sourceContext.map iso.wires
    let pattern := Splice.Input.compiledSpliceOpenRootItems spliceInput.pattern
    let hostIndex := iterationRootAnchorIndex input selection target
      hadmissible hzero
    let wireEquiv : FiniteEquiv (Fin sourceContext.length)
        (Fin targetContext.length) :=
      FiniteEquiv.finCast (List.length_map iso.wires).symm
    let routeWire : Fin spliceInput.pattern.val.exposedWires.length →
        Fin witness.toFocus.holeWires := fun index =>
      Fin.cast terminal.leaf.inheritedLength
        (terminal.inheritedIndex (wireEquiv.symm (hostIndex index)))
    let wireMap : Fin spliceInput.pattern.val.exposedWires.length →
        Fin (witness.toFocus.holeWires + hostLocal) := fun index =>
      Fin.castAdd hostLocal (routeWire index)
    let relationMap : RelationRenaming [] witness.toFocus.holeRels :=
      Splice.Input.PlugLayout.emptyRelationRenaming witness.toFocus.holeRels
    let material := ConcreteElaboration.finishRoot
      spliceInput.pattern.val.exposedWires spliceInput.pattern.val.hiddenWires
      pattern.items
    denoteRegion model named sourceEnv sourceRelEnv
        ((Region.mk 0 selectedItems).conjoin
          (witness.toFocus.context.fill (Region.mk hostLocal hostItems))) ↔
      denoteRegion model named sourceEnv sourceRelEnv
        ((Region.mk 0 selectedItems).conjoin
          (witness.toFocus.context.fill
            (Region.spliceAt hostLocal hostItems material wireMap
              relationMap))) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let anchorView := iterationCoalescedAnchorView input selection target
    hadmissible
  let sourceContext := anchorView.compilerLeaf.inheritedWires.extend
    selection.val.anchor
  let iso := iterationCoalescedFrameIso input selection target
  let targetContext := sourceContext.map iso.wires
  let pattern := Splice.Input.compiledSpliceOpenRootItems spliceInput.pattern
  let hostIndex := iterationRootAnchorIndex input selection target
    hadmissible hzero
  let wireEquiv : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length) :=
    FiniteEquiv.finCast (List.length_map iso.wires).symm
  let routeWire : Fin spliceInput.pattern.val.exposedWires.length →
      Fin witness.toFocus.holeWires := fun index =>
    Fin.cast terminal.leaf.inheritedLength
      (terminal.inheritedIndex (wireEquiv.symm (hostIndex index)))
  let wireMap : Fin spliceInput.pattern.val.exposedWires.length →
      Fin (witness.toFocus.holeWires + hostLocal) := fun index =>
    Fin.castAdd hostLocal (routeWire index)
  let relationMap : RelationRenaming [] witness.toFocus.holeRels :=
    Splice.Input.PlugLayout.emptyRelationRenaming witness.toFocus.holeRels
  let material := ConcreteElaboration.finishRoot
    spliceInput.pattern.val.exposedWires spliceInput.pattern.val.hiddenWires
    pattern.items
  have copyTransport := partitionedRoute_rootCopyTransport input selection
    target hadmissible hzero selectedCompiled route terminal model named
  have contraction := ancestorSpliceCopy_sound
    (.hole : DiagramContext signature sourceContext.length
      sourceContext.length anchorView.focus.holeRels anchorView.focus.holeRels)
    witness.toFocus.context (Region.mk 0 selectedItems) hostLocal hostItems
    material wireMap relationMap model named sourceEnv sourceRelEnv
    (by
      intro ancestorEnv ancestorRelEnv ancestorDenotes holeEnv holeRelEnv
        reachable hostEnv hostDenotes
      have supplied := copyTransport ancestorEnv ancestorRelEnv ancestorDenotes
        holeEnv holeRelEnv reachable
      have envEq : extendWireEnv holeEnv hostEnv ∘ wireMap =
          holeEnv ∘ routeWire := by
        funext index
        simp [wireMap, extendWireEnv]
      rw [envEq]
      change denoteRegion model named (holeEnv ∘ routeWire)
        (RelEnv.pullback relationMap holeRelEnv) material
      exact supplied)
  exact contraction

/-- The selected anchor block supplies the extracted terminal material under
every valuation reachable through the retained route.  The wire and relation
maps in the conclusion are the route-native factors later identified with the
maps used by the executable splice compiler. -/
theorem partitionedRoute_copyTransport
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    {selectedItems : ItemSeq signature
      ((iterationCoalescedAnchorView input selection target hadmissible)
        |>.compilerLeaf.inheritedWires.extend selection.val.anchor).length
      (iterationCoalescedAnchorView input selection target hadmissible
        ).focus.holeRels}
    (selectedCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature
          (iterationInput input selection target).coalesceFrameRaw
          (ConcreteElaboration.compileRegion? signature
            (iterationInput input selection target).coalesceFrameRaw
            (iterationCoalescedAnchorView input selection target hadmissible
              ).compilerLeaf.fuel)
          ((iterationCoalescedAnchorView input selection target hadmissible)
            |>.compilerLeaf.inheritedWires.extend selection.val.anchor)
          (iterationCoalescedAnchorView input selection target hadmissible
            ).compilerLeaf.binders
          (selectedOccurrences input.val selection) = some selectedItems)
    {keptItems : ItemSeq signature
      ((iterationCoalescedAnchorView input selection target hadmissible)
        |>.compilerLeaf.inheritedWires.extend selection.val.anchor).length
      (iterationCoalescedAnchorView input selection target hadmissible
        ).focus.holeRels}
    {path : List Nat}
    (route : Splice.RegionRoute
      (iterationInput input selection target).coalesceFrameRaw
      selection.val.anchor target path)
    {compiledPath : List Nat}
    {witness : Region.ContextPath (Region.mk 0 keptItems) compiledPath}
    (terminal : CompiledRouteTerminal
      ((iterationInput input selection target).coalesceFrame hadmissible)
      (Splice.Region.ContextPath.CompilerLeaf.hereOfItemsComputation
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
      keptItems route compiledPath witness)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature) :
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
    let targetCover : targetBinders.Covers selection.val.anchor :=
      sourceLeaf.bindersCover.mapIso iso (by intro binder; rfl)
    let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
    let binderWitness := ExtractionBinderWitness.terminal input selection layout
      pattern.leaf.binders pattern.leaf.binderEnumeration targetBinders
      targetCover
    let hostIndex := iterationTerminalAnchorIndex input selection target
      hadmissible hnonempty
    let wireEquiv : FiniteEquiv (Fin sourceContext.length)
        (Fin targetContext.length) :=
      FiniteEquiv.finCast (List.length_map iso.wires).symm
    let routeWire : Fin pattern.leaf.inheritedWires.length →
        Fin witness.toFocus.holeWires := fun index =>
      Fin.cast terminal.leaf.inheritedLength
        (terminal.inheritedIndex (wireEquiv.symm (hostIndex index)))
    let routeRelation : RelationRenaming pattern.witness.toFocus.holeRels
        witness.toFocus.holeRels := fun {arity} relation =>
      witness.toFocus.context.outerRelation
        (binderWitness.relationMap relation)
    ∀ (sourceEnv : Fin sourceContext.length → model.Carrier)
      (sourceRelEnv : RelEnv model.Carrier anchorView.focus.holeRels),
      denoteRegion model named sourceEnv sourceRelEnv
          (Region.mk 0 selectedItems) →
        ∀ (holeEnv : Fin witness.toFocus.holeWires → model.Carrier)
          (holeRelEnv : RelEnv model.Carrier witness.toFocus.holeRels),
          witness.toFocus.context.Reachable sourceEnv sourceRelEnv
              holeEnv holeRelEnv →
            denoteRegion model named (holeEnv ∘ routeWire)
              (RelEnv.pullback routeRelation holeRelEnv)
              (ConcreteElaboration.finishRegion spliceInput.pattern.val.diagram
                pattern.leaf.inheritedWires spliceInput.binderSpine.bodyContainer
                pattern.leaf.items) := by
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
  have binderAgreement : ConcreteElaboration.BinderContextsAgree iso
      sourceLeaf.binders targetBinders := by
    intro binder
    rfl
  let targetCover : targetBinders.Covers selection.val.anchor :=
    sourceLeaf.bindersCover.mapIso iso binderAgreement
  let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
  let binderWitness := ExtractionBinderWitness.terminal input selection layout
    pattern.leaf.binders pattern.leaf.binderEnumeration targetBinders
    targetCover
  let hostIndex := iterationTerminalAnchorIndex input selection target
    hadmissible hnonempty
  let wireEquiv : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length) :=
    FiniteEquiv.finCast (List.length_map iso.wires).symm
  let routeWire : Fin pattern.leaf.inheritedWires.length →
      Fin witness.toFocus.holeWires := fun index =>
    Fin.cast terminal.leaf.inheritedLength
      (terminal.inheritedIndex (wireEquiv.symm (hostIndex index)))
  let routeRelation : RelationRenaming pattern.witness.toFocus.holeRels
      witness.toFocus.holeRels := fun {arity} relation =>
    witness.toFocus.context.outerRelation
      (binderWitness.relationMap relation)
  obtain ⟨semanticItems, semanticCompiled, selectedSemantic⟩ :=
    coalescedAnchorSelected_entails_terminal input selection target hadmissible
      hnonempty
  have itemsEq : semanticItems = selectedItems := by
    exact Option.some.inj (semanticCompiled.symm.trans selectedCompiled)
  subst semanticItems
  intro sourceEnv sourceRelEnv selectedDenotes holeEnv holeRelEnv reachable
  have outerValues := reachable.outerWire
  have environments :
      (extractionContextRelation input selection layout
        pattern.leaf.inheritedWires targetContext).EnvironmentsAgree
        (holeEnv ∘ routeWire)
        (fun index => sourceEnv (wireEquiv.symm index)) := by
    intro patternIndex targetIndex related
    have targetExact : ConcreteElaboration.WireContext.Exact targetContext
        selection.val.anchor := sourceLeaf.wiresExact.mapIso iso
    have targetIndexEq : hostIndex patternIndex = targetIndex := by
      apply Fin.ext
      apply (List.getElem_inj targetExact.nodup).mp
      have chosen := iterationTerminalAnchorIndex_related input selection target
        hadmissible hnonempty patternIndex
      exact chosen.symm.trans related
    subst targetIndex
    change holeEnv
        (Fin.cast terminal.leaf.inheritedLength
          (terminal.inheritedIndex (wireEquiv.symm (hostIndex patternIndex)))) =
      sourceEnv (wireEquiv.symm (hostIndex patternIndex))
    have intrinsic := terminal.inheritedIndex_intrinsic
      (wireEquiv.symm (hostIndex patternIndex))
    have retained := congrFun outerValues
      (wireEquiv.symm (hostIndex patternIndex))
    exact (congrArg holeEnv intrinsic).trans retained
  have renamedMaterial := selectedSemantic model named sourceEnv sourceRelEnv
    (holeEnv ∘ routeWire) environments
    ((denoteRegion_mk_zero_iff model named sourceEnv sourceRelEnv
      selectedItems).1 selectedDenotes)
  have anchorPulled : RelEnv.pullback binderWitness.relationMap sourceRelEnv =
      RelEnv.pullback routeRelation holeRelEnv := by
    apply RelEnv.eq_of_lookup
    intro arity relation
    have routePull := RelEnv.pullback_agrees routeRelation holeRelEnv
      arity relation
    have binderPull := RelEnv.pullback_agrees binderWitness.relationMap
      sourceRelEnv arity relation
    have retained := reachable.outerRelation arity
      (binderWitness.relationMap relation)
    exact binderPull.trans (retained.trans routePull.symm)
  have rawMaterial :=
    (denoteRegion_renameRelations model named binderWitness.relationMap
      (RelEnv.pullback binderWitness.relationMap sourceRelEnv) sourceRelEnv
      (RelEnv.pullback_agrees binderWitness.relationMap sourceRelEnv)
      (holeEnv ∘ routeWire)
      (ConcreteElaboration.finishRegion spliceInput.pattern.val.diagram
        pattern.leaf.inheritedWires spliceInput.binderSpine.bodyContainer
        pattern.leaf.items)).mp renamedMaterial
  exact anchorPulled ▸ rawMaterial

/-- Contraction at the retained route's actual terminal body.  This is the
semantic iteration law before the final compiler-presentation isomorphism:
the selected ancestor remains present while an identical extracted copy is
inserted at the descendant. -/
theorem partitionedRoute_splice_equiv
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (target : Fin input.val.regionCount)
    (hadmissible : (iterationInput input selection target).Admissible)
    (hnonempty : (iterationInput input selection target).binderSpine.proxyCount
      ≠ 0)
    {selectedItems keptItems : ItemSeq signature
      ((iterationCoalescedAnchorView input selection target hadmissible)
        |>.compilerLeaf.inheritedWires.extend selection.val.anchor).length
      (iterationCoalescedAnchorView input selection target hadmissible
        ).focus.holeRels}
    (selectedCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature
          (iterationInput input selection target).coalesceFrameRaw
          (ConcreteElaboration.compileRegion? signature
            (iterationInput input selection target).coalesceFrameRaw
            (iterationCoalescedAnchorView input selection target hadmissible
              ).compilerLeaf.fuel)
          ((iterationCoalescedAnchorView input selection target hadmissible)
            |>.compilerLeaf.inheritedWires.extend selection.val.anchor)
          (iterationCoalescedAnchorView input selection target hadmissible
            ).compilerLeaf.binders
          (selectedOccurrences input.val selection) = some selectedItems)
    {path : List Nat}
    (route : Splice.RegionRoute
      (iterationInput input selection target).coalesceFrameRaw
      selection.val.anchor target path)
    {compiledPath : List Nat}
    {witness : Region.ContextPath (Region.mk 0 keptItems) compiledPath}
    (terminal : CompiledRouteTerminal
      ((iterationInput input selection target).coalesceFrame hadmissible)
      (Splice.Region.ContextPath.CompilerLeaf.hereOfItemsComputation
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
      keptItems route compiledPath witness)
    {hostLocal : Nat}
    {hostItems : ItemSeq signature (witness.toFocus.holeWires + hostLocal)
      witness.toFocus.holeRels}
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceEnv : Fin ((iterationCoalescedAnchorView input selection target
      hadmissible).compilerLeaf.inheritedWires.extend
        selection.val.anchor).length → model.Carrier)
    (sourceRelEnv : RelEnv model.Carrier
      (iterationCoalescedAnchorView input selection target hadmissible
        ).focus.holeRels) :
    let spliceInput := iterationInput input selection target
    let layout : FragmentLayout input.val selection := {}
    let anchorView := iterationCoalescedAnchorView input selection target
      hadmissible
    let sourceContext :=
      anchorView.compilerLeaf.inheritedWires.extend selection.val.anchor
    let iso := iterationCoalescedFrameIso input selection target
    let targetContext := sourceContext.map iso.wires
    let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
    let targetBinders : ConcreteElaboration.BinderContext input.val
        anchorView.focus.holeRels := fun binder =>
      anchorView.compilerLeaf.binders binder
    let targetCover : targetBinders.Covers selection.val.anchor :=
      anchorView.compilerLeaf.bindersCover.mapIso iso (by intro binder; rfl)
    let binderWitness := ExtractionBinderWitness.terminal input selection layout
      pattern.leaf.binders pattern.leaf.binderEnumeration targetBinders
      targetCover
    let hostIndex := iterationTerminalAnchorIndex input selection target
      hadmissible hnonempty
    let wireEquiv : FiniteEquiv (Fin sourceContext.length)
        (Fin targetContext.length) :=
      FiniteEquiv.finCast (List.length_map iso.wires).symm
    let routeWire : Fin pattern.leaf.inheritedWires.length →
        Fin witness.toFocus.holeWires := fun index =>
      Fin.cast terminal.leaf.inheritedLength
        (terminal.inheritedIndex (wireEquiv.symm (hostIndex index)))
    let wireMap : Fin pattern.leaf.inheritedWires.length →
        Fin (witness.toFocus.holeWires + hostLocal) := fun index =>
      Fin.castAdd hostLocal (routeWire index)
    let relationMap : RelationRenaming pattern.witness.toFocus.holeRels
        witness.toFocus.holeRels := fun {arity} relation =>
      witness.toFocus.context.outerRelation
        (binderWitness.relationMap relation)
    let material := ConcreteElaboration.finishRegion
      spliceInput.pattern.val.diagram pattern.leaf.inheritedWires
      spliceInput.binderSpine.bodyContainer pattern.leaf.items
    denoteRegion model named sourceEnv sourceRelEnv
        ((Region.mk 0 selectedItems).conjoin
          (witness.toFocus.context.fill (Region.mk hostLocal hostItems))) ↔
      denoteRegion model named sourceEnv sourceRelEnv
        ((Region.mk 0 selectedItems).conjoin
          (witness.toFocus.context.fill
            (Region.spliceAt hostLocal hostItems material wireMap
              relationMap))) := by
  dsimp only
  let spliceInput := iterationInput input selection target
  let layout : FragmentLayout input.val selection := {}
  let anchorView := iterationCoalescedAnchorView input selection target
    hadmissible
  let sourceContext :=
    anchorView.compilerLeaf.inheritedWires.extend selection.val.anchor
  let iso := iterationCoalescedFrameIso input selection target
  let targetContext := sourceContext.map iso.wires
  let pattern := Splice.Input.compiledSpliceTerminalView spliceInput hnonempty
  let targetBinders : ConcreteElaboration.BinderContext input.val
      anchorView.focus.holeRels := fun binder =>
    anchorView.compilerLeaf.binders binder
  have binderAgreement : ConcreteElaboration.BinderContextsAgree iso
      anchorView.compilerLeaf.binders targetBinders := by
    intro binder
    rfl
  let targetCover : targetBinders.Covers selection.val.anchor :=
    anchorView.compilerLeaf.bindersCover.mapIso iso binderAgreement
  let binderWitness := ExtractionBinderWitness.terminal input selection layout
    pattern.leaf.binders pattern.leaf.binderEnumeration targetBinders
    targetCover
  let hostIndex := iterationTerminalAnchorIndex input selection target
    hadmissible hnonempty
  let wireEquiv : FiniteEquiv (Fin sourceContext.length)
      (Fin targetContext.length) :=
    FiniteEquiv.finCast (List.length_map iso.wires).symm
  let routeWire : Fin pattern.leaf.inheritedWires.length →
      Fin witness.toFocus.holeWires := fun index =>
    Fin.cast terminal.leaf.inheritedLength
      (terminal.inheritedIndex (wireEquiv.symm (hostIndex index)))
  let wireMap : Fin pattern.leaf.inheritedWires.length →
      Fin (witness.toFocus.holeWires + hostLocal) := fun index =>
    Fin.castAdd hostLocal (routeWire index)
  let relationMap : RelationRenaming pattern.witness.toFocus.holeRels
      witness.toFocus.holeRels := fun {arity} relation =>
    witness.toFocus.context.outerRelation
      (binderWitness.relationMap relation)
  let material := ConcreteElaboration.finishRegion
    spliceInput.pattern.val.diagram pattern.leaf.inheritedWires
    spliceInput.binderSpine.bodyContainer pattern.leaf.items
  have copyTransport := partitionedRoute_copyTransport input selection target
    hadmissible hnonempty selectedCompiled route terminal model named
  have contraction := ancestorSpliceCopy_sound
    (.hole : DiagramContext signature sourceContext.length
      sourceContext.length anchorView.focus.holeRels anchorView.focus.holeRels)
    witness.toFocus.context (Region.mk 0 selectedItems) hostLocal hostItems
    material wireMap relationMap model named sourceEnv sourceRelEnv
    (by
      intro ancestorEnv ancestorRelEnv ancestorDenotes holeEnv holeRelEnv
        reachable hostEnv hostDenotes
      have supplied := copyTransport ancestorEnv ancestorRelEnv ancestorDenotes
        holeEnv holeRelEnv reachable
      have envEq : extendWireEnv holeEnv hostEnv ∘ wireMap =
          holeEnv ∘ routeWire := by
        funext index
        simp [wireMap, extendWireEnv]
      rw [envEq]
      change denoteRegion model named (holeEnv ∘ routeWire)
        (RelEnv.pullback relationMap holeRelEnv) material
      exact supplied)
  exact contraction

end VisualProof.Rule.IterationSoundness
