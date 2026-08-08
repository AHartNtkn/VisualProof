import VisualProof.Refinement.Implementation.DoubleCutIntroCompile
import VisualProof.Concrete.Subgraph.Splice.Input.Route
import VisualProof.Concrete.Subgraph.Splice.Input.Alignment.Nested

namespace VisualProof.Refinement.Implementation.DoubleCutIntroContext

open VisualProof
open VisualProof.Concrete
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Refinement.Implementation.DoubleCutTransport
open VisualProof.Refinement.Implementation.DoubleCutIntroPartition

noncomputable def compilerBodyOuterWire
    {sourceOuter targetOuter : Nat} {rels : RelCtx}
    {sourceBody : Region sourceOuter rels}
    {targetBody : Region targetOuter rels}
    (sourceState : Concrete.Splice.Region.ContextPath.CompilerLeaf sourceDiagram
      sourceRegion (.here sourceBody))
    (targetState : Concrete.Splice.Region.ContextPath.CompilerLeaf targetDiagram
      targetRegion (.here targetBody))
    (inherited : FiniteEquiv (Fin sourceState.inheritedWires.length)
      (Fin targetState.inheritedWires.length)) :
    FiniteEquiv (Fin sourceOuter) (Fin targetOuter) :=
  (FiniteEquiv.finCast sourceState.inheritedLength).symm |>.trans
    (inherited.trans (FiniteEquiv.finCast targetState.inheritedLength))

private theorem list_get_cast
    {source target : List α} (equality : source = target)
    (index : Fin source.length) :
    target.get (Fin.cast (congrArg List.length equality) index) =
      source.get index := by
  subst target
  rfl

/-- The enclosing concrete route is unchanged by double-cut introduction;
only its region indices are lifted past the two fresh regions. -/
private def route_lift_aux
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    (wellFormed : input.WellFormed)
    {start target : Fin input.regionCount} {path : List Nat}
    (route : Concrete.Splice.RegionRoute input start target path)
    (targetEq : target = selection.val.anchor) :
    Concrete.Splice.RegionRoute (doubleCutIntroRaw input selection)
      (Fin.castAdd 2 start) (Fin.castAdd 2 target) path := by
  induction route with
  | here region => exact .here _
  | @step start child target rest parent position positionEq tail induction =>
      have startNe : start ≠ selection.val.anchor := by
        intro equality
        subst start
        exact Concrete.Elaboration.checked_direct_child_not_encloses_parent
          wellFormed parent
          (targetEq ▸ Concrete.Splice.Input.RegionRoute.encloses tail wellFormed)
      have childUnselected : child ∉ selection.val.childRoots := by
        intro selected
        have direct := selection.property.childRoots_direct child selected
        exact Concrete.Elaboration.checked_direct_child_not_encloses_parent
          wellFormed direct
          (targetEq ▸ Concrete.Splice.Input.RegionRoute.encloses tail wellFormed)
      have targetParent :
          ((doubleCutIntroRaw input selection).regions
            (Fin.castAdd 2 child)).parent? = some (Fin.castAdd 2 start) := by
        rw [oldRegion_parent, if_neg childUnselected, parent]
        rfl
      let targetPosition : Fin
          (Concrete.Elaboration.localOccurrences
            (doubleCutIntroRaw input selection) (Fin.castAdd 2 start)).length :=
        Fin.cast (by simp [regular_localOccurrences input selection start startNe])
          position
      have targetGet :
          (Concrete.Elaboration.localOccurrences
            (doubleCutIntroRaw input selection)
            (Fin.castAdd 2 start)).get targetPosition =
              .child (Fin.castAdd 2 child) := by
        have sourceGet := indexOf?_sound positionEq
        simpa [targetPosition,
          regular_localOccurrences input selection start startNe,
          liftOccurrence] using
          congrArg (liftOccurrence input) sourceGet
      have targetPositionEq :
          indexOf? (Concrete.Elaboration.localOccurrences
            (doubleCutIntroRaw input selection) (Fin.castAdd 2 start))
            (.child (Fin.castAdd 2 child)) = some targetPosition := by
        rw [← targetGet]
        exact indexOf?_get_eq_some_of_nodup
          (Concrete.Elaboration.localOccurrences_nodup _ _) targetPosition
      have positionVal : targetPosition.val = position.val := rfl
      simpa [positionVal] using Concrete.Splice.RegionRoute.step targetParent
        targetPosition targetPositionEq (induction targetEq)

theorem route_lift
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    (wellFormed : input.WellFormed)
    {start : Fin input.regionCount} {path : List Nat}
    (route : Concrete.Splice.RegionRoute input start
      selection.val.anchor path) :
    Concrete.Splice.RegionRoute (doubleCutIntroRaw input selection)
      (Fin.castAdd 2 start) (Fin.castAdd 2 selection.val.anchor) path :=
  route_lift_aux input selection wellFormed route rfl

def checkedTarget (source : Concrete.CheckedOpen)
    (selection : CheckedSelection source.val.diagram)
    (wellFormed : (DoubleCutTransport.targetOpen source.val selection).WellFormed) :
    Concrete.CheckedOpen :=
  ⟨DoubleCutTransport.targetOpen source.val selection, wellFormed⟩

/-- The lifted route is accepted by the target's actual open-root compiler.
The result retains the target context path and every compiler frame needed
for structural context alignment. -/
theorem targetTrace_complete
    (source : Concrete.CheckedOpen)
    (selection : CheckedSelection source.val.diagram)
    (targetWellFormed :
      (DoubleCutTransport.targetOpen source.val selection).WellFormed)
    (sourceView : Concrete.Splice.OpenSiteView source selection.val.anchor) :
    let target := checkedTarget source selection targetWellFormed
    let targetRoute : Concrete.Splice.RegionRoute target.val.diagram
        target.val.diagram.root (Fin.castAdd 2 selection.val.anchor)
        sourceView.path :=
      route_lift source.val.diagram selection
        source.property.diagram_well_formed sourceView.route
    Nonempty (Concrete.Splice.OpenCompilerTraceResult target targetRoute
      target.elaborate.body) := by
  dsimp only
  let target := checkedTarget source selection targetWellFormed
  let lifted := route_lift source.val.diagram selection
    source.property.diagram_well_formed sourceView.route
  let targetRoute : Concrete.Splice.RegionRoute target.val.diagram
      target.val.diagram.root (Fin.castAdd 2 selection.val.anchor)
      sourceView.path := lifted
  obtain ⟨body, compiled, elaborates⟩ :=
    Concrete.CheckedOpen.elaborate_body_computation target
  obtain ⟨result⟩ :=
    Concrete.Splice.compileOpenRoot_route_context_complete target targetRoute
      compiled
  subst body
  exact ⟨result⟩

/-- Every nonfocused compiler item in an enclosing frame is transported
structurally; the distinguished route child is left for recursive alignment. -/
theorem compilerRawFrame
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    (wellFormed : input.WellFormed)
    {region child : Fin input.regionCount} {rest : List Nat}
    (regionNe : region ≠ selection.val.anchor)
    (childParent : (input.regions child).parent? = some region)
    (position : Fin (Concrete.Elaboration.localOccurrences input region).length)
    (positionEq : indexOf?
      (Concrete.Elaboration.localOccurrences input region) (.child child) =
        some position)
    (tail : Concrete.Splice.RegionRoute input child
      selection.val.anchor rest)
    {sourceOuter targetOuter : Nat} {rels : RelCtx}
    {sourceBody : Region sourceOuter rels}
    {targetBody : Region targetOuter rels}
    (sourceState : Concrete.Splice.Region.ContextPath.CompilerLeaf input region
      (.here sourceBody))
    (targetState : Concrete.Splice.Region.ContextPath.CompilerLeaf
      (doubleCutIntroRaw input selection) (Fin.castAdd 2 region)
      (.here targetBody))
    (context : Context input selection sourceState.inheritedWires
      targetState.inheritedWires)
    (binders : Binders input selection sourceState.binders targetState.binders)
    (sourceIndex : Fin sourceState.items.length)
    (targetIndex : Fin targetState.items.length)
    (sourceIndexVal : sourceIndex.val = position.val)
    (targetIndexVal : targetIndex.val = position.val) :
    Nonempty (ItemSeqIso.Frame
      (FiniteEquiv.finCast (congrArg List.length
        (context.extend region).equality)) sourceIndex targetIndex) := by
  let sourceExtended := sourceState.inheritedWires.extend region
  let targetExtended := targetState.inheritedWires.extend (Fin.castAdd 2 region)
  let occurrences := Concrete.Elaboration.localOccurrences input region
  have sourceComputation : Concrete.Elaboration.compileOccurrencesWith? input
      (Concrete.Elaboration.compileRegion? input sourceState.fuel)
      sourceExtended sourceState.binders occurrences =
        some sourceState.items := by
    simpa [sourceExtended, occurrences] using sourceState.itemsComputation
  have targetComputation : Concrete.Elaboration.compileOccurrencesWith?
      (doubleCutIntroRaw input selection)
      (Concrete.Elaboration.compileRegion?
        (doubleCutIntroRaw input selection) targetState.fuel)
      targetExtended targetState.binders
      (occurrences.map (liftOccurrence input)) = some targetState.items := by
    simpa [targetExtended, occurrences,
      regular_localOccurrences input selection region regionNe] using
        targetState.itemsComputation
  let sourceLength := Concrete.Elaboration.compileOccurrencesWith?_length
    (Concrete.Elaboration.compileRegion? input sourceState.fuel)
    sourceExtended sourceState.binders sourceComputation
  let targetLength := Concrete.Elaboration.compileOccurrencesWith?_length
    (Concrete.Elaboration.compileRegion?
      (doubleCutIntroRaw input selection) targetState.fuel)
    targetExtended targetState.binders targetComputation
  let occurrenceLength : occurrences.length =
      (occurrences.map (liftOccurrence input)).length :=
    (List.length_map (as := occurrences) (liftOccurrence input)).symm
  let positions : FiniteEquiv (Fin sourceState.items.length)
      (Fin targetState.items.length) :=
    (FiniteEquiv.finCast sourceLength).trans
      ((FiniteEquiv.finCast occurrenceLength).trans
        (FiniteEquiv.finCast targetLength.symm))
  have mapped : positions sourceIndex = targetIndex := by
    apply Fin.ext
    simp [positions, sourceIndexVal, targetIndexVal, FiniteEquiv.finCast]
  refine ⟨{
    positions := positions
    mapped := mapped
    siblings := ?_
  }⟩
  intro index indexNe
  let occurrenceIndex : Fin occurrences.length := Fin.cast sourceLength index
  have occurrenceNe : occurrenceIndex ≠ position := by
    intro equality
    apply indexNe
    apply Fin.ext
    have values := congrArg Fin.val equality
    simpa [occurrenceIndex, sourceIndexVal] using values
  let targetOccurrenceIndex : Fin (occurrences.map (liftOccurrence input)).length :=
    Fin.cast occurrenceLength occurrenceIndex
  have sourceGet := Concrete.Elaboration.compileOccurrencesWith?_get
    (Concrete.Elaboration.compileRegion? input sourceState.fuel)
    sourceExtended sourceState.binders sourceComputation occurrenceIndex
  have targetGet := Concrete.Elaboration.compileOccurrencesWith?_get
    (Concrete.Elaboration.compileRegion?
      (doubleCutIntroRaw input selection) targetState.fuel)
    targetExtended targetState.binders targetComputation targetOccurrenceIndex
  have sourcePosition : Fin.cast sourceLength.symm occurrenceIndex = index := by
    apply Fin.ext
    rfl
  have targetPosition : Fin.cast targetLength.symm targetOccurrenceIndex =
      positions index := by
    apply Fin.ext
    rfl
  rw [sourcePosition] at sourceGet
  rw [targetPosition] at targetGet
  let occurrence := occurrences.get occurrenceIndex
  have occurrenceMem : occurrence ∈ occurrences := List.get_mem _ _
  have targetOccurrenceGet :
      (occurrences.map (liftOccurrence input)).get targetOccurrenceIndex =
        liftOccurrence input occurrence := by
    simp [targetOccurrenceIndex, occurrence]
  have targetGet' : Concrete.Elaboration.compileOccurrenceWith?
      (doubleCutIntroRaw input selection)
      (Concrete.Elaboration.compileRegion?
        (doubleCutIntroRaw input selection) targetState.fuel)
      targetExtended targetState.binders (liftOccurrence input occurrence) =
        some (targetState.items.get (positions index)) := by
    exact targetOccurrenceGet ▸ targetGet
  apply DoubleCutIntroCompile.occurrence_iso input selection
    sourceExtended targetExtended (context.extend region)
    sourceState.binders targetState.binders binders occurrence (Fin.castAdd 2)
  · intro node equality
    rw [equality] at occurrenceMem
    exact regular_node input selection region regionNe node
      ((Concrete.Elaboration.mem_localOccurrences_node input region node).1
        occurrenceMem)
  · intro sibling equality
    rw [equality] at occurrenceMem
    exact regular_region input selection region sibling regionNe
      ((Concrete.Elaboration.mem_localOccurrences_child input region sibling).1
        occurrenceMem)
  · intro childSourceRels childTargetRels childSourceBinders
      childTargetBinders childBinders sibling equality sourceSibling
      targetSibling sourceCompiled targetCompiled
    rw [equality] at occurrenceMem
    have siblingParent :=
      (Concrete.Elaboration.mem_localOccurrences_child input region sibling).1
        occurrenceMem
    have siblingNe : sibling ≠ child := by
      intro childEq
      subst sibling
      have found := indexOf?_get_eq_some_of_nodup
        (Concrete.Elaboration.localOccurrences_nodup input region)
        occurrenceIndex
      have foundChild : indexOf?
          (Concrete.Elaboration.localOccurrences input region) (.child child) =
            some occurrenceIndex := by
        rw [← equality]
        exact found
      apply occurrenceNe
      exact Option.some.inj (foundChild.symm.trans positionEq)
    have siblingAway : ¬ input.Encloses sibling selection.val.anchor :=
      Concrete.Splice.Input.PlugLayout.RegionRoute.distinctSibling_away
        wellFormed tail childParent siblingParent siblingNe
    exact DoubleCutIntroCompile.away_region_iso input selection wellFormed
      sibling siblingAway sourceExtended targetExtended
      (context.extend region) childSourceBinders childTargetBinders
      childBinders sourceCompiled targetCompiled
  · exact sourceGet
  · exact targetGet'

/-- Canonical-body form of `compilerRawFrame`, transported through the casts
performed by `finishRegion`. -/
theorem compilerLeafFrame
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    (wellFormed : input.WellFormed)
    {region child : Fin input.regionCount} {rest : List Nat}
    (regionNe : region ≠ selection.val.anchor)
    (childParent : (input.regions child).parent? = some region)
    (position : Fin (Concrete.Elaboration.localOccurrences input region).length)
    (positionEq : indexOf?
      (Concrete.Elaboration.localOccurrences input region) (.child child) =
        some position)
    (tail : Concrete.Splice.RegionRoute input child
      selection.val.anchor rest)
    {sourceOuter sourceLocal targetOuter targetLocal : Nat} {rels : RelCtx}
    {sourceItems : ItemSeq (sourceOuter + sourceLocal) rels}
    {targetItems : ItemSeq (targetOuter + targetLocal) rels}
    (sourceState : Concrete.Splice.Region.ContextPath.CompilerLeaf input region
      (.here (.mk sourceLocal sourceItems)))
    (targetState : Concrete.Splice.Region.ContextPath.CompilerLeaf
      (doubleCutIntroRaw input selection) (Fin.castAdd 2 region)
      (.here (.mk targetLocal targetItems)))
    (sourceLocalCanonical : sourceLocal =
      (Concrete.Elaboration.exactScopeWires input region).length)
    (targetLocalCanonical : targetLocal =
      (Concrete.Elaboration.exactScopeWires
        (doubleCutIntroRaw input selection) (Fin.castAdd 2 region)).length)
    (sourceItemsCanonical : HEq sourceItems sourceState.canonicalBodyItems)
    (targetItemsCanonical : HEq targetItems targetState.canonicalBodyItems)
    (context : Context input selection sourceState.inheritedWires
      targetState.inheritedWires)
    (binders : Binders input selection sourceState.binders targetState.binders)
    (sourceIndex : Fin sourceItems.length)
    (targetIndex : Fin targetItems.length)
    (sourceIndexVal : sourceIndex.val = position.val)
    (targetIndexVal : targetIndex.val = position.val) :
    let inherited := FiniteEquiv.finCast
      (congrArg List.length context.equality)
    let outerWire := compilerBodyOuterWire sourceState targetState inherited
    let localWire := (FiniteEquiv.finCast sourceLocalCanonical).trans
      ((FiniteEquiv.finCast (congrArg List.length
        (exactScopeWires input selection region).symm)).trans
        (FiniteEquiv.finCast targetLocalCanonical.symm))
    Nonempty (ItemSeqIso.Frame (extendWireEquiv outerWire localWire)
      sourceIndex targetIndex) := by
  dsimp only
  subst sourceLocal
  subst targetLocal
  let inherited := FiniteEquiv.finCast
    (congrArg List.length context.equality)
  let outerWire := compilerBodyOuterWire sourceState targetState inherited
  let sourceExtended := sourceState.inheritedWires.extend region
  let targetExtended :=
    targetState.inheritedWires.extend (Fin.castAdd 2 region)
  let extendedEquiv := FiniteEquiv.finCast
    (congrArg List.length (context.extend region).equality)
  let localWire := FiniteEquiv.finCast (congrArg List.length
    (exactScopeWires input selection region).symm)
  let sourceCast : FiniteEquiv (Fin sourceExtended.length)
      (Fin (sourceOuter +
        (Concrete.Elaboration.exactScopeWires input region).length)) :=
    (FiniteEquiv.finCast (Concrete.Elaboration.WireContext.length_extend
      sourceState.inheritedWires region)).trans
      (FiniteEquiv.finCast (congrArg
        (fun inheritedLength => inheritedLength +
          (Concrete.Elaboration.exactScopeWires input region).length)
        sourceState.inheritedLength))
  let targetCast : FiniteEquiv (Fin targetExtended.length)
      (Fin (targetOuter + (Concrete.Elaboration.exactScopeWires
        (doubleCutIntroRaw input selection) (Fin.castAdd 2 region)).length)) :=
    (FiniteEquiv.finCast (Concrete.Elaboration.WireContext.length_extend
      targetState.inheritedWires (Fin.castAdd 2 region))).trans
      (FiniteEquiv.finCast (congrArg
        (fun inheritedLength => inheritedLength +
          (Concrete.Elaboration.exactScopeWires
            (doubleCutIntroRaw input selection)
            (Fin.castAdd 2 region)).length)
        targetState.inheritedLength))
  have sourceCanonicalEq : sourceItems =
      sourceState.items.renameWires sourceCast := by
    have core := eq_of_heq sourceItemsCanonical
    rw [Concrete.Splice.Region.ContextPath.CompilerLeaf.canonicalBodyItems,
      ItemSeq.castWiresEq_eq_renameWires,
      ItemSeq.castWiresEq_eq_renameWires] at core
    exact core.trans ((ItemSeq.renameWires_comp sourceState.items _ _).trans (by
      apply congrArg (sourceState.items.renameWires ·)
      funext index
      rfl))
  have targetCanonicalEq : targetItems =
      targetState.items.renameWires targetCast := by
    have core := eq_of_heq targetItemsCanonical
    rw [Concrete.Splice.Region.ContextPath.CompilerLeaf.canonicalBodyItems,
      ItemSeq.castWiresEq_eq_renameWires,
      ItemSeq.castWiresEq_eq_renameWires] at core
    exact core.trans ((ItemSeq.renameWires_comp targetState.items _ _).trans (by
      apply congrArg (targetState.items.renameWires ·)
      funext index
      rfl))
  let sourceRenamedIndex : Fin
      (sourceState.items.renameWires sourceCast).length :=
    Fin.cast (congrArg ItemSeq.length sourceCanonicalEq) sourceIndex
  let targetRenamedIndex : Fin
      (targetState.items.renameWires targetCast).length :=
    Fin.cast (congrArg ItemSeq.length targetCanonicalEq) targetIndex
  let rawSourceIndex :=
    (sourceState.items.renameWiresPositionEquiv sourceCast).symm
      sourceRenamedIndex
  let rawTargetIndex :=
    (targetState.items.renameWiresPositionEquiv targetCast).symm
      targetRenamedIndex
  have rawSourceVal : rawSourceIndex.val = position.val := by
    simpa [rawSourceIndex, sourceRenamedIndex,
      ItemSeq.renameWiresPositionEquiv, FiniteEquiv.finCast] using sourceIndexVal
  have rawTargetVal : rawTargetIndex.val = position.val := by
    simpa [rawTargetIndex, targetRenamedIndex,
      ItemSeq.renameWiresPositionEquiv, FiniteEquiv.finCast] using targetIndexVal
  obtain ⟨rawFrame⟩ := compilerRawFrame input selection wellFormed regionNe
    childParent position positionEq tail sourceState targetState context binders
    rawSourceIndex rawTargetIndex rawSourceVal rawTargetVal
  have sourceUndo : sourceItems.renameWires sourceCast.symm =
      sourceState.items := by
    calc
      sourceItems.renameWires sourceCast.symm =
          (sourceState.items.renameWires sourceCast).renameWires
            sourceCast.symm := congrArg
              (fun items => items.renameWires sourceCast.symm) sourceCanonicalEq
      _ = sourceState.items.renameWires
          (sourceCast.symm.toFun ∘ sourceCast.toFun) :=
        ItemSeq.renameWires_comp sourceState.items sourceCast sourceCast.symm
      _ = sourceState.items := by
        have identity : sourceCast.symm.toFun ∘ sourceCast.toFun = id := by
          funext index
          exact sourceCast.left_inv index
        rw [identity]
        exact ItemSeq.renameWires_id sourceState.items
  have targetPush : targetState.items.renameWires targetCast = targetItems :=
    targetCanonicalEq.symm
  let finalWire := extendWireEquiv outerWire localWire
  have wireFactor :
      (sourceCast.symm.trans extendedEquiv).trans targetCast = finalWire := by
    have extendedEq : extendedEquiv =
        (FiniteEquiv.finCast
          (Concrete.Elaboration.WireContext.length_extend
            sourceState.inheritedWires region)).trans
          ((extendWireEquiv inherited localWire).trans
            (FiniteEquiv.finCast
              (Concrete.Elaboration.WireContext.length_extend
                targetState.inheritedWires
                (Fin.castAdd 2 region))).symm) := by
      apply FiniteEquiv.ext
      intro index
      let split := Fin.cast
        (Concrete.Elaboration.WireContext.length_extend
          sourceState.inheritedWires region) index
      have recover : Fin.cast
          (Concrete.Elaboration.WireContext.length_extend
            sourceState.inheritedWires region).symm split = index := by
        apply Fin.ext
        rfl
      rw [← recover]
      refine Fin.addCases (fun inheritedIndex => ?_)
        (fun localIndex => ?_) split
      · apply Fin.ext
        simp [extendedEquiv, inherited, localWire, extendWireEquiv,
          FiniteEquiv.finCast]
      · apply Fin.ext
        simp [extendedEquiv, inherited, localWire, extendWireEquiv,
          FiniteEquiv.finCast,
          congrArg List.length context.equality]
    have sourceChildExtended : sourceOuter +
          (Concrete.Elaboration.exactScopeWires input region).length =
        sourceExtended.length :=
      (congrArg
          (fun inheritedLength => inheritedLength +
            (Concrete.Elaboration.exactScopeWires input region).length)
          sourceState.inheritedLength).symm.trans
        (Concrete.Elaboration.WireContext.length_extend
          sourceState.inheritedWires region).symm
    have targetChildExtended : targetOuter +
          (Concrete.Elaboration.exactScopeWires
            (doubleCutIntroRaw input selection)
            (Fin.castAdd 2 region)).length = targetExtended.length :=
      (congrArg
          (fun inheritedLength => inheritedLength +
            (Concrete.Elaboration.exactScopeWires
              (doubleCutIntroRaw input selection)
              (Fin.castAdd 2 region)).length)
          targetState.inheritedLength).symm.trans
        (Concrete.Elaboration.WireContext.length_extend
          targetState.inheritedWires (Fin.castAdd 2 region)).symm
    have algebra :=
      Concrete.Splice.Input.compilerBodyOuterWire_extend_algebra
        sourceChildExtended
        (Concrete.Elaboration.WireContext.length_extend
          sourceState.inheritedWires region)
        sourceState.inheritedLength
        (rfl : sourceOuter +
          (Concrete.Elaboration.exactScopeWires input region).length = _)
        (rfl : (Concrete.Elaboration.exactScopeWires input region).length = _)
        targetChildExtended
        (Concrete.Elaboration.WireContext.length_extend
          targetState.inheritedWires (Fin.castAdd 2 region))
        targetState.inheritedLength
        (rfl : targetOuter + (Concrete.Elaboration.exactScopeWires
          (doubleCutIntroRaw input selection)
          (Fin.castAdd 2 region)).length = _)
        (rfl : (Concrete.Elaboration.exactScopeWires
          (doubleCutIntroRaw input selection)
          (Fin.castAdd 2 region)).length = _)
        inherited localWire
    simpa [sourceCast, targetCast, extendedEq, finalWire, outerWire,
      sourceExtended, targetExtended] using algebra
  obtain ⟨sourceIndex', targetIndex', sourceVal, targetVal, ⟨frame⟩⟩ :=
    ItemSeqIso.Frame.pullPush sourceCast.symm extendedEquiv targetCast
      finalWire sourceUndo targetPush wireFactor rawFrame
  have sourceIndexEq : sourceIndex' = sourceIndex := by
    apply Fin.ext
    exact sourceVal.trans (by
      change rawSourceIndex.val = sourceIndex.val
      simp [rawSourceIndex, sourceRenamedIndex,
        ItemSeq.renameWiresPositionEquiv])
  have targetIndexEq : targetIndex' = targetIndex := by
    apply Fin.ext
    exact targetVal.trans (by
      change rawTargetIndex.val = targetIndex.val
      simp [rawTargetIndex, targetRenamedIndex,
        ItemSeq.renameWiresPositionEquiv])
  subst sourceIndex'
  subst targetIndex'
  simpa only [finalWire] using ⟨frame⟩

theorem openRootRawFrame
    (source : Concrete.CheckedOpen)
    (selection : CheckedSelection source.val.diagram)
    (rootNe : source.val.diagram.root ≠ selection.val.anchor)
    (targetWellFormed :
      (DoubleCutTransport.targetOpen source.val selection).WellFormed)
    {child : Fin source.val.diagram.regionCount} {rest : List Nat}
    (childParent : (source.val.diagram.regions child).parent? =
      some source.val.diagram.root)
    (position : Fin (Concrete.Elaboration.localOccurrences
      source.val.diagram source.val.diagram.root).length)
    (positionEq : indexOf? (Concrete.Elaboration.localOccurrences
      source.val.diagram source.val.diagram.root) (.child child) =
        some position)
    (tail : Concrete.Splice.RegionRoute source.val.diagram child
      selection.val.anchor rest)
    {sourceBody targetBody : Region source.val.exposedWires.length []}
    (sourceState : Concrete.Splice.OpenRootCompilerState source sourceBody)
    (targetState : Concrete.Splice.OpenRootCompilerState
      (checkedTarget source selection targetWellFormed) targetBody)
    (sourceIndex : Fin sourceState.items.length)
    (targetIndex : Fin targetState.items.length)
    (sourceIndexVal : sourceIndex.val = position.val)
    (targetIndexVal : targetIndex.val = position.val) :
    Nonempty (ItemSeqIso.Frame
      (FiniteEquiv.finCast (congrArg List.length
        (DoubleCutTransport.targetOpen_rootWires source.val selection).symm))
      sourceIndex targetIndex) := by
  let input := source.val.diagram
  let target := checkedTarget source selection targetWellFormed
  let sourceWires := source.val.rootWires
  let targetWires := target.val.rootWires
  let occurrences := Concrete.Elaboration.localOccurrences input input.root
  have sourceComputation : Concrete.Elaboration.compileOccurrencesWith? input
      (Concrete.Elaboration.compileRegion? input input.regionCount)
      sourceWires Concrete.Elaboration.BinderContext.empty occurrences =
        some sourceState.items := by
    simpa [input, sourceWires, occurrences] using sourceState.itemsComputation
  have targetComputation : Concrete.Elaboration.compileOccurrencesWith?
      (doubleCutIntroRaw input selection)
      (Concrete.Elaboration.compileRegion? (doubleCutIntroRaw input selection)
        (doubleCutIntroRaw input selection).regionCount)
      targetWires Concrete.Elaboration.BinderContext.empty
      (occurrences.map (liftOccurrence input)) = some targetState.items := by
    simpa [target, checkedTarget, DoubleCutTransport.targetOpen, input,
      targetWires, occurrences,
      regular_localOccurrences input selection input.root rootNe] using
        targetState.itemsComputation
  let sourceLength := Concrete.Elaboration.compileOccurrencesWith?_length
    (Concrete.Elaboration.compileRegion? input input.regionCount)
    sourceWires Concrete.Elaboration.BinderContext.empty sourceComputation
  let targetLength := Concrete.Elaboration.compileOccurrencesWith?_length
    (Concrete.Elaboration.compileRegion? (doubleCutIntroRaw input selection)
      (doubleCutIntroRaw input selection).regionCount)
    targetWires Concrete.Elaboration.BinderContext.empty targetComputation
  let occurrenceLength : occurrences.length =
      (occurrences.map (liftOccurrence input)).length :=
    (List.length_map (as := occurrences) (liftOccurrence input)).symm
  let positions : FiniteEquiv (Fin sourceState.items.length)
      (Fin targetState.items.length) :=
    (FiniteEquiv.finCast sourceLength).trans
      ((FiniteEquiv.finCast occurrenceLength).trans
        (FiniteEquiv.finCast targetLength.symm))
  have mapped : positions sourceIndex = targetIndex := by
    apply Fin.ext
    simp [positions, sourceIndexVal, targetIndexVal, FiniteEquiv.finCast]
  refine ⟨{ positions := positions, mapped := mapped, siblings := ?_ }⟩
  intro index indexNe
  let occurrenceIndex : Fin occurrences.length := Fin.cast sourceLength index
  have occurrenceNe : occurrenceIndex ≠ position := by
    intro equality
    apply indexNe
    apply Fin.ext
    simpa [occurrenceIndex, sourceIndexVal] using congrArg Fin.val equality
  let targetOccurrenceIndex : Fin
      (occurrences.map (liftOccurrence input)).length :=
    Fin.cast occurrenceLength occurrenceIndex
  have sourceGet := Concrete.Elaboration.compileOccurrencesWith?_get
    (Concrete.Elaboration.compileRegion? input input.regionCount)
    sourceWires Concrete.Elaboration.BinderContext.empty sourceComputation
      occurrenceIndex
  have targetGet := Concrete.Elaboration.compileOccurrencesWith?_get
    (Concrete.Elaboration.compileRegion? (doubleCutIntroRaw input selection)
      (doubleCutIntroRaw input selection).regionCount)
    targetWires Concrete.Elaboration.BinderContext.empty targetComputation
      targetOccurrenceIndex
  have sourcePosition : Fin.cast sourceLength.symm occurrenceIndex = index := by
    apply Fin.ext
    rfl
  have targetPosition : Fin.cast targetLength.symm targetOccurrenceIndex =
      positions index := by
    apply Fin.ext
    rfl
  rw [sourcePosition] at sourceGet
  rw [targetPosition] at targetGet
  let occurrence := occurrences.get occurrenceIndex
  have occurrenceMem : occurrence ∈ occurrences := List.get_mem _ _
  have targetOccurrenceGet :
      (occurrences.map (liftOccurrence input)).get targetOccurrenceIndex =
        liftOccurrence input occurrence := by
    simp [targetOccurrenceIndex, occurrence]
  have targetGet' : Concrete.Elaboration.compileOccurrenceWith?
      (doubleCutIntroRaw input selection)
      (Concrete.Elaboration.compileRegion? (doubleCutIntroRaw input selection)
        (doubleCutIntroRaw input selection).regionCount)
      targetWires Concrete.Elaboration.BinderContext.empty
      (liftOccurrence input occurrence) =
        some (targetState.items.get (positions index)) := by
    exact targetOccurrenceGet ▸ targetGet
  let context : Context input selection sourceWires targetWires :=
    ⟨DoubleCutTransport.targetOpen_rootWires source.val selection |>.symm⟩
  let binders : Binders input selection
      (Concrete.Elaboration.BinderContext.empty :
        Concrete.Elaboration.BinderContext input [])
      (Concrete.Elaboration.BinderContext.empty :
        Concrete.Elaboration.BinderContext (doubleCutIntroRaw input selection)
          []) := ⟨rfl, fun region => by
            simp [Concrete.Elaboration.BinderContext.empty]⟩
  apply DoubleCutIntroCompile.occurrence_iso input selection sourceWires
    targetWires context Concrete.Elaboration.BinderContext.empty
    Concrete.Elaboration.BinderContext.empty binders occurrence
    (Fin.castAdd 2)
  · intro node equality
    rw [equality] at occurrenceMem
    exact regular_node input selection input.root rootNe node
      ((Concrete.Elaboration.mem_localOccurrences_node input input.root node).1
        occurrenceMem)
  · intro sibling equality
    rw [equality] at occurrenceMem
    exact regular_region input selection input.root sibling rootNe
      ((Concrete.Elaboration.mem_localOccurrences_child input input.root
        sibling).1 occurrenceMem)
  · intro childSourceRels childTargetRels childSourceBinders
      childTargetBinders childBinders sibling equality sourceSibling
      targetSibling sourceCompiled targetCompiled
    rw [equality] at occurrenceMem
    have siblingParent :=
      (Concrete.Elaboration.mem_localOccurrences_child input input.root
        sibling).1 occurrenceMem
    have siblingNe : sibling ≠ child := by
      intro childEq
      subst sibling
      have found := indexOf?_get_eq_some_of_nodup
        (Concrete.Elaboration.localOccurrences_nodup input input.root)
        occurrenceIndex
      have foundChild : indexOf?
          (Concrete.Elaboration.localOccurrences input input.root)
            (.child child) = some occurrenceIndex := by
        rw [← equality]
        exact found
      apply occurrenceNe
      exact Option.some.inj (foundChild.symm.trans positionEq)
    have siblingAway : ¬ input.Encloses sibling selection.val.anchor :=
      Concrete.Splice.Input.PlugLayout.RegionRoute.distinctSibling_away
        source.property.diagram_well_formed tail childParent siblingParent
          siblingNe
    exact DoubleCutIntroCompile.away_region_iso input selection
      source.property.diagram_well_formed sibling siblingAway sourceWires
      targetWires context childSourceBinders childTargetBinders childBinders
      sourceCompiled targetCompiled
  · exact sourceGet
  · exact targetGet'

theorem openRootFrame
    (source : Concrete.CheckedOpen)
    (selection : CheckedSelection source.val.diagram)
    (targetWellFormed :
      (DoubleCutTransport.targetOpen source.val selection).WellFormed)
    {sourceLocal targetLocal : Nat}
    {sourceSeq : ItemSeq
      (source.val.exposedWires.length + sourceLocal) []}
    {targetSeq : ItemSeq
      ((DoubleCutTransport.targetOpen source.val selection).exposedWires.length +
        targetLocal) []}
    (sourceState : Concrete.Splice.OpenRootCompilerState source
      (.mk sourceLocal sourceSeq))
    (targetState : Concrete.Splice.OpenRootCompilerState
      (checkedTarget source selection targetWellFormed)
      (.mk targetLocal targetSeq))
    (sourceLocalCanonical : sourceLocal = source.val.hiddenWires.length)
    (targetLocalCanonical : targetLocal =
      (DoubleCutTransport.targetOpen source.val selection).hiddenWires.length)
    (sourceItemsCanonical : HEq sourceSeq sourceState.canonicalBodyItems)
    (targetItemsCanonical : HEq targetSeq targetState.canonicalBodyItems)
    {sourceIndex : Fin sourceState.items.length}
    {targetIndex : Fin targetState.items.length}
    (rawFrame : ItemSeqIso.Frame
      (FiniteEquiv.finCast (congrArg List.length
        (DoubleCutTransport.targetOpen_rootWires source.val selection).symm))
      sourceIndex targetIndex) :
    ∃ sourceIndex' : Fin sourceSeq.length,
      ∃ targetIndex' : Fin targetSeq.length,
        sourceIndex'.val = sourceIndex.val ∧
        targetIndex'.val = targetIndex.val ∧
        Nonempty (ItemSeqIso.Frame
          (extendWireEquiv
            (FiniteEquiv.finCast (congrArg List.length
              (DoubleCutTransport.targetOpen_exposedWires source.val
                selection).symm))
            ((FiniteEquiv.finCast sourceLocalCanonical).trans
              ((FiniteEquiv.finCast (congrArg List.length
                (DoubleCutTransport.targetOpen_hiddenWires source.val
                  selection).symm)).trans
                (FiniteEquiv.finCast targetLocalCanonical.symm))))
          sourceIndex' targetIndex') := by
  subst sourceLocal
  subst targetLocal
  let target := checkedTarget source selection targetWellFormed
  let sourceEq : source.val.rootWires.length =
      source.val.exposedWires.length + source.val.hiddenWires.length := by
    simp [Concrete.OpenDiagram.rootWires]
  let targetEq : target.val.rootWires.length =
      target.val.exposedWires.length + target.val.hiddenWires.length := by
    simp [Concrete.OpenDiagram.rootWires]
  let firstWire := FiniteEquiv.finCast sourceEq.symm
  let middleWire := FiniteEquiv.finCast (congrArg List.length
    (DoubleCutTransport.targetOpen_rootWires source.val selection).symm)
  let lastWire := FiniteEquiv.finCast targetEq
  let outerWire := FiniteEquiv.finCast (congrArg List.length
    (DoubleCutTransport.targetOpen_exposedWires source.val selection).symm)
  let localWire := FiniteEquiv.finCast (congrArg List.length
    (DoubleCutTransport.targetOpen_hiddenWires source.val selection).symm)
  let finalWire := extendWireEquiv outerWire localWire
  have sourcePull : sourceSeq.renameWires firstWire = sourceState.items := by
    have canonical : sourceSeq = sourceState.canonicalBodyItems :=
      eq_of_heq sourceItemsCanonical
    conv =>
      lhs
      rw [canonical]
    simp only [Concrete.Splice.OpenRootCompilerState.canonicalBodyItems,
      ItemSeq.castWiresEq_eq_renameWires]
    rw [ItemSeq.renameWires_comp]
    have identity : firstWire.toFun ∘
        Fin.cast (by simp [Concrete.OpenDiagram.rootWires]) = id := by
      funext index
      apply Fin.ext
      rfl
    rw [identity]
    exact ItemSeq.renameWires_id sourceState.items
  have targetPush : targetState.items.renameWires lastWire = targetSeq := by
    have canonical : targetSeq = targetState.canonicalBodyItems :=
      eq_of_heq targetItemsCanonical
    conv =>
      rhs
      rw [canonical]
    simp only [Concrete.Splice.OpenRootCompilerState.canonicalBodyItems,
      ItemSeq.castWiresEq_eq_renameWires]
    apply congrArg (targetState.items.renameWires ·)
    funext index
    apply Fin.ext
    rfl
  have wireFactor : (firstWire.trans middleWire).trans lastWire =
      finalWire := by
    apply FiniteEquiv.ext
    intro index
    apply Fin.ext
    refine Fin.addCases (fun outerIndex => ?_)
      (fun localIndex => ?_) index
    · simp [firstWire, middleWire, lastWire, finalWire, outerWire,
        localWire, extendWireEquiv, FiniteEquiv.finCast]
    · simp [firstWire, middleWire, lastWire, finalWire, outerWire,
        localWire, extendWireEquiv, FiniteEquiv.finCast,
        DoubleCutTransport.targetOpen_exposedWires]
  simpa only [finalWire] using
    ItemSeqIso.Frame.pullPush firstWire middleWire lastWire finalWire
      sourcePull targetPush wireFactor rawFrame

structure CompilerTraceAlignment
    {sourceOuter targetOuter : Nat} {rels : RelCtx}
    {sourceBody : Region sourceOuter rels}
    {targetBody : Region targetOuter rels}
    {sourcePath targetPath : List Nat}
    (outerWire : FiniteEquiv (Fin sourceOuter) (Fin targetOuter))
    (sourceWitness : Region.ContextPath sourceBody sourcePath)
    (targetWitness : Region.ContextPath targetBody targetPath) where
  holeRelsEq : sourceWitness.toFocus.holeRels =
    targetWitness.toFocus.holeRels
  holeWire : FiniteEquiv (Fin sourceWitness.toFocus.holeWires)
    (Fin targetWitness.toFocus.holeWires)
  contexts : DiagramContextIso outerWire holeWire rels
    sourceWitness.toFocus.holeRels sourceWitness.toFocus.context
    (holeRelsEq.symm ▸ targetWitness.toFocus.context)

private theorem lifted_child_eq
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    {sourceStart sourceChild : Fin input.regionCount}
    (sourceStartNe : sourceStart ≠ selection.val.anchor)
    (sourcePosition : Fin
      (Concrete.Elaboration.localOccurrences input sourceStart).length)
    (sourcePositionEq : indexOf?
      (Concrete.Elaboration.localOccurrences input sourceStart)
        (.child sourceChild) = some sourcePosition)
    {targetChild : Fin (input.regionCount + 2)}
    (targetPosition : Fin (Concrete.Elaboration.localOccurrences
      (doubleCutIntroRaw input selection)
      (Fin.castAdd 2 sourceStart)).length)
    (targetPositionEq : indexOf? (Concrete.Elaboration.localOccurrences
      (doubleCutIntroRaw input selection) (Fin.castAdd 2 sourceStart))
        (.child targetChild) = some targetPosition)
    (positionVal : targetPosition.val = sourcePosition.val) :
    targetChild = Fin.castAdd 2 sourceChild := by
  have sourceGet := indexOf?_sound sourcePositionEq
  have targetGet := indexOf?_sound targetPositionEq
  let occurrencesEq := regular_localOccurrences input selection sourceStart
    sourceStartNe
  let targetMappedPosition : Fin
      ((Concrete.Elaboration.localOccurrences input sourceStart).map
        (liftOccurrence input)).length :=
    Fin.cast (congrArg List.length occurrencesEq) targetPosition
  let mappedSourcePosition : Fin
      ((Concrete.Elaboration.localOccurrences input sourceStart).map
        (liftOccurrence input)).length :=
    Fin.cast (List.length_map (liftOccurrence input)).symm sourcePosition
  have mappedPositionsEq : targetMappedPosition = mappedSourcePosition := by
    apply Fin.ext
    simpa [targetMappedPosition, mappedSourcePosition] using positionVal
  have targetGetMapped :
      ((Concrete.Elaboration.localOccurrences input sourceStart).map
        (liftOccurrence input)).get targetMappedPosition =
          .child targetChild := by
    calc
      _ = (Concrete.Elaboration.localOccurrences
          (doubleCutIntroRaw input selection)
          (Fin.castAdd 2 sourceStart)).get targetPosition :=
        list_get_cast occurrencesEq targetPosition
      _ = .child targetChild := by
        simpa only [List.get_eq_getElem] using targetGet
  rw [mappedPositionsEq] at targetGetMapped
  have targetGet' : liftOccurrence input
      ((Concrete.Elaboration.localOccurrences input sourceStart).get
        sourcePosition) = .child targetChild := by
    simpa [mappedSourcePosition] using targetGetMapped
  have sourceGet' :
      (Concrete.Elaboration.localOccurrences input sourceStart).get
        sourcePosition = .child sourceChild := by
    simpa only [List.get_eq_getElem] using sourceGet
  rw [sourceGet'] at targetGet'
  exact Concrete.Elaboration.LocalOccurrence.child.inj targetGet'.symm

theorem compilerTraceContextIso
    (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    (wellFormed : input.WellFormed)
    {start site : Fin input.regionCount}
    {targetStart targetSite : Fin (input.regionCount + 2)}
    {sourcePath targetPath : List Nat}
    {sourceRoute : Concrete.Splice.RegionRoute input start site sourcePath}
    {targetRoute : Concrete.Splice.RegionRoute
      (doubleCutIntroRaw input selection) targetStart targetSite targetPath}
    (siteEq : site = selection.val.anchor)
    (startEq : targetStart = Fin.castAdd 2 start)
    (pathEq : targetPath = sourcePath)
    {sourceOuter targetOuter : Nat} {rels : RelCtx}
    {sourceBody : Region sourceOuter rels}
    {targetBody : Region targetOuter rels}
    {sourceWitness : Region.ContextPath sourceBody sourcePath}
    {targetWitness : Region.ContextPath targetBody targetPath}
    (sourceState : Concrete.Splice.Region.ContextPath.CompilerLeaf input start
      (.here sourceBody))
    (targetState : Concrete.Splice.Region.ContextPath.CompilerLeaf
      (doubleCutIntroRaw input selection) targetStart
      (.here targetBody))
    (sourceTrace : Concrete.Splice.CompilerTrace input sourceRoute
      sourceWitness sourceState)
    (targetTrace : Concrete.Splice.CompilerTrace
      (doubleCutIntroRaw input selection)
      targetRoute targetWitness targetState)
    (context : Context input selection sourceState.inheritedWires
      targetState.inheritedWires)
    (binders : Binders input selection sourceState.binders
      targetState.binders) :
    let inherited := FiniteEquiv.finCast
      (congrArg List.length context.equality)
    Nonempty (CompilerTraceAlignment
      (compilerBodyOuterWire sourceState targetState inherited)
      sourceWitness targetWitness) := by
  dsimp only
  revert targetTrace context binders
  induction sourceTrace using @Concrete.Splice.CompilerTrace.rec input
      generalizing targetStart targetPath targetOuter with
  | here sourceState =>
      intro targetTrace
      cases targetTrace using @Concrete.Splice.CompilerTrace.casesOn
          (doubleCutIntroRaw input selection) with
      | here targetState =>
          intro context binders
          let inherited := FiniteEquiv.finCast
            (congrArg List.length context.equality)
          exact ⟨{
            holeRelsEq := rfl
            holeWire := compilerBodyOuterWire sourceState targetState inherited
            contexts := .hole _
          }⟩
      | cut =>
          simp at pathEq
      | bubble =>
          simp at pathEq
  | @cut sourceStart sourceChild sourceEnd sourceRest sourceParent
      sourcePosition sourcePositionEq sourceTail sourceOuter sourceLocal
      sourceRels sourceSeq sourceFocus sourceChildBody sourceAt sourceIsCut
      sourceNested sourceState sourceLocalCanonical sourceItemsCanonical
      sourceChildState sourceChildKind sourceInherited sourceBinders sourceFuel
      sourceTailTrace induction =>
      intro targetTrace
      cases targetTrace using @Concrete.Splice.CompilerTrace.casesOn
          (doubleCutIntroRaw input selection) with
      | here =>
          simp at pathEq
      | @cut targetStart targetChild targetEnd targetRest targetParent
          targetPosition targetPositionEq targetTail targetOuter targetLocal
          targetRels targetSeq targetFocus targetChildBody targetAt targetIsCut
          targetNested targetState targetLocalCanonical targetItemsCanonical
          targetChildState targetChildKind targetInherited targetBinders
          targetFuel targetTailTrace =>
          intro context binders
          have sourceStartNe : sourceStart ≠ selection.val.anchor := by
            intro equality
            subst sourceStart
            exact Concrete.Elaboration.checked_direct_child_not_encloses_parent
              wellFormed sourceParent
              (siteEq ▸ Concrete.Splice.Input.RegionRoute.encloses sourceTail
                wellFormed)
          have positionVal : targetPosition.val = sourcePosition.val :=
            (List.cons.inj pathEq).1
          have restEq : targetRest = sourceRest :=
            (List.cons.inj pathEq).2
          subst targetStart
          have targetChildEq : targetChild = Fin.castAdd 2 sourceChild := by
            exact lifted_child_eq input selection sourceStartNe sourcePosition
              sourcePositionEq targetPosition targetPositionEq positionVal
          subst targetChild
          have targetKind :
              (doubleCutIntroRaw input selection).regions
                  (Fin.castAdd 2 sourceChild) =
                .cut (Fin.castAdd 2 sourceStart) := by
            rw [regular_region input selection sourceStart sourceChild
              sourceStartNe sourceParent, sourceChildKind]
          have targetKindEq := targetChildKind.symm.trans targetKind
          cases CRegion.cut.inj targetKindEq
          let childContext : Context input selection
              sourceChildState.inheritedWires
              targetChildState.inheritedWires := ⟨
            sourceInherited.trans ((context.extend sourceStart).equality.trans
              targetInherited.symm)
          ⟩
          let childBinders : Binders input selection sourceChildState.binders
              targetChildState.binders := by
            rw [sourceBinders, targetBinders]
            exact binders
          obtain ⟨childResult⟩ := induction siteEq rfl restEq
            targetChildState targetTailTrace childContext childBinders
          let inherited := FiniteEquiv.finCast
            (congrArg List.length context.equality)
          let outerWire := compilerBodyOuterWire sourceState targetState
            inherited
          let localWire := (FiniteEquiv.finCast sourceLocalCanonical).trans
            ((FiniteEquiv.finCast (congrArg List.length
              (exactScopeWires input selection sourceStart).symm)).trans
              (FiniteEquiv.finCast targetLocalCanonical.symm))
          let sourceIndex : Fin sourceSeq.length :=
            ⟨sourcePosition.val, ItemSeq.focusAt?_index_lt sourceSeq
              sourcePosition.val sourceFocus sourceAt⟩
          let targetIndex : Fin targetSeq.length :=
            ⟨targetPosition.val, ItemSeq.focusAt?_index_lt targetSeq
              targetPosition.val targetFocus targetAt⟩
          have sourceTailAnchor : Concrete.Splice.RegionRoute input sourceChild
              selection.val.anchor sourceRest := siteEq ▸ sourceTail
          obtain ⟨frame⟩ := compilerLeafFrame input selection wellFormed
            sourceStartNe sourceParent sourcePosition sourcePositionEq
            sourceTailAnchor
            sourceState targetState sourceLocalCanonical targetLocalCanonical
            sourceItemsCanonical targetItemsCanonical context binders sourceIndex
            targetIndex rfl positionVal
          let childInherited := FiniteEquiv.finCast
            (congrArg List.length childContext.equality)
          have childOuterEq : compilerBodyOuterWire sourceChildState
              targetChildState childInherited =
            extendWireEquiv outerWire localWire := by
            apply FiniteEquiv.ext
            intro index
            apply Fin.ext
            have left : (compilerBodyOuterWire sourceChildState
                targetChildState childInherited index).val = index.val := by
              simp [compilerBodyOuterWire, childInherited,
                FiniteEquiv.finCast]
            have outerCountEq : sourceOuter = targetOuter :=
              sourceState.inheritedLength.symm.trans
                ((congrArg List.length context.equality).trans
                  targetState.inheritedLength)
            have right : ((extendWireEquiv outerWire localWire) index).val =
                index.val := by
              refine Fin.addCases (fun inheritedIndex => ?_)
                (fun localIndex => ?_) index
              · simp [outerWire, compilerBodyOuterWire, inherited,
                  extendWireEquiv, FiniteEquiv.finCast]
              · simp [localWire, extendWireEquiv, FiniteEquiv.finCast,
                  outerCountEq]
            exact left.trans right.symm
          have childContexts : DiagramContextIso
              (extendWireEquiv outerWire localWire) childResult.holeWire
              sourceRels sourceNested.toFocus.holeRels
              sourceNested.toFocus.context
              (childResult.holeRelsEq.symm ▸
                targetNested.toFocus.context) := by
            rw [← childOuterEq]
            exact childResult.contexts
          have targetContextTransport :
              childResult.holeRelsEq.symm ▸
                  DiagramContext.cut targetLocal targetFocus.before
                    targetFocus.after targetNested.toFocus.context =
                DiagramContext.cut targetLocal targetFocus.before
                  targetFocus.after
                  (childResult.holeRelsEq.symm ▸
                    targetNested.toFocus.context) :=
            DiagramContext.cut_transport_holeRels childResult.holeRelsEq
              targetFocus.before targetFocus.after targetNested.toFocus.context
          have contexts := DiagramContextIso.cutFrame localWire sourceFocus
            targetFocus sourceAt targetAt frame sourceNested.toFocus.context
            (childResult.holeRelsEq.symm ▸
              targetNested.toFocus.context) childContexts
          exact ⟨{
            holeRelsEq := childResult.holeRelsEq
            holeWire := childResult.holeWire
            contexts := by
              simpa only [Region.ContextPath.toFocus,
                targetContextTransport] using contexts
          }⟩
      | @bubble targetStart targetChild targetEnd targetRest targetParent
          targetPosition targetPositionEq targetTail targetOuter targetLocal
          targetArity targetRels targetSeq targetFocus targetChildBody targetAt
          targetIsBubble targetNested targetState targetLocalCanonical
          targetItemsCanonical targetChildState targetChildKind targetInherited
          targetBinders targetFuel targetTailTrace =>
          intro context binders
          have sourceStartNe : sourceStart ≠ selection.val.anchor := by
            intro equality
            subst sourceStart
            exact Concrete.Elaboration.checked_direct_child_not_encloses_parent
              wellFormed sourceParent
              (siteEq ▸ Concrete.Splice.Input.RegionRoute.encloses sourceTail
                wellFormed)
          have positionVal : targetPosition.val = sourcePosition.val :=
            (List.cons.inj pathEq).1
          subst targetStart
          have targetChildEq : targetChild = Fin.castAdd 2 sourceChild :=
            lifted_child_eq input selection sourceStartNe sourcePosition
              sourcePositionEq targetPosition targetPositionEq positionVal
          subst targetChild
          have targetKind :
              (doubleCutIntroRaw input selection).regions
                  (Fin.castAdd 2 sourceChild) =
                .cut (Fin.castAdd 2 sourceStart) := by
            rw [regular_region input selection sourceStart sourceChild
              sourceStartNe sourceParent, sourceChildKind]
          have impossible := targetChildKind.symm.trans targetKind
          cases impossible
  | @bubble sourceStart sourceChild sourceEnd sourceRest sourceParent
      sourcePosition sourcePositionEq sourceTail sourceOuter sourceLocal
      sourceArity sourceRels sourceSeq sourceFocus sourceChildBody sourceAt
      sourceIsBubble sourceNested sourceState sourceLocalCanonical
      sourceItemsCanonical sourceChildState sourceChildKind sourceInherited
      sourceBinders sourceFuel sourceTailTrace induction =>
      intro targetTrace
      cases targetTrace using @Concrete.Splice.CompilerTrace.casesOn
          (doubleCutIntroRaw input selection) with
      | here =>
          simp at pathEq
      | @cut targetStart targetChild targetEnd targetRest targetParent
          targetPosition targetPositionEq targetTail targetOuter targetLocal
          targetRels targetSeq targetFocus targetChildBody targetAt targetIsCut
          targetNested targetState targetLocalCanonical targetItemsCanonical
          targetChildState targetChildKind targetInherited targetBinders
          targetFuel targetTailTrace =>
          intro context binders
          have sourceStartNe : sourceStart ≠ selection.val.anchor := by
            intro equality
            subst sourceStart
            exact Concrete.Elaboration.checked_direct_child_not_encloses_parent
              wellFormed sourceParent
              (siteEq ▸ Concrete.Splice.Input.RegionRoute.encloses sourceTail
                wellFormed)
          have positionVal : targetPosition.val = sourcePosition.val :=
            (List.cons.inj pathEq).1
          subst targetStart
          have targetChildEq : targetChild = Fin.castAdd 2 sourceChild :=
            lifted_child_eq input selection sourceStartNe sourcePosition
              sourcePositionEq targetPosition targetPositionEq positionVal
          subst targetChild
          have targetKind :
              (doubleCutIntroRaw input selection).regions
                  (Fin.castAdd 2 sourceChild) =
                .bubble (Fin.castAdd 2 sourceStart) sourceArity := by
            rw [regular_region input selection sourceStart sourceChild
              sourceStartNe sourceParent, sourceChildKind]
          have impossible := targetChildKind.symm.trans targetKind
          cases impossible
      | @bubble targetStart targetChild targetEnd targetRest targetParent
          targetPosition targetPositionEq targetTail targetOuter targetLocal
          targetArity targetRels targetSeq targetFocus targetChildBody targetAt
          targetIsBubble targetNested targetState targetLocalCanonical
          targetItemsCanonical targetChildState targetChildKind targetInherited
          targetBinders targetFuel targetTailTrace =>
          intro context binders
          have sourceStartNe : sourceStart ≠ selection.val.anchor := by
            intro equality
            subst sourceStart
            exact Concrete.Elaboration.checked_direct_child_not_encloses_parent
              wellFormed sourceParent
              (siteEq ▸ Concrete.Splice.Input.RegionRoute.encloses sourceTail
                wellFormed)
          have positionVal : targetPosition.val = sourcePosition.val :=
            (List.cons.inj pathEq).1
          have restEq : targetRest = sourceRest :=
            (List.cons.inj pathEq).2
          subst targetStart
          have targetChildEq : targetChild = Fin.castAdd 2 sourceChild :=
            lifted_child_eq input selection sourceStartNe sourcePosition
              sourcePositionEq targetPosition targetPositionEq positionVal
          subst targetChild
          have targetKind :
              (doubleCutIntroRaw input selection).regions
                  (Fin.castAdd 2 sourceChild) =
                .bubble (Fin.castAdd 2 sourceStart) sourceArity := by
            rw [regular_region input selection sourceStart sourceChild
              sourceStartNe sourceParent, sourceChildKind]
          have targetKindEq := targetChildKind.symm.trans targetKind
          have arityEq : targetArity = sourceArity := by
            injection targetKindEq
          subst targetArity
          let childContext : Context input selection
              sourceChildState.inheritedWires
              targetChildState.inheritedWires := ⟨
            sourceInherited.trans ((context.extend sourceStart).equality.trans
              targetInherited.symm)
          ⟩
          let childBinders : Binders input selection sourceChildState.binders
              targetChildState.binders := by
            rw [sourceBinders, targetBinders]
            exact binders.push sourceChild sourceArity
          obtain ⟨childResult⟩ := induction siteEq rfl restEq
            targetChildState targetTailTrace childContext childBinders
          let inherited := FiniteEquiv.finCast
            (congrArg List.length context.equality)
          let outerWire := compilerBodyOuterWire sourceState targetState
            inherited
          let localWire := (FiniteEquiv.finCast sourceLocalCanonical).trans
            ((FiniteEquiv.finCast (congrArg List.length
              (exactScopeWires input selection sourceStart).symm)).trans
              (FiniteEquiv.finCast targetLocalCanonical.symm))
          let sourceIndex : Fin sourceSeq.length :=
            ⟨sourcePosition.val, ItemSeq.focusAt?_index_lt sourceSeq
              sourcePosition.val sourceFocus sourceAt⟩
          let targetIndex : Fin targetSeq.length :=
            ⟨targetPosition.val, ItemSeq.focusAt?_index_lt targetSeq
              targetPosition.val targetFocus targetAt⟩
          have sourceTailAnchor : Concrete.Splice.RegionRoute input sourceChild
              selection.val.anchor sourceRest := siteEq ▸ sourceTail
          obtain ⟨frame⟩ := compilerLeafFrame input selection wellFormed
            sourceStartNe sourceParent sourcePosition sourcePositionEq
            sourceTailAnchor sourceState targetState sourceLocalCanonical
            targetLocalCanonical sourceItemsCanonical targetItemsCanonical
            context binders sourceIndex targetIndex rfl positionVal
          let childInherited := FiniteEquiv.finCast
            (congrArg List.length childContext.equality)
          have childOuterEq : compilerBodyOuterWire sourceChildState
              targetChildState childInherited =
            extendWireEquiv outerWire localWire := by
            apply FiniteEquiv.ext
            intro index
            apply Fin.ext
            have left : (compilerBodyOuterWire sourceChildState
                targetChildState childInherited index).val = index.val := by
              simp [compilerBodyOuterWire, childInherited,
                FiniteEquiv.finCast]
            have outerCountEq : sourceOuter = targetOuter :=
              sourceState.inheritedLength.symm.trans
                ((congrArg List.length context.equality).trans
                  targetState.inheritedLength)
            have right : ((extendWireEquiv outerWire localWire) index).val =
                index.val := by
              refine Fin.addCases (fun inheritedIndex => ?_)
                (fun localIndex => ?_) index
              · simp [outerWire, compilerBodyOuterWire, inherited,
                  extendWireEquiv, FiniteEquiv.finCast]
              · simp [localWire, extendWireEquiv, FiniteEquiv.finCast,
                  outerCountEq]
            exact left.trans right.symm
          have childContexts : DiagramContextIso
              (extendWireEquiv outerWire localWire) childResult.holeWire
              (sourceArity :: sourceRels) sourceNested.toFocus.holeRels
              sourceNested.toFocus.context
              (childResult.holeRelsEq.symm ▸
                targetNested.toFocus.context) := by
            rw [← childOuterEq]
            exact childResult.contexts
          have targetContextTransport :
              childResult.holeRelsEq.symm ▸
                  DiagramContext.bubble targetLocal targetFocus.before
                    targetFocus.after sourceArity
                    targetNested.toFocus.context =
                DiagramContext.bubble targetLocal targetFocus.before
                  targetFocus.after sourceArity
                  (childResult.holeRelsEq.symm ▸
                    targetNested.toFocus.context) :=
            DiagramContext.bubble_transport_holeRels
              childResult.holeRelsEq targetFocus.before targetFocus.after
                targetNested.toFocus.context
          have contexts := DiagramContextIso.bubbleFrame localWire sourceFocus
            targetFocus sourceAt targetAt frame sourceNested.toFocus.context
            (childResult.holeRelsEq.symm ▸
              targetNested.toFocus.context) childContexts
          exact ⟨{
            holeRelsEq := childResult.holeRelsEq
            holeWire := childResult.holeWire
            contexts := by
              simpa only [Region.ContextPath.toFocus,
                targetContextTransport] using contexts
          }⟩

end VisualProof.Refinement.Implementation.DoubleCutIntroContext
