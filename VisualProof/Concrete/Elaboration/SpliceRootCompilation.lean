import VisualProof.Concrete.Elaboration.SpliceSiteCompilation

/-! Construct the target root by following the canonical source host zipper. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Diagram
open Theory
open Elaboration

namespace Splice.Input.PlugLayout

private theorem sibling_not_encloses
    {d : Diagram} (hwf : d.WellFormed)
    {parent selected sibling site : Fin d.regionCount}
    (selectedParent : (d.regions selected).parent? = some parent)
    (siblingParent : (d.regions sibling).parent? = some parent)
    (different : sibling ≠ selected)
    (selectedEncloses : d.Encloses selected site) :
    ¬ d.Encloses sibling site := by
  intro siblingEncloses
  rcases d.enclosingRegions_comparable selectedEncloses siblingEncloses with
    selectedSibling | siblingSelected
  · rcases Elaboration.encloses_direct_child siblingParent selectedSibling with
      same | selectedParentEncloses
    · exact different same.symm
    · exact Elaboration.checked_direct_child_not_encloses_parent hwf
        selectedParent selectedParentEncloses
  · rcases Elaboration.encloses_direct_child selectedParent siblingSelected with
      same | siblingParentEncloses
    · exact different same
    · exact Elaboration.checked_direct_child_not_encloses_parent hwf
        siblingParent siblingParentEncloses

private def finSuccEquiv
    (equiv : FiniteEquiv (Fin source) (Fin target)) :
    FiniteEquiv (Fin source.succ) (Fin target.succ) where
  toFun := Fin.cases 0 (fun index => (equiv index).succ)
  invFun := Fin.cases 0 (fun index => (equiv.symm index).succ)
  left_inv := by
    intro index
    induction index using Fin.cases with
    | zero => rfl
    | succ rest => exact congrArg Fin.succ (equiv.left_inv rest)
  right_inv := by
    intro index
    induction index using Fin.cases with
    | zero => rfl
    | succ rest => exact congrArg Fin.succ (equiv.right_inv rest)

/-- Add a distinguished head to a frame whose tails are already aligned. -/
private noncomputable def ItemSeqIso.Frame.selectedCons
    {sourceTail : ItemSeq sourceWires rels}
    {targetTail : ItemSeq targetWires rels}
    (tail : ItemSeqIso wire rels sourceTail targetTail)
    (sourceHead : Item sourceWires rels)
    (targetHead : Item targetWires rels) :
    ItemSeqIso.Frame
      (source := .cons sourceHead sourceTail)
      (target := .cons targetHead targetTail) wire
      ⟨0, Nat.zero_lt_succ _⟩ ⟨0, Nat.zero_lt_succ _⟩ := by
  cases tail with
  | permute positions items =>
      refine {
        positions := finSuccEquiv positions
        mapped := rfl
        siblings := ?_
      }
      intro index different
      induction index using Fin.cases with
      | zero => exact False.elim (different rfl)
      | succ rest =>
          simpa [ItemSeq.get, finSuccEquiv] using items rest

/-- Add one aligned nonfocused head before an existing focused frame. -/
private noncomputable def ItemSeqIso.Frame.siblingCons
    {sourceHead : Item sourceWires rels}
    {targetHead : Item targetWires rels}
    {sourceTail : ItemSeq sourceWires rels}
    {targetTail : ItemSeq targetWires rels}
    {sourceIndex : Fin sourceTail.length}
    {targetIndex : Fin targetTail.length}
    (head : ItemIso wire rels sourceHead targetHead)
    (tail : ItemSeqIso.Frame wire sourceIndex targetIndex) :
    ItemSeqIso.Frame
      (source := .cons sourceHead sourceTail)
      (target := .cons targetHead targetTail)
      wire sourceIndex.succ targetIndex.succ := by
  refine {
    positions := finSuccEquiv tail.positions
    mapped := congrArg Fin.succ tail.mapped
    siblings := ?_
  }
  intro index different
  induction index using Fin.cases with
  | zero => simpa [ItemSeq.get, finSuccEquiv] using head
  | succ rest =>
      have restDifferent : rest ≠ sourceIndex := by
        intro same
        exact different (congrArg Fin.succ same)
      simpa [ItemSeq.get, finSuccEquiv] using
        tail.siblings rest restDifferent

/-- The one recursive semantic result.  The compiler result and the aligned
enclosing context remain separate; the endpoint isomorphism is filled only by
the root caller. -/
private structure NestedGraftResult
    (layout : PlugLayout input) (targetWf : layout.plugRaw.WellFormed)
    {endpointCall : CompilerCall input.frame.val}
    {endpoint : CompiledRegion input.frame.val endpointCall}
    {sourceOuter : WireContext input.frame.val}
    {sourceBinders : BinderContext input.frame.val sourceRels}
    {sourceBody : CompiledRegion input.frame.val
      (.nested sourceParent sourceOuter sourceRels sourceBinders)}
    {targetOuter : WireContext layout.plugRaw}
    {targetBinders : BinderContext layout.plugRaw sourceRels}
    (outerWire : FiniteEquiv (Fin targetOuter.length)
      (Fin sourceOuter.length))
    (focus : CompiledZipper input.frame.val sourceBody input.site
      endpointCall endpoint)
    (after : Region endpointCall.outerContext.length endpointCall.rels) where
  targetBody : CompiledRegion layout.plugRaw
    (.nested (layout.frameRegion sourceParent) targetOuter sourceRels
      targetBinders)
  compiled : compileRegion? layout.plugRaw targetWf
    (layout.frameRegion sourceParent) targetOuter targetBinders =
      some targetBody
  holeWires : Nat
  holeWire : FiniteEquiv (Fin holeWires)
    (Fin endpointCall.outerContext.length)
  targetSite : Region holeWires endpointCall.rels
  targetContext : DiagramContext targetOuter.length holeWires
    sourceRels endpointCall.rels
  alignment : DiagramContextIso outerWire holeWire sourceRels endpointCall.rels
    targetContext focus.intrinsic.context
  targetRebuild : targetContext.fill targetSite = targetBody.erase
  endpointIso : RegionIso holeWire endpointCall.rels targetSite after

/-- A distinguished item and all nonfocused sibling isomorphisms. -/
private structure SelectedFrame
    (wire : FiniteEquiv (Fin targetWires) (Fin sourceWires))
    (targetItems : ItemSeq targetWires rels)
    (sourceItems : ItemSeq sourceWires rels) where
  targetIndex : Fin targetItems.length
  sourceIndex : Fin sourceItems.length
  targetFocus : ItemSeq.IndexedFocus targetItems targetIndex
  sourceFocus : ItemSeq.IndexedFocus sourceItems sourceIndex
  frame : ItemSeqIso.Frame wire targetIndex sourceIndex

private noncomputable def SelectedFrame.selectedCons
    {targetTail : ItemSeq targetWires rels}
    {sourceTail : ItemSeq sourceWires rels}
    (tail : ItemSeqIso wire rels targetTail sourceTail)
    (targetHead : Item targetWires rels)
    (sourceHead : Item sourceWires rels) :
    SelectedFrame wire (.cons targetHead targetTail)
      (.cons sourceHead sourceTail) where
  targetIndex := ⟨0, Nat.zero_lt_succ _⟩
  sourceIndex := ⟨0, Nat.zero_lt_succ _⟩
  targetFocus := ItemSeq.focusAt (.cons targetHead targetTail)
    ⟨0, Nat.zero_lt_succ _⟩
  sourceFocus := ItemSeq.focusAt (.cons sourceHead sourceTail)
    ⟨0, Nat.zero_lt_succ _⟩
  frame := ItemSeqIso.Frame.selectedCons tail targetHead sourceHead

private noncomputable def SelectedFrame.siblingCons
    {targetHead : Item targetWires rels}
    {sourceHead : Item sourceWires rels}
    {targetTail : ItemSeq targetWires rels}
    {sourceTail : ItemSeq sourceWires rels}
    (head : ItemIso wire rels targetHead sourceHead)
    (tail : SelectedFrame wire targetTail sourceTail) :
    SelectedFrame wire (.cons targetHead targetTail)
      (.cons sourceHead sourceTail) where
  targetIndex := tail.targetIndex.succ
  sourceIndex := tail.sourceIndex.succ
  targetFocus := ItemSeq.focusAt (.cons targetHead targetTail)
    tail.targetIndex.succ
  sourceFocus := ItemSeq.focusAt (.cons sourceHead sourceTail)
    tail.sourceIndex.succ
  frame := ItemSeqIso.Frame.siblingCons head tail.frame

private noncomputable def awayLocalWire
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (parent : Fin input.frame.val.regionCount)
    (away : parent ≠ input.site) :
    FiniteEquiv
      (Fin (exactScopeWires layout.plugRaw
        (layout.frameRegion parent)).length)
      (Fin (exactScopeWires input.frame.val parent).length) := by
  have localEq : exactScopeWires layout.plugRaw
      (layout.frameRegion parent) =
        (exactScopeWires input.frame.val parent).map layout.frameWireMap := by
    rw [layout.exactScopeWires_frameRegion consistent terminal parent,
      if_neg away, List.append_nil]
    rfl
  exact FiniteEquiv.finCast
    ((congrArg List.length localEq).trans
      (List.length_map layout.frameWireMap))

private noncomputable def awayFullWire
    (layout : PlugLayout input)
    {sourceOuter : WireContext input.frame.val}
    {targetOuter : WireContext layout.plugRaw}
    (parent : Fin input.frame.val.regionCount)
    (outerWire : FiniteEquiv (Fin targetOuter.length)
      (Fin sourceOuter.length))
    (localWire : FiniteEquiv
      (Fin (exactScopeWires layout.plugRaw
        (layout.frameRegion parent)).length)
      (Fin (exactScopeWires input.frame.val parent).length)) :
    FiniteEquiv
      (Fin (targetOuter.extend (layout.frameRegion parent)).length)
      (Fin (sourceOuter.extend parent).length) :=
  castFinEquiv (WireContext.length_extend targetOuter
      (layout.frameRegion parent))
    (WireContext.length_extend sourceOuter parent)
    (extendWireEquiv outerWire localWire)

private theorem awayLocalWire_get
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (parent : Fin input.frame.val.regionCount)
    (away : parent ≠ input.site)
    (index : Fin (exactScopeWires input.frame.val parent).length) :
    (exactScopeWires layout.plugRaw (layout.frameRegion parent)).get
        ((layout.awayLocalWire consistent terminal parent away).symm index) =
      layout.frameWireMap
        ((exactScopeWires input.frame.val parent).get index) := by
  have localEq : exactScopeWires layout.plugRaw
      (layout.frameRegion parent) =
        (exactScopeWires input.frame.val parent).map layout.frameWireMap := by
    rw [layout.exactScopeWires_frameRegion consistent terminal parent,
      if_neg away, List.append_nil]
    rfl
  rw [List.get_of_eq localEq]
  change ((exactScopeWires input.frame.val parent).map
      layout.frameWireMap).get
        (Fin.cast (List.length_map layout.frameWireMap).symm index) = _
  exact List.getElem_map layout.frameWireMap

private theorem awayFullWire_get
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    {sourceOuter : WireContext input.frame.val}
    {targetOuter : WireContext layout.plugRaw}
    (parent : Fin input.frame.val.regionCount)
    (away : parent ≠ input.site)
    (outerWire : FiniteEquiv (Fin targetOuter.length)
      (Fin sourceOuter.length))
    (outerGet : ∀ index, targetOuter.get (outerWire.symm index) =
      layout.frameWireMap (sourceOuter.get index))
    (index : Fin (sourceOuter.extend parent).length) :
    (targetOuter.extend (layout.frameRegion parent)).get
        ((layout.awayFullWire parent outerWire
          (layout.awayLocalWire consistent terminal parent away)).symm index) =
      layout.frameWireMap ((sourceOuter.extend parent).get index) := by
  let split := Fin.cast (WireContext.length_extend sourceOuter parent) index
  have indexEq : Fin.cast (WireContext.length_extend sourceOuter parent).symm
      split = index := by
    apply Fin.ext
    rfl
  rw [← indexEq]
  exact Fin.addCases (motive := fun position =>
      (targetOuter.extend (layout.frameRegion parent)).get
          ((layout.awayFullWire parent outerWire
            (layout.awayLocalWire consistent terminal parent away)).symm
            (Fin.cast (WireContext.length_extend sourceOuter parent).symm
              position)) =
        layout.frameWireMap ((sourceOuter.extend parent).get
          (Fin.cast (WireContext.length_extend sourceOuter parent).symm
            position)))
    (fun inherited => by
      simpa [awayFullWire, castFinEquiv, extendWireEquiv,
        WireContext.extend] using outerGet inherited)
    (fun localIndex => by
      simpa [awayFullWire, castFinEquiv, extendWireEquiv,
        WireContext.extend] using
          layout.awayLocalWire_get consistent terminal parent away localIndex)
    split

/-- The item fold returns one selected compiler frame and the recursive
context graft below its distinguished cut or bubble. -/
private inductive FocusedItemsGraft
    (layout : PlugLayout input) (targetWf : layout.plugRaw.WellFormed)
    {endpointCall : CompilerCall input.frame.val}
    {endpoint : CompiledRegion input.frame.val endpointCall}
    {sourceOuter : WireContext input.frame.val}
    {sourceBinders : BinderContext input.frame.val sourceRels}
    {targetOuter : WireContext layout.plugRaw}
    {targetBinders : BinderContext layout.plugRaw sourceRels}
    (outerWire : FiniteEquiv (Fin targetOuter.length)
      (Fin sourceOuter.length))
    (localWire : FiniteEquiv
      (Fin (exactScopeWires layout.plugRaw
        (layout.frameRegion sourceParent)).length)
      (Fin (exactScopeWires input.frame.val sourceParent).length)) :
    {sourceItems : CompiledItems input.frame.val
      (sourceOuter.extend sourceParent) sourceRels sourceBinders} →
    CompiledItemsZipper input.frame.val sourceItems input.site
      endpointCall endpoint →
    (after : Region endpointCall.outerContext.length endpointCall.rels) → Type
  | cut
      {origin : Fin input.frame.val.regionCount}
      {sourceChild : CompiledRegion input.frame.val
        (.nested origin (sourceOuter.extend sourceParent) sourceRels
          sourceBinders)}
      {sourceSuffix : CompiledItems input.frame.val
        (sourceOuter.extend sourceParent) sourceRels sourceBinders}
      {nested : CompiledZipper input.frame.val sourceChild input.site
        endpointCall endpoint}
      (targetItems : CompiledItems layout.plugRaw
        (targetOuter.extend (layout.frameRegion sourceParent)) sourceRels
        targetBinders)
      (targetCompiled : compileItems? layout.plugRaw targetWf
        (layout.frameRegion sourceParent)
        (targetOuter.extend (layout.frameRegion sourceParent)) targetBinders
        (localOccurrences layout.plugRaw (layout.frameRegion sourceParent))
        (fun _ member => member) = some targetItems)
      (selected : SelectedFrame
        (castFinEquiv
          (WireContext.length_extend targetOuter
            (layout.frameRegion sourceParent))
          (WireContext.length_extend sourceOuter sourceParent)
          (extendWireEquiv outerWire localWire))
        targetItems.erase (.cons (.cut sourceChild.erase) sourceSuffix.erase))
      (child : NestedGraftResult layout targetWf
        (targetBinders := targetBinders)
        (outerWire := castFinEquiv
          (WireContext.length_extend targetOuter
            (layout.frameRegion sourceParent))
          (WireContext.length_extend sourceOuter sourceParent)
          (extendWireEquiv outerWire localWire)) nested after) :
      FocusedItemsGraft layout targetWf outerWire localWire
        (.cut nested) after
  | bubble
      {origin : Fin input.frame.val.regionCount} {arity : Nat}
      {sourceChild : CompiledRegion input.frame.val
        (.nested origin (sourceOuter.extend sourceParent) (arity :: sourceRels)
          (sourceBinders.push origin arity))}
      {sourceSuffix : CompiledItems input.frame.val
        (sourceOuter.extend sourceParent) sourceRels sourceBinders}
      {nested : CompiledZipper input.frame.val sourceChild input.site
        endpointCall endpoint}
      (targetItems : CompiledItems layout.plugRaw
        (targetOuter.extend (layout.frameRegion sourceParent)) sourceRels
        targetBinders)
      (targetCompiled : compileItems? layout.plugRaw targetWf
        (layout.frameRegion sourceParent)
        (targetOuter.extend (layout.frameRegion sourceParent)) targetBinders
        (localOccurrences layout.plugRaw (layout.frameRegion sourceParent))
        (fun _ member => member) = some targetItems)
      (selected : SelectedFrame
        (castFinEquiv
          (WireContext.length_extend targetOuter
            (layout.frameRegion sourceParent))
          (WireContext.length_extend sourceOuter sourceParent)
          (extendWireEquiv outerWire localWire))
        targetItems.erase
        (.cons (.bubble arity sourceChild.erase) sourceSuffix.erase))
      (child : NestedGraftResult layout targetWf
        (targetBinders := targetBinders.push
          (layout.frameRegion origin) arity)
        (outerWire := castFinEquiv
          (WireContext.length_extend targetOuter
            (layout.frameRegion sourceParent))
          (WireContext.length_extend sourceOuter sourceParent)
          (extendWireEquiv outerWire localWire)) nested after) :
      FocusedItemsGraft layout targetWf outerWire localWire
        (.bubble nested) after



end Splice.Input.PlugLayout

end VisualProof.Concrete
