import VisualProof.Concrete.Elaboration.SpliceNodeBlocks

/-! Recursive compiler transport for retained frame children. -/

namespace VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open Theory
open Elaboration

namespace Splice.Input.PlugLayout

private theorem get_cast_of_eq {first second : List α}
    (equality : first = second) (index : Fin second.length) :
    first.get (Fin.cast (congrArg List.length equality).symm index) =
      second.get index := by
  subst second
  rfl

private theorem get_of_eq {first second : List α}
    (equality : first = second)
    (firstIndex : Fin first.length) (secondIndex : Fin second.length)
    (indexEq : firstIndex.val = secondIndex.val) :
    first.get firstIndex = second.get secondIndex := by
  subst second
  have indices : firstIndex = secondIndex := Fin.ext indexEq
  subst secondIndex
  rfl

private theorem ItemSeq.renameWires_heq_of_val
    (items : ItemSeq source rels)
    (first : Fin source → Fin firstTarget)
    (second : Fin source → Fin secondTarget)
    (targetEq : firstTarget = secondTarget)
    (values : ∀ index, (first index).val = (second index).val) :
    items.renameWires first ≍ items.renameWires second := by
  subst secondTarget
  have maps : first = second := by
    funext index
    exact Fin.ext (values index)
  subst second
  rfl

/-- Compare two successful sequence compilers pointwise without requiring
either recursive compiler to have the same failure behavior. -/
private theorem compileOccurrencesWith?_map_of_success
    {sourceDiagram targetDiagram : Concrete.Diagram}
    (sourceRecurse : ∀ {rels : RelCtx},
      (region : Fin sourceDiagram.regionCount) →
      (context : WireContext sourceDiagram) →
      BinderContext sourceDiagram rels → Option (Region context.length rels))
    (targetRecurse : ∀ {rels : RelCtx},
      (region : Fin targetDiagram.regionCount) →
      (context : WireContext targetDiagram) →
      BinderContext targetDiagram rels → Option (Region context.length rels))
    (sourceContext : WireContext sourceDiagram)
    (targetContext : WireContext targetDiagram)
    (sourceBinders : BinderContext sourceDiagram rels)
    (targetBinders : BinderContext targetDiagram rels)
    (mapOccurrence : LocalOccurrence sourceDiagram.regionCount
        sourceDiagram.nodeCount →
      LocalOccurrence targetDiagram.regionCount targetDiagram.nodeCount)
    (wireMap : Fin sourceContext.length → Fin targetContext.length)
    (sourceOccurrences : List
      (LocalOccurrence sourceDiagram.regionCount sourceDiagram.nodeCount))
    (sourceItems : ItemSeq sourceContext.length rels)
    (targetItems : ItemSeq targetContext.length rels)
    (sourceCompiled : compileOccurrencesWith? sourceDiagram sourceRecurse
      sourceContext sourceBinders sourceOccurrences = some sourceItems)
    (targetCompiled : compileOccurrencesWith? targetDiagram targetRecurse
      targetContext targetBinders (sourceOccurrences.map mapOccurrence) =
        some targetItems)
    (occurrenceMapped : ∀ occurrence,
      occurrence ∈ sourceOccurrences →
      ∀ sourceItem targetItem,
        compileOccurrenceWith? sourceDiagram sourceRecurse
            sourceContext sourceBinders occurrence = some sourceItem →
        compileOccurrenceWith? targetDiagram targetRecurse
            targetContext targetBinders (mapOccurrence occurrence) =
              some targetItem →
        targetItem = sourceItem.renameWires wireMap) :
    targetItems = sourceItems.renameWires wireMap := by
  induction sourceOccurrences generalizing sourceItems targetItems with
  | nil =>
      simp only [compileOccurrencesWith?] at sourceCompiled targetCompiled
      cases sourceCompiled
      cases targetCompiled
      rfl
  | cons occurrence tail inductionHypothesis =>
      simp only [compileOccurrencesWith?] at sourceCompiled
      simp only [List.map_cons, compileOccurrencesWith?] at targetCompiled
      cases sourceHead : compileOccurrenceWith? sourceDiagram sourceRecurse
          sourceContext sourceBinders occurrence with
      | none => simp [sourceHead] at sourceCompiled
      | some sourceItem =>
          cases sourceTail : compileOccurrencesWith? sourceDiagram sourceRecurse
              sourceContext sourceBinders tail with
          | none => simp [sourceHead, sourceTail] at sourceCompiled
          | some compiledSourceTail =>
              simp [sourceHead, sourceTail] at sourceCompiled
              subst sourceItems
              cases targetHead : compileOccurrenceWith? targetDiagram
                  targetRecurse targetContext targetBinders
                  (mapOccurrence occurrence) with
              | none => simp [targetHead] at targetCompiled
              | some targetItem =>
                  cases targetTail : compileOccurrencesWith? targetDiagram
                      targetRecurse targetContext targetBinders
                      (tail.map mapOccurrence) with
                  | none => simp [targetHead, targetTail] at targetCompiled
                  | some compiledTargetTail =>
                      simp [targetHead, targetTail] at targetCompiled
                      subst targetItems
                      have headEq := occurrenceMapped occurrence (by simp)
                        sourceItem targetItem sourceHead targetHead
                      have tailMapped : ∀ current, current ∈ tail →
                          ∀ sourceCurrent targetCurrent,
                            compileOccurrenceWith? sourceDiagram sourceRecurse
                                sourceContext sourceBinders current =
                              some sourceCurrent →
                            compileOccurrenceWith? targetDiagram targetRecurse
                                targetContext targetBinders
                                (mapOccurrence current) = some targetCurrent →
                            targetCurrent =
                              sourceCurrent.renameWires wireMap := by
                        intro current member
                        exact occurrenceMapped current (by simp [member])
                      have tailEq := inductionHypothesis compiledSourceTail
                        compiledTargetTail
                        sourceTail targetTail tailMapped
                      simp only [ItemSeq.renameWires]
                      rw [headEq, tailEq]

/-- Away from the splice site, retained frame regions have the same number of
local wires as their source regions. -/
theorem exactScopeWires_frameRegion_length_of_ne
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (region : Fin input.frame.val.regionCount)
    (away : region ≠ input.site) :
    (exactScopeWires layout.plugRaw
      (layout.frameRegion region)).length =
        (exactScopeWires input.frame.val region).length := by
  rw [layout.exactScopeWires_frameRegion consistent terminal region,
    if_neg away, List.append_nil]
  simp [frameLocalWires]

/-- Extend an ordered embedding of inherited frame wires by the stable local
wire block of a retained frame region. -/
noncomputable def extendFrameContextIndexMap
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (sourceContext : WireContext input.frame.val)
    (targetContext : WireContext layout.plugRaw)
    (wireMap : Fin sourceContext.length → Fin targetContext.length)
    (region : Fin input.frame.val.regionCount)
    (away : region ≠ input.site) :
    Fin (sourceContext.extend region).length →
      Fin (targetContext.extend (layout.frameRegion region)).length :=
  fun index =>
    Fin.cast (by
      rw [WireContext.length_extend,
        layout.exactScopeWires_frameRegion_length_of_ne consistent terminal
          region away])
      (extendWireRenaming wireMap
        (exactScopeWires input.frame.val region).length
        (Fin.cast (WireContext.length_extend sourceContext region) index))

/-- The extended position embedding retrieves exactly the embedded source
wire, both in the inherited prefix and in the newly appended local block. -/
theorem extendFrameContextIndexMap_get
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (sourceContext : WireContext input.frame.val)
    (targetContext : WireContext layout.plugRaw)
    (wireMap : Fin sourceContext.length → Fin targetContext.length)
    (getMapped : ∀ index,
      targetContext.get (wireMap index) =
        layout.frameWireEmbedding consistent (sourceContext.get index))
    (region : Fin input.frame.val.regionCount)
    (away : region ≠ input.site)
    (index : Fin (sourceContext.extend region).length) :
    (targetContext.extend (layout.frameRegion region)).get
        (layout.extendFrameContextIndexMap consistent terminal
          sourceContext targetContext wireMap region away index) =
      layout.frameWireEmbedding consistent
        ((sourceContext.extend region).get index) := by
  let sourceIndex : Fin
      (sourceContext.length +
        (exactScopeWires input.frame.val region).length) :=
    Fin.cast (WireContext.length_extend sourceContext region) index
  have sourceIndexEq :
      Fin.cast (WireContext.length_extend sourceContext region).symm
        sourceIndex = index := by
    apply Fin.ext
    rfl
  rw [← sourceIndexEq]
  refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_) sourceIndex
  · have targetPosition :
        layout.extendFrameContextIndexMap consistent terminal
            sourceContext targetContext wireMap region away
            (Fin.cast (WireContext.length_extend sourceContext region).symm
              (Fin.castAdd (exactScopeWires input.frame.val region).length
                inherited)) =
          Fin.cast (by simp [WireContext.extend])
            (Fin.castAdd
              (exactScopeWires layout.plugRaw
                (layout.frameRegion region)).length
              (wireMap inherited)) := by
      apply Fin.ext
      simp [extendFrameContextIndexMap, extendWireRenaming]
    have sourcePosition :
        Fin.cast (WireContext.length_extend sourceContext region).symm
            (Fin.castAdd (exactScopeWires input.frame.val region).length
              inherited) =
          Fin.cast (by simp [WireContext.extend])
            (Fin.castAdd (exactScopeWires input.frame.val region).length
              inherited) := by
      apply Fin.ext
      rfl
    rw [targetPosition, sourcePosition]
    simp only [WireContext.extend, get_append_castAdd]
    exact getMapped inherited
  · let targetLocal : Fin
        (exactScopeWires layout.plugRaw
          (layout.frameRegion region)).length :=
      Fin.cast
        (layout.exactScopeWires_frameRegion_length_of_ne consistent terminal
          region away).symm localIndex
    have targetPosition :
        layout.extendFrameContextIndexMap consistent terminal
            sourceContext targetContext wireMap region away
            (Fin.cast (WireContext.length_extend sourceContext region).symm
              (Fin.natAdd sourceContext.length localIndex)) =
          Fin.cast (by simp [WireContext.extend])
            (Fin.natAdd targetContext.length targetLocal) := by
      apply Fin.ext
      simp [extendFrameContextIndexMap, extendWireRenaming, targetLocal]
    have sourcePosition :
        Fin.cast (WireContext.length_extend sourceContext region).symm
            (Fin.natAdd sourceContext.length localIndex) =
          Fin.cast (by simp [WireContext.extend])
            (Fin.natAdd sourceContext.length localIndex) := by
      apply Fin.ext
      rfl
    rw [targetPosition, sourcePosition]
    simp only [WireContext.extend, get_append_natAdd]
    have localWiresEq :
        exactScopeWires layout.plugRaw (layout.frameRegion region) =
          (exactScopeWires input.frame.val region).map
            (layout.frameWireEmbedding consistent) := by
      rw [layout.exactScopeWires_frameRegion consistent terminal region,
        if_neg away, List.append_nil]
      rfl
    let mappedLocal : Fin
        ((exactScopeWires input.frame.val region).map
          (layout.frameWireEmbedding consistent)).length :=
      Fin.cast (List.length_map
        (layout.frameWireEmbedding consistent)).symm localIndex
    calc
      _ = ((exactScopeWires input.frame.val region).map
            (layout.frameWireEmbedding consistent)).get mappedLocal := by
        apply get_of_eq localWiresEq targetLocal mappedLocal
        rfl
      _ = _ := by
        unfold mappedLocal
        exact List.getElem_map (layout.frameWireEmbedding consistent)

/-- The recursive retained-frame compiler kernel.  The source region is either
below the splice site or belongs to a subtree that does not contain it; this
source-only separation invariant is preserved by every direct child. -/
private theorem compileRegion?_frameRegion_map_of_separated
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (sourceWellFormed : input.frame.val.WellFormed)
    (targetWellFormed : layout.plugRaw.WellFormed)
    (region : Fin input.frame.val.regionCount)
    (separated : input.frame.val.Encloses input.site region ∨
      ¬input.frame.val.Encloses region input.site)
    (away : region ≠ input.site)
    (sourceContext : WireContext input.frame.val)
    (targetContext : WireContext layout.plugRaw)
    (wireMap : Fin sourceContext.length → Fin targetContext.length)
    (getMapped : ∀ index,
      targetContext.get (wireMap index) =
        layout.frameWireEmbedding consistent (sourceContext.get index))
    (sourceExact : (sourceContext.extend region).Exact region)
    (targetExact :
      (targetContext.extend (layout.frameRegion region)).Exact
        (layout.frameRegion region))
    (sourceBinders : BinderContext input.frame.val rels)
    (sourceFuel targetFuel : Nat)
    (sourceBody : Region sourceContext.length rels)
    (targetBody : Region targetContext.length rels)
    (sourceCompiled : compileRegion? input.frame.val sourceFuel region
      sourceContext sourceBinders = some sourceBody)
    (targetCompiled : compileRegion? layout.plugRaw targetFuel
      (layout.frameRegion region) targetContext
      (layout.mapFrameBinders sourceBinders) = some targetBody) :
    targetBody = sourceBody.renameWires wireMap := by
  induction sourceFuel generalizing targetFuel region sourceContext
      targetContext wireMap rels sourceBinders sourceBody targetBody with
  | zero => simp [compileRegion?] at sourceCompiled
  | succ sourceFuel inductionHypothesis =>
      cases targetFuel with
      | zero => simp [compileRegion?] at targetCompiled
      | succ targetFuel =>
          let sourceExtended := sourceContext.extend region
          let targetExtended :=
            targetContext.extend (layout.frameRegion region)
          let extendedWireMap := layout.extendFrameContextIndexMap consistent
            terminal sourceContext targetContext wireMap region away
          have extendedGet : ∀ index,
              targetExtended.get (extendedWireMap index) =
                layout.frameWireEmbedding consistent
                  (sourceExtended.get index) := by
            intro index
            exact layout.extendFrameContextIndexMap_get consistent terminal
              sourceContext targetContext wireMap getMapped region away index
          simp only [compileRegion?] at sourceCompiled targetCompiled
          cases sourceItemsResult : compileOccurrencesWith? input.frame.val
              (compileRegion? input.frame.val sourceFuel) sourceExtended
              sourceBinders (localOccurrences input.frame.val region) with
          | none => simp [sourceExtended, sourceItemsResult] at sourceCompiled
          | some sourceItems =>
              simp [sourceExtended, sourceItemsResult] at sourceCompiled
              subst sourceBody
              have targetOccurrences :=
                layout.localOccurrences_frameRegion_of_ne_site region away
              rw [targetOccurrences] at targetCompiled
              change (do
                let items ← compileOccurrencesWith? layout.plugRaw
                  (compileRegion? layout.plugRaw targetFuel) targetExtended
                  (layout.mapFrameBinders sourceBinders)
                  ((localOccurrences input.frame.val region).map
                    layout.mapFrameOccurrence)
                pure (finishRegion layout.plugRaw targetContext
                  (layout.frameRegion region) items)) =
                    some targetBody at targetCompiled
              cases targetItemsResult : compileOccurrencesWith? layout.plugRaw
                  (compileRegion? layout.plugRaw targetFuel) targetExtended
                  (layout.mapFrameBinders sourceBinders)
                  ((localOccurrences input.frame.val region).map
                    layout.mapFrameOccurrence) with
              | none =>
                  simp [targetExtended, targetItemsResult] at targetCompiled
              | some targetItems =>
                  simp [targetExtended, targetItemsResult] at targetCompiled
                  subst targetBody
                  have occurrenceMapped : ∀ occurrence,
                      occurrence ∈ localOccurrences input.frame.val region →
                      ∀ sourceItem targetItem,
                        compileOccurrenceWith? input.frame.val
                            (compileRegion? input.frame.val sourceFuel)
                            sourceExtended sourceBinders occurrence =
                              some sourceItem →
                        compileOccurrenceWith? layout.plugRaw
                            (compileRegion? layout.plugRaw targetFuel)
                            targetExtended
                            (layout.mapFrameBinders sourceBinders)
                            (layout.mapFrameOccurrence occurrence) =
                              some targetItem →
                        targetItem =
                          sourceItem.renameWires extendedWireMap := by
                    intro occurrence member sourceItem targetItem
                      sourceItemCompiled targetItemCompiled
                    cases occurrence with
                    | node node =>
                        have nodeRegion :
                            (input.frame.val.nodes node).region = region :=
                          (mem_localOccurrences_node input.frame.val
                            region node).mp member
                        have nodeMap := layout.compileNode?_frameNode_map
                          consistent sourceExtended targetExtended
                          sourceBinders (layout.mapFrameBinders sourceBinders)
                          node extendedWireMap (fun relation => relation)
                          targetExact.nodup extendedGet (by
                            intro wire port occurs _
                            have wireEncloses := sourceWellFormed
                              |>.wire_scopes_enclose wire ⟨node, port⟩ occurs
                            exact (sourceExact.mem_iff wire).2 (by
                              simpa [nodeRegion] using wireEncloses))
                          targetWellFormed.wire_endpoints_are_disjoint (by
                            intro nodeOwner binder _
                            rw [layout.mapFrameBinders_frameRegion]
                            cases sourceBinders binder <;> simp)
                        simp only [compileOccurrenceWith?, mapFrameOccurrence]
                          at sourceItemCompiled targetItemCompiled
                        rw [sourceItemCompiled] at nodeMap
                        simp only [Option.map_some,
                          Item.renameRelations_id] at nodeMap
                        exact Option.some.inj
                          (targetItemCompiled.symm.trans nodeMap)
                    | child child =>
                        have sourceParent :=
                          (mem_localOccurrences_child input.frame.val
                            region child).mp member
                        have parentChild :
                            input.frame.val.Encloses region child := by
                          refine ⟨⟨1, by
                            have := child.isLt
                            omega⟩, ?_⟩
                          simp [Diagram.climb, sourceParent]
                        have childSeparated :
                            input.frame.val.Encloses input.site child ∨
                              ¬input.frame.val.Encloses child input.site := by
                          rcases separated with belowSite | siteOutside
                          · exact .inl (checked_encloses_trans
                              sourceWellFormed belowSite parentChild)
                          · refine .inr ?_
                            intro childContainsSite
                            exact siteOutside (checked_encloses_trans
                              sourceWellFormed parentChild childContainsSite)
                        have childAway : child ≠ input.site := by
                          intro childAtSite
                          subst child
                          rcases separated with belowSite | siteOutside
                          · exact (checked_direct_child_not_encloses_parent
                              sourceWellFormed sourceParent) belowSite
                          · exact siteOutside parentChild
                        have sourceChildExact := sourceExact.extend_child
                          sourceWellFormed sourceParent
                        have targetParent :
                            (layout.plugRaw.regions
                              (layout.frameRegion child)).parent? =
                                some (layout.frameRegion region) := by
                          rw [layout.plugRegion_frameRegion]
                          exact (layout.mapFrameRegion_parent_eq_some_iff
                            child region).2 sourceParent
                        have targetChildExact := targetExact.extend_child
                          targetWellFormed targetParent
                        simp only [compileOccurrenceWith?, mapFrameOccurrence]
                          at sourceItemCompiled targetItemCompiled
                        cases childRegion : input.frame.val.regions child with
                        | sheet =>
                            simp [childRegion] at sourceItemCompiled
                        | cut parent =>
                            have parentEq : parent = region := by
                              simpa [childRegion, CRegion.parent?] using
                                sourceParent
                            subst parent
                            have targetChildRegion :
                                layout.plugRaw.regions
                                    (layout.frameRegion child) =
                                  .cut (layout.frameRegion region) := by
                              rw [layout.plugRegion_frameRegion, childRegion]
                              rfl
                            cases sourceChildResult : compileRegion?
                                input.frame.val sourceFuel child sourceExtended
                                sourceBinders with
                            | none =>
                                simp [childRegion, sourceChildResult]
                                  at sourceItemCompiled
                            | some sourceChildBody =>
                                simp [childRegion, sourceChildResult]
                                  at sourceItemCompiled
                                subst sourceItem
                                cases targetChildResult : compileRegion?
                                    layout.plugRaw targetFuel
                                    (layout.frameRegion child) targetExtended
                                    (layout.mapFrameBinders sourceBinders) with
                                | none =>
                                    simp [targetChildRegion,
                                      targetChildResult] at targetItemCompiled
                                | some targetChildBody =>
                                    simp [targetChildRegion,
                                      targetChildResult] at targetItemCompiled
                                    subst targetItem
                                    exact congrArg Item.cut
                                      (inductionHypothesis child childSeparated
                                        childAway
                                        sourceExtended targetExtended
                                        extendedWireMap extendedGet
                                        sourceChildExact targetChildExact
                                        sourceBinders targetFuel
                                        sourceChildBody targetChildBody
                                        sourceChildResult targetChildResult)
                        | bubble parent arity =>
                            have parentEq : parent = region := by
                              simpa [childRegion, CRegion.parent?] using
                                sourceParent
                            subst parent
                            have targetChildRegion :
                                layout.plugRaw.regions
                                    (layout.frameRegion child) =
                                  .bubble (layout.frameRegion region) arity := by
                              rw [layout.plugRegion_frameRegion, childRegion]
                              rfl
                            cases sourceChildResult : compileRegion?
                                input.frame.val sourceFuel child sourceExtended
                                (sourceBinders.push child arity) with
                            | none =>
                                simp [childRegion, sourceChildResult]
                                  at sourceItemCompiled
                            | some sourceChildBody =>
                                simp [childRegion, sourceChildResult]
                                  at sourceItemCompiled
                                subst sourceItem
                                cases targetChildResult : compileRegion?
                                    layout.plugRaw targetFuel
                                    (layout.frameRegion child) targetExtended
                                    ((layout.mapFrameBinders sourceBinders).push
                                      (layout.frameRegion child) arity) with
                                | none =>
                                    simp [targetChildRegion,
                                      targetChildResult] at targetItemCompiled
                                | some targetChildBody =>
                                    simp [targetChildRegion,
                                      targetChildResult] at targetItemCompiled
                                    subst targetItem
                                    have targetChildResult' : compileRegion?
                                        layout.plugRaw targetFuel
                                        (layout.frameRegion child) targetExtended
                                        (layout.mapFrameBinders
                                          (sourceBinders.push child arity)) =
                                          some targetChildBody := by
                                      rw [← layout.mapFrameBinders_push]
                                      exact targetChildResult
                                    exact congrArg (Item.bubble arity)
                                      (inductionHypothesis child childSeparated
                                        childAway
                                        sourceExtended targetExtended
                                        extendedWireMap extendedGet
                                        sourceChildExact targetChildExact
                                        (sourceBinders.push child arity)
                                        targetFuel sourceChildBody
                                        targetChildBody sourceChildResult
                                        targetChildResult')
                  have itemsEq := compileOccurrencesWith?_map_of_success
                    (compileRegion? input.frame.val sourceFuel)
                    (compileRegion? layout.plugRaw targetFuel)
                    sourceExtended targetExtended sourceBinders
                    (layout.mapFrameBinders sourceBinders)
                    layout.mapFrameOccurrence extendedWireMap
                    (localOccurrences input.frame.val region)
                    sourceItems targetItems sourceItemsResult
                    targetItemsResult occurrenceMapped
                  rw [itemsEq]
                  simp [finishRegion, Region.renameWires,
                    extendedWireMap,
                    layout.exactScopeWires_frameRegion_length_of_ne
                      consistent terminal region away]
                  rw [ItemSeq.castWiresEq_eq_renameWires,
                    ItemSeq.castWiresEq_eq_renameWires,
                    ItemSeq.renameWires_comp, ItemSeq.renameWires_comp]
                  apply ItemSeq.renameWires_heq_of_val sourceItems
                    _ _ (congrArg (fun localCount =>
                      targetContext.length + localCount)
                      (layout.exactScopeWires_frameRegion_length_of_ne
                        consistent terminal region away))
                  intro index
                  simp [Function.comp_apply, extendFrameContextIndexMap]

/-- Successful recursive compilation of a retained frame region below the
splice site is exactly source compilation renamed through the inherited
frame-position embedding.  The source and target fuels may differ. -/
theorem compileRegion?_frameRegion_map
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (sourceWellFormed : input.frame.val.WellFormed)
    (targetWellFormed : layout.plugRaw.WellFormed)
    (region : Fin input.frame.val.regionCount)
    (belowSite : input.frame.val.Encloses input.site region)
    (away : region ≠ input.site)
    (sourceContext : WireContext input.frame.val)
    (targetContext : WireContext layout.plugRaw)
    (wireMap : Fin sourceContext.length → Fin targetContext.length)
    (getMapped : ∀ index,
      targetContext.get (wireMap index) =
        layout.frameWireEmbedding consistent (sourceContext.get index))
    (sourceExact : (sourceContext.extend region).Exact region)
    (targetExact :
      (targetContext.extend (layout.frameRegion region)).Exact
        (layout.frameRegion region))
    (sourceBinders : BinderContext input.frame.val rels)
    (sourceFuel targetFuel : Nat)
    (sourceBody : Region sourceContext.length rels)
    (targetBody : Region targetContext.length rels)
    (sourceCompiled : compileRegion? input.frame.val sourceFuel region
      sourceContext sourceBinders = some sourceBody)
    (targetCompiled : compileRegion? layout.plugRaw targetFuel
      (layout.frameRegion region) targetContext
      (layout.mapFrameBinders sourceBinders) = some targetBody) :
    targetBody = sourceBody.renameWires wireMap := by
  exact layout.compileRegion?_frameRegion_map_of_separated consistent terminal
    sourceWellFormed targetWellFormed region (.inl belowSite) away
    sourceContext targetContext wireMap getMapped sourceExact targetExact
    sourceBinders sourceFuel targetFuel sourceBody targetBody sourceCompiled
    targetCompiled

/-- Successful recursive compilation of a retained frame subtree disjoint
from the insertion site is exactly the corresponding source compilation.
The non-enclosure premise is source topology and is inherited by all children. -/
theorem compileRegion?_frameRegion_map_of_not_encloses_site
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (sourceWellFormed : input.frame.val.WellFormed)
    (targetWellFormed : layout.plugRaw.WellFormed)
    (region : Fin input.frame.val.regionCount)
    (siteOutside : ¬input.frame.val.Encloses region input.site)
    (sourceContext : WireContext input.frame.val)
    (targetContext : WireContext layout.plugRaw)
    (wireMap : Fin sourceContext.length → Fin targetContext.length)
    (getMapped : ∀ index,
      targetContext.get (wireMap index) =
        layout.frameWireEmbedding consistent (sourceContext.get index))
    (sourceExact : (sourceContext.extend region).Exact region)
    (targetExact :
      (targetContext.extend (layout.frameRegion region)).Exact
        (layout.frameRegion region))
    (sourceBinders : BinderContext input.frame.val rels)
    (sourceFuel targetFuel : Nat)
    (sourceBody : Region sourceContext.length rels)
    (targetBody : Region targetContext.length rels)
    (sourceCompiled : compileRegion? input.frame.val sourceFuel region
      sourceContext sourceBinders = some sourceBody)
    (targetCompiled : compileRegion? layout.plugRaw targetFuel
      (layout.frameRegion region) targetContext
      (layout.mapFrameBinders sourceBinders) = some targetBody) :
    targetBody = sourceBody.renameWires wireMap := by
  apply layout.compileRegion?_frameRegion_map_of_separated consistent terminal
    sourceWellFormed targetWellFormed region (.inr siteOutside)
  · intro atSite
    subst region
    exact siteOutside (Diagram.Encloses.refl input.frame.val input.site)
  · exact getMapped
  · exact sourceExact
  · exact targetExact
  · exact sourceCompiled
  · exact targetCompiled

/-- Given successful source and target child-block computations at the splice
site, the retained target children are exactly the source children renamed by
the stable frame-site position map. -/
theorem compileFrameChildBlock
    (layout : PlugLayout input) (consistent : input.AttachmentConsistent)
    (terminal : input.TerminalBody)
    (sourceWellFormed : input.frame.val.WellFormed)
    (targetWellFormed : layout.plugRaw.WellFormed)
    (sourceContext : WireContext input.frame.val)
    (sourceExact : sourceContext.Exact input.site)
    (targetExact :
      (layout.patternSiteWires consistent sourceContext).Exact
        (layout.frameRegion input.site))
    (sourceBinders : BinderContext input.frame.val rels)
    (sourceFuel targetFuel : Nat)
    (sourceItems : ItemSeq sourceContext.length rels)
    (targetItems : ItemSeq
      (layout.patternSiteWires consistent sourceContext).length rels)
    (sourceCompiled : compileOccurrencesWith? input.frame.val
      (compileRegion? input.frame.val sourceFuel) sourceContext sourceBinders
      (localChildOccurrences input.frame.val input.site) = some sourceItems)
    (targetCompiled : compileOccurrencesWith? layout.plugRaw
      (compileRegion? layout.plugRaw targetFuel)
      (layout.patternSiteWires consistent sourceContext)
      (layout.mapFrameBinders sourceBinders)
      (layout.frameChildOccurrences input.site) = some targetItems) :
    targetItems = sourceItems.renameWires
      (layout.frameSiteIndexMap consistent sourceContext) := by
  have occurrencesEq :
      (localChildOccurrences input.frame.val input.site).map
          layout.mapFrameOccurrence =
        layout.frameChildOccurrences input.site := by
    unfold localChildOccurrences frameChildOccurrences mapFrameOccurrence
    simp only [List.map_map]
    rfl
  rw [← occurrencesEq] at targetCompiled
  apply compileOccurrencesWith?_map_of_success
    (compileRegion? input.frame.val sourceFuel)
    (compileRegion? layout.plugRaw targetFuel)
    sourceContext (layout.patternSiteWires consistent sourceContext)
    sourceBinders (layout.mapFrameBinders sourceBinders)
    layout.mapFrameOccurrence
    (layout.frameSiteIndexMap consistent sourceContext)
    (localChildOccurrences input.frame.val input.site)
    sourceItems targetItems sourceCompiled targetCompiled
  intro occurrence member sourceItem targetItem sourceItemCompiled
    targetItemCompiled
  obtain ⟨child, childMember, occurrenceEq⟩ := List.mem_map.mp member
  subst occurrence
  have sourceParent :
      (input.frame.val.regions child).parent? = some input.site :=
    of_decide_eq_true (List.mem_filter.mp childMember).2
  have siteChild : input.frame.val.Encloses input.site child := by
    refine ⟨⟨1, by
      have := child.isLt
      omega⟩, ?_⟩
    simp [Diagram.climb, sourceParent]
  have childAway : child ≠ input.site := by
    intro childAtSite
    subst child
    exact (checked_direct_child_not_encloses_parent sourceWellFormed
      sourceParent) (Diagram.Encloses.refl input.frame.val input.site)
  have sourceChildExact := sourceExact.extend_child sourceWellFormed sourceParent
  have targetParent :
      (layout.plugRaw.regions (layout.frameRegion child)).parent? =
        some (layout.frameRegion input.site) := by
    rw [layout.plugRegion_frameRegion]
    exact (layout.mapFrameRegion_parent_eq_some_iff
      child input.site).2 sourceParent
  have targetChildExact := targetExact.extend_child targetWellFormed targetParent
  simp only [compileOccurrenceWith?, mapFrameOccurrence]
    at sourceItemCompiled targetItemCompiled
  cases childRegion : input.frame.val.regions child with
  | sheet => simp [childRegion] at sourceItemCompiled
  | cut parent =>
      have parentEq : parent = input.site := by
        simpa [childRegion, CRegion.parent?] using sourceParent
      subst parent
      have targetChildRegion :
          layout.plugRaw.regions (layout.frameRegion child) =
            .cut (layout.frameRegion input.site) := by
        rw [layout.plugRegion_frameRegion, childRegion]
        rfl
      cases sourceChildResult : compileRegion? input.frame.val sourceFuel child
          sourceContext sourceBinders with
      | none => simp [childRegion, sourceChildResult] at sourceItemCompiled
      | some sourceChildBody =>
          simp [childRegion, sourceChildResult] at sourceItemCompiled
          subst sourceItem
          cases targetChildResult : compileRegion? layout.plugRaw targetFuel
              (layout.frameRegion child)
              (layout.patternSiteWires consistent sourceContext)
              (layout.mapFrameBinders sourceBinders) with
          | none =>
              simp [targetChildRegion, targetChildResult] at targetItemCompiled
          | some targetChildBody =>
              simp [targetChildRegion, targetChildResult] at targetItemCompiled
              subst targetItem
              exact congrArg Item.cut
                (layout.compileRegion?_frameRegion_map consistent terminal
                  sourceWellFormed targetWellFormed child siteChild childAway
                  sourceContext
                  (layout.patternSiteWires consistent sourceContext)
                  (layout.frameSiteIndexMap consistent sourceContext)
                  (layout.frameSiteIndexMap_get consistent sourceContext)
                  sourceChildExact targetChildExact sourceBinders
                  sourceFuel targetFuel sourceChildBody targetChildBody
                  sourceChildResult targetChildResult)
  | bubble parent arity =>
      have parentEq : parent = input.site := by
        simpa [childRegion, CRegion.parent?] using sourceParent
      subst parent
      have targetChildRegion :
          layout.plugRaw.regions (layout.frameRegion child) =
            .bubble (layout.frameRegion input.site) arity := by
        rw [layout.plugRegion_frameRegion, childRegion]
        rfl
      cases sourceChildResult : compileRegion? input.frame.val sourceFuel child
          sourceContext (sourceBinders.push child arity) with
      | none => simp [childRegion, sourceChildResult] at sourceItemCompiled
      | some sourceChildBody =>
          simp [childRegion, sourceChildResult] at sourceItemCompiled
          subst sourceItem
          cases targetChildResult : compileRegion? layout.plugRaw targetFuel
              (layout.frameRegion child)
              (layout.patternSiteWires consistent sourceContext)
              ((layout.mapFrameBinders sourceBinders).push
                (layout.frameRegion child) arity) with
          | none =>
              simp [targetChildRegion, targetChildResult] at targetItemCompiled
          | some targetChildBody =>
              simp [targetChildRegion, targetChildResult] at targetItemCompiled
              subst targetItem
              have targetChildResult' : compileRegion? layout.plugRaw targetFuel
                  (layout.frameRegion child)
                  (layout.patternSiteWires consistent sourceContext)
                  (layout.mapFrameBinders
                    (sourceBinders.push child arity)) =
                    some targetChildBody := by
                rw [← layout.mapFrameBinders_push]
                exact targetChildResult
              exact congrArg (Item.bubble arity)
                (layout.compileRegion?_frameRegion_map consistent terminal
                  sourceWellFormed targetWellFormed child siteChild childAway
                  sourceContext
                  (layout.patternSiteWires consistent sourceContext)
                  (layout.frameSiteIndexMap consistent sourceContext)
                  (layout.frameSiteIndexMap_get consistent sourceContext)
                  sourceChildExact targetChildExact
                  (sourceBinders.push child arity) sourceFuel targetFuel
                  sourceChildBody targetChildBody sourceChildResult
                  targetChildResult')

end Splice.Input.PlugLayout

end VisualProof.Concrete
