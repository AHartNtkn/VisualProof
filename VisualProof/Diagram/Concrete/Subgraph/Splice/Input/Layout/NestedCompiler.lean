import VisualProof.Diagram.Concrete.Subgraph.Splice.Input.Layout.OccurrenceCompiler

namespace VisualProof.Diagram.Splice.Input

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram
open VisualProof.Diagram.ConcreteElaboration

namespace PlugLayout

/-- Root counterpart of `compileFrameSiblings_targetCoordinates`.  At a
proper nested site the caller's open-root split itself is an exact context,
so siblings are compiled directly in open coordinates. -/
theorem compileNestedRootSiblings
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root)
    (child : Fin input.coalesceFrameRaw.regionCount)
    (hparent : (input.coalesceFrameRaw.regions child).parent? =
      some input.coalesceFrameRaw.root)
    (sourcePosition : Fin (ConcreteElaboration.localOccurrences
      input.coalesceFrameRaw input.coalesceFrameRaw.root).length)
    (hposition : indexOf? (ConcreteElaboration.localOccurrences
      input.coalesceFrameRaw input.coalesceFrameRaw.root) (.child child) =
        some sourcePosition)
    (tail : RegionRoute input.coalesceFrameRaw child input.site rest)
    (sourceItems : ItemSeq signature
      (coalescedOpenRoot input sourceBoundary).rootWires.length [])
    (targetItems : ItemSeq signature
      (outputOpenRoot input layout sourceBoundary).rootWires.length [])
    (hsourceItems : ConcreteElaboration.compileOccurrencesWith? signature
      input.coalesceFrameRaw
      (ConcreteElaboration.compileRegion? signature input.coalesceFrameRaw
        input.coalesceFrameRaw.regionCount)
      (coalescedOpenRoot input sourceBoundary).rootWires
      ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences input.coalesceFrameRaw
        input.coalesceFrameRaw.root) = some sourceItems)
    (htargetItems : ConcreteElaboration.compileOccurrencesWith? signature
      layout.plugRaw
      (ConcreteElaboration.compileRegion? signature layout.plugRaw
        layout.plugRaw.regionCount)
      (outputOpenRoot input layout sourceBoundary).rootWires
      ConcreteElaboration.BinderContext.empty
      (ConcreteElaboration.localOccurrences layout.plugRaw
        layout.plugRaw.root) = some targetItems) :
    ∃ sourceIndex : Fin sourceItems.length,
      ∃ targetIndex : Fin targetItems.length,
        sourceIndex.val = sourcePosition.val ∧
        targetIndex.val =
          (layout.frameOccurrenceEquiv input.coalesceFrameRaw.root
            (by intro heq; exact hnested heq.symm)
            sourcePosition).val ∧
        Nonempty (ItemSeqIso.Frame
          (nestedRootWireEquiv input layout sourceBoundary hnested)
          sourceIndex targetIndex) := by
  have hrootNe : input.coalesceFrameRaw.root ≠ input.site := by
    intro heq
    exact hnested heq.symm
  let sourceOpen := coalescedOpenRoot input sourceBoundary
  let targetOpen := outputOpenRoot input layout sourceBoundary
  let rootWire := nestedRootWireEquiv input layout sourceBoundary hnested
  let sourceExact := openRootWires_exact
    (checkedCoalescedOpenRoot input hadmissible sourceBoundary sourceRoot)
  let targetExact := openRootWires_exact
    (checkedOutputOpenRoot input layout hadmissible sourceBoundary sourceRoot)
  let sourceCover := ConcreteElaboration.BinderContext.empty_covers_root
    (input.coalesceFrameRaw_wellFormed hadmissible)
  let targetCover := ConcreteElaboration.BinderContext.empty_covers_root
    (layout.plugRaw_wellFormed signature input hadmissible)
  let sourceEnumeration :=
    ConcreteElaboration.BinderContext.Enumeration.empty
      input.coalesceFrameRaw
  have sourceLength := ConcreteElaboration.compileOccurrencesWith?_length
    (ConcreteElaboration.compileRegion? signature input.coalesceFrameRaw
      input.coalesceFrameRaw.regionCount)
    sourceOpen.rootWires ConcreteElaboration.BinderContext.empty hsourceItems
  have targetLength := ConcreteElaboration.compileOccurrencesWith?_length
    (ConcreteElaboration.compileRegion? signature layout.plugRaw
      layout.plugRaw.regionCount)
    targetOpen.rootWires ConcreteElaboration.BinderContext.empty htargetItems
  let positions :=
    (FiniteEquiv.finCast sourceLength).trans
      ((layout.frameOccurrenceEquiv input.coalesceFrameRaw.root hrootNe).trans
        (FiniteEquiv.finCast targetLength.symm))
  let sourceIndex := Fin.cast sourceLength.symm sourcePosition
  let targetPosition :=
    layout.frameOccurrenceEquiv input.coalesceFrameRaw.root hrootNe
      sourcePosition
  let targetIndex := Fin.cast targetLength.symm targetPosition
  have hmapped : positions sourceIndex = targetIndex := by
    apply Fin.ext
    rfl
  refine ⟨sourceIndex, targetIndex, rfl, rfl, ⟨{
    positions := positions
    mapped := hmapped
    siblings := ?_
  }⟩⟩
  intro index hindex
  let occurrenceIndex := Fin.cast sourceLength index
  let targetOccurrenceIndex :=
    layout.frameOccurrenceEquiv input.coalesceFrameRaw.root hrootNe
      occurrenceIndex
  let sourceOriginalIndex := Fin.cast sourceLength.symm occurrenceIndex
  let targetOriginalIndex := Fin.cast targetLength.symm targetOccurrenceIndex
  have hoccurrenceNe : occurrenceIndex ≠ sourcePosition := by
    intro heq
    apply hindex
    apply Fin.ext
    simpa [occurrenceIndex, sourceIndex] using congrArg Fin.val heq
  have hsourceGet := ConcreteElaboration.compileOccurrencesWith?_get
    (ConcreteElaboration.compileRegion? signature input.coalesceFrameRaw
      input.coalesceFrameRaw.regionCount)
    sourceOpen.rootWires ConcreteElaboration.BinderContext.empty hsourceItems
    occurrenceIndex
  have htargetGet := ConcreteElaboration.compileOccurrencesWith?_get
    (ConcreteElaboration.compileRegion? signature layout.plugRaw
      layout.plugRaw.regionCount)
    targetOpen.rootWires ConcreteElaboration.BinderContext.empty htargetItems
    targetOccurrenceIndex
  have htargetOccurrence :
      (ConcreteElaboration.localOccurrences layout.plugRaw
        layout.plugRaw.root).get targetOccurrenceIndex =
        layout.mapFrameOccurrence
          ((ConcreteElaboration.localOccurrences input.coalesceFrameRaw
            input.coalesceFrameRaw.root).get occurrenceIndex) := by
    change
      (ConcreteElaboration.localOccurrences layout.plugRaw
        (layout.frameRegion input.coalesceFrameRaw.root)).get
          (layout.frameOccurrenceEquiv input.coalesceFrameRaw.root hrootNe
            occurrenceIndex) = _
    exact layout.frameOccurrenceEquiv_spec input.coalesceFrameRaw.root
      hrootNe occurrenceIndex
  rw [htargetOccurrence] at htargetGet
  let occurrence := (ConcreteElaboration.localOccurrences
    input.coalesceFrameRaw input.coalesceFrameRaw.root).get occurrenceIndex
  have hoccurrenceMem := List.get_mem
    (ConcreteElaboration.localOccurrences input.coalesceFrameRaw
      input.coalesceFrameRaw.root) occurrenceIndex
  change occurrence ∈ ConcreteElaboration.localOccurrences
    input.coalesceFrameRaw input.coalesceFrameRaw.root at hoccurrenceMem
  change ConcreteElaboration.compileOccurrenceWith? signature
    input.coalesceFrameRaw
    (ConcreteElaboration.compileRegion? signature input.coalesceFrameRaw
      input.coalesceFrameRaw.regionCount)
    sourceOpen.rootWires ConcreteElaboration.BinderContext.empty occurrence =
      some (sourceItems.get sourceOriginalIndex) at hsourceGet
  change ConcreteElaboration.compileOccurrenceWith? signature layout.plugRaw
    (ConcreteElaboration.compileRegion? signature layout.plugRaw
      layout.plugRaw.regionCount)
    targetOpen.rootWires ConcreteElaboration.BinderContext.empty
      (layout.mapFrameOccurrence occurrence) =
        some (targetItems.get targetOriginalIndex) at htargetGet
  have childAway : ∀ sibling, occurrence = .child sibling →
      ¬ input.coalesceFrameRaw.Encloses sibling input.site := by
    intro sibling hsibling
    have siblingParent :=
      (ConcreteElaboration.mem_localOccurrences_child _ _ _).1
        (show ConcreteElaboration.LocalOccurrence.child sibling ∈
          ConcreteElaboration.localOccurrences input.coalesceFrameRaw
            input.coalesceFrameRaw.root by
          rw [← hsibling]
          exact hoccurrenceMem)
    have hsiblingNe : sibling ≠ child := by
      intro heq
      subst sibling
      have hindexOf := indexOf?_get_eq_some_of_nodup
        (ConcreteElaboration.localOccurrences_nodup _ _) occurrenceIndex
      have hsome : some occurrenceIndex = some sourcePosition := by
        rw [← hindexOf, ← hposition]
        congr 1
      exact hoccurrenceNe (Option.some.inj hsome)
    exact RegionRoute.distinctSibling_away
      (input.coalesceFrameRaw_wellFormed hadmissible) tail hparent
      siblingParent hsiblingNe
  have hitem : ItemIso signature rootWire []
      (sourceItems.get sourceOriginalIndex)
      (targetItems.get targetOriginalIndex) := by
    cases hoccurrence : occurrence with
    | node node =>
        rw [hoccurrence] at hoccurrenceMem hsourceGet htargetGet
        have hnodeRegion :=
          (ConcreteElaboration.mem_localOccurrences_node _ _ _).1
            hoccurrenceMem
        have hmap := layout.compileFrameNode_at_region_of_maps signature input
          hadmissible input.coalesceFrameRaw.root sourceOpen.rootWires
          targetOpen.rootWires sourceExact targetExact
          ConcreteElaboration.BinderContext.empty
          ConcreteElaboration.BinderContext.empty sourceCover sourceEnumeration
          rootWire (nestedRootWireEquiv_spec input layout sourceBoundary hnested)
          (fun {_} relation => relation)
          (by intro arity relation; exact Fin.elim0 relation.index)
          node hnodeRegion
        have hsourceNode : ConcreteElaboration.compileNode? signature
            input.coalesceFrameRaw sourceOpen.rootWires
              ConcreteElaboration.BinderContext.empty node =
            some (sourceItems.get sourceOriginalIndex) := by
          simpa [occurrence, ConcreteElaboration.compileOccurrenceWith?] using
            hsourceGet
        have htargetNode : ConcreteElaboration.compileNode? signature
            layout.plugRaw targetOpen.rootWires
              ConcreteElaboration.BinderContext.empty (layout.frameNode node) =
            some (targetItems.get targetOriginalIndex) := by
          simpa [occurrence, PlugLayout.mapFrameOccurrence,
            ConcreteElaboration.compileOccurrenceWith?] using htargetGet
        rw [hsourceNode, htargetNode] at hmap
        have hmapRaw :
            Item.renameRelations (fun {_} relation => relation)
                ((sourceItems.get sourceOriginalIndex).renameWires rootWire) =
              targetItems.get targetOriginalIndex := by
          exact Option.some.inj (by simpa only [Option.map_some] using hmap.symm)
        have hmap' :
            (sourceItems.get sourceOriginalIndex).renameWires rootWire =
              targetItems.get targetOriginalIndex := by
          simpa only [Item.renameRelations_id] using hmapRaw
        rw [← hmap']
        exact ItemIso.renameWiresEquiv _ rootWire
    | child sibling =>
        have haway := childAway sibling hoccurrence
        rw [hoccurrence] at hoccurrenceMem hsourceGet htargetGet
        have siblingParent :=
          (ConcreteElaboration.mem_localOccurrences_child _ _ _).1
            hoccurrenceMem
        cases hsibling : input.coalesceFrameRaw.regions sibling with
        | sheet =>
            change input.frame.val.regions sibling = .sheet at hsibling
            simp [occurrence, ConcreteElaboration.compileOccurrenceWith?,
              hsibling] at hsourceGet
        | cut parent =>
            have hsiblingRaw := hsibling
            change input.frame.val.regions sibling = .cut parent at hsibling
            have hparentEq : parent = input.coalesceFrameRaw.root := by
              simpa [hsibling, CRegion.parent?] using siblingParent
            subst parent
            have htargetSibling :=
              layout.plugRaw_frameRegion_cut sibling
                input.coalesceFrameRaw.root hsibling
            have htargetParent :
                (layout.plugRaw.regions (layout.frameRegion sibling)).parent? =
                  some layout.plugRaw.root := by
              simpa [CRegion.parent?] using
                congrArg CRegion.parent? htargetSibling
            have hsourceChildExact := sourceExact.extend_child
              (input.coalesceFrameRaw_wellFormed hadmissible) siblingParent
            have htargetChildExact := targetExact.extend_child
              (layout.plugRaw_wellFormed signature input hadmissible)
              htargetParent
            cases hsourceChild : ConcreteElaboration.compileRegion? signature
                input.coalesceFrameRaw input.coalesceFrameRaw.regionCount
                sibling sourceOpen.rootWires
                ConcreteElaboration.BinderContext.empty with
            | none =>
                change ConcreteElaboration.compileRegion? signature
                  input.coalesceFrameRaw input.frame.val.regionCount sibling
                  sourceOpen.rootWires
                    ConcreteElaboration.BinderContext.empty = none at hsourceChild
                simp [ConcreteElaboration.compileOccurrenceWith?,
                  hsiblingRaw, hsibling, hsourceChild] at hsourceGet
            | some compiledSource =>
                change ConcreteElaboration.compileRegion? signature
                  input.coalesceFrameRaw input.frame.val.regionCount sibling
                  sourceOpen.rootWires
                    ConcreteElaboration.BinderContext.empty =
                      some compiledSource at hsourceChild
                simp [occurrence, ConcreteElaboration.compileOccurrenceWith?,
                  hsiblingRaw, hsibling, hsourceChild] at hsourceGet
                cases htargetChild : ConcreteElaboration.compileRegion?
                    signature layout.plugRaw layout.plugRaw.regionCount
                    (layout.frameRegion sibling) targetOpen.rootWires
                    ConcreteElaboration.BinderContext.empty with
                | none =>
                    simp [occurrence, PlugLayout.mapFrameOccurrence,
                      ConcreteElaboration.compileOccurrenceWith?,
                      htargetSibling, htargetChild] at htargetGet
                | some compiledTarget =>
                    simp [occurrence, PlugLayout.mapFrameOccurrence,
                      ConcreteElaboration.compileOccurrenceWith?,
                      htargetSibling, htargetChild] at htargetGet
                    have hrecursive := layout.compileFrameRegion_away_from_site
                      signature input hadmissible input.coalesceFrameRaw.regionCount
                      layout.plugRaw.regionCount sibling haway
                      sourceOpen.rootWires targetOpen.rootWires
                      hsourceChildExact htargetChildExact
                      ConcreteElaboration.BinderContext.empty
                      ConcreteElaboration.BinderContext.empty
                      (ConcreteElaboration.BinderContext.covers_cut_child
                        sourceCover hsibling)
                      (ConcreteElaboration.BinderContext.covers_cut_child
                        targetCover htargetSibling)
                      (sourceEnumeration.cutChild
                        (input.coalesceFrameRaw_wellFormed hadmissible) hsibling)
                      rootWire
                      (nestedRootWireEquiv_spec input layout sourceBoundary
                        hnested)
                      (fun {_} relation => relation)
                      (by intro arity relation; exact Fin.elim0 relation.index)
                      compiledSource compiledTarget hsourceChild htargetChild
                    have hrename := RegionIso.renameWiresEquiv compiledSource
                      rootWire
                    have hrecursive' : RegionIso signature
                        (FiniteEquiv.refl _) []
                        (compiledSource.renameWires rootWire)
                        compiledTarget := by
                      simpa [Region.renameRelations_id] using hrecursive
                    have hcombined := hrename.trans hrecursive'
                    have hwire : rootWire.trans (FiniteEquiv.refl _) =
                        rootWire := by
                      apply FiniteEquiv.ext
                      intro wire
                      rfl
                    have hcut : ItemIso signature rootWire []
                        (Item.cut compiledSource) (Item.cut compiledTarget) :=
                      hwire ▸ ItemIso.cut hcombined
                    have hsourceEq : sourceItems.get sourceOriginalIndex =
                        Item.cut compiledSource :=
                      Option.some.inj hsourceGet.symm
                    have htargetEq : targetItems.get targetOriginalIndex =
                        Item.cut compiledTarget :=
                      Option.some.inj htargetGet.symm
                    rw [hsourceEq, htargetEq]
                    exact hcut
        | bubble parent arity =>
            have hsiblingRaw := hsibling
            change input.frame.val.regions sibling =
              .bubble parent arity at hsibling
            have hparentEq : parent = input.coalesceFrameRaw.root := by
              simpa [hsibling, CRegion.parent?] using siblingParent
            subst parent
            have htargetSibling := layout.plugRaw_frameRegion_bubble sibling
              input.coalesceFrameRaw.root arity hsibling
            have htargetParent :
                (layout.plugRaw.regions (layout.frameRegion sibling)).parent? =
                  some layout.plugRaw.root := by
              simpa [CRegion.parent?] using
                congrArg CRegion.parent? htargetSibling
            have hsourceChildExact := sourceExact.extend_child
              (input.coalesceFrameRaw_wellFormed hadmissible) siblingParent
            have htargetChildExact := targetExact.extend_child
              (layout.plugRaw_wellFormed signature input hadmissible)
              htargetParent
            cases hsourceChild : ConcreteElaboration.compileRegion? signature
                input.coalesceFrameRaw input.coalesceFrameRaw.regionCount
                sibling sourceOpen.rootWires
                (ConcreteElaboration.BinderContext.empty.push sibling arity) with
            | none =>
                change ConcreteElaboration.compileRegion? signature
                  input.coalesceFrameRaw input.frame.val.regionCount sibling
                  sourceOpen.rootWires
                    (ConcreteElaboration.BinderContext.empty.push sibling
                      arity) = none at hsourceChild
                simp [ConcreteElaboration.compileOccurrenceWith?,
                  hsiblingRaw, hsibling, hsourceChild] at hsourceGet
            | some compiledSource =>
                change ConcreteElaboration.compileRegion? signature
                  input.coalesceFrameRaw input.frame.val.regionCount sibling
                  sourceOpen.rootWires
                    (ConcreteElaboration.BinderContext.empty.push sibling
                      arity) = some compiledSource at hsourceChild
                simp [occurrence, ConcreteElaboration.compileOccurrenceWith?,
                  hsiblingRaw, hsibling, hsourceChild] at hsourceGet
                cases htargetChild : ConcreteElaboration.compileRegion?
                    signature layout.plugRaw layout.plugRaw.regionCount
                    (layout.frameRegion sibling) targetOpen.rootWires
                    (ConcreteElaboration.BinderContext.empty.push
                      (layout.frameRegion sibling) arity) with
                | none =>
                    simp [occurrence, PlugLayout.mapFrameOccurrence,
                      ConcreteElaboration.compileOccurrenceWith?,
                      htargetSibling, htargetChild] at htargetGet
                | some compiledTarget =>
                    simp [occurrence, PlugLayout.mapFrameOccurrence,
                      ConcreteElaboration.compileOccurrenceWith?,
                      htargetSibling, htargetChild] at htargetGet
                    have hrecursive := layout.compileFrameRegion_away_from_site
                      signature input hadmissible input.coalesceFrameRaw.regionCount
                      layout.plugRaw.regionCount sibling haway
                      sourceOpen.rootWires targetOpen.rootWires
                      hsourceChildExact htargetChildExact
                      (ConcreteElaboration.BinderContext.empty.push sibling arity)
                      (ConcreteElaboration.BinderContext.empty.push
                        (layout.frameRegion sibling) arity)
                      (ConcreteElaboration.BinderContext.push_covers_bubble_child
                        sourceCover hsibling)
                      (ConcreteElaboration.BinderContext.push_covers_bubble_child
                        targetCover htargetSibling)
                      (sourceEnumeration.bubbleChild
                        (input.coalesceFrameRaw_wellFormed hadmissible) hsibling)
                      rootWire
                      (nestedRootWireEquiv_spec input layout sourceBoundary
                        hnested)
                      (RelationRenaming.lift (fun {_} relation => relation) arity)
                      (layout.frameRelationLookup_bubbleChild hadmissible
                        input.coalesceFrameRaw.root sibling
                        ConcreteElaboration.BinderContext.empty
                        ConcreteElaboration.BinderContext.empty
                        sourceEnumeration arity hsibling
                        (fun {_} relation => relation)
                        (by intro a relation; exact Fin.elim0 relation.index))
                      compiledSource compiledTarget hsourceChild htargetChild
                    have hrename := RegionIso.renameWiresEquiv compiledSource
                      rootWire
                    have hrecursive' : RegionIso signature
                        (FiniteEquiv.refl _) [arity]
                        (compiledSource.renameWires rootWire)
                        compiledTarget := by
                      simpa [Region.renameRelations_id,
                        RelationRenaming.lift_id_fun] using hrecursive
                    have hcombined := hrename.trans hrecursive'
                    have hwire : rootWire.trans (FiniteEquiv.refl _) =
                        rootWire := by
                      apply FiniteEquiv.ext
                      intro wire
                      rfl
                    have hbubble : ItemIso signature rootWire []
                        (Item.bubble arity compiledSource)
                        (Item.bubble arity compiledTarget) :=
                      hwire ▸ ItemIso.bubble hcombined
                    have hsourceEq : sourceItems.get sourceOriginalIndex =
                        Item.bubble arity compiledSource :=
                      Option.some.inj hsourceGet.symm
                    have htargetEq : targetItems.get targetOriginalIndex =
                        Item.bubble arity compiledTarget :=
                      Option.some.inj htargetGet.symm
                    rw [hsourceEq, htargetEq]
                    exact hbubble
  have hsourcePosition : sourceOriginalIndex = index := by
    apply Fin.ext
    rfl
  have htargetPosition : targetOriginalIndex = positions index := by
    apply Fin.ext
    rfl
  rw [← htargetPosition, ← hsourcePosition]
  exact hitem

theorem compileHostOccurrence_at_seam_iso_of_maps
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    {preparedWires : Nat}
    (combined : FiniteEquiv (Fin preparedWires)
      (Fin (outputLeaf.inheritedWires.length +
        (ConcreteElaboration.exactScopeWires layout.plugRaw
          (layout.frameRegion input.site)).length)))
    (sourcePreparedMap : Fin
        (host.compilerLeaf.inheritedWires.extend input.site).length →
      Fin preparedWires)
    (hwire :
      (combined.trans (FiniteEquiv.finCast
        (ConcreteElaboration.WireContext.length_extend
          outputLeaf.inheritedWires
          (layout.frameRegion input.site)).symm)).toFun ∘
          sourcePreparedMap =
        layout.hostSiteWireIndexMap host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf)
    (occurrence : ConcreteElaboration.LocalOccurrence
      input.coalesceFrameRaw.regionCount input.coalesceFrameRaw.nodeCount)
    (hoccurrence : occurrence ∈ ConcreteElaboration.localOccurrences
      input.coalesceFrameRaw input.site)
    (sourceItem : Item signature
      (host.compilerLeaf.inheritedWires.extend input.site).length
      host.intrinsicPath.toFocus.holeRels)
    (targetItem : Item signature
      (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).length
      outputWitness.toFocus.holeRels)
    (hsource : ConcreteElaboration.compileOccurrenceWith? signature
      input.coalesceFrameRaw
      (ConcreteElaboration.compileRegion? signature input.coalesceFrameRaw
        host.compilerLeaf.fuel)
      (host.compilerLeaf.inheritedWires.extend input.site)
      host.compilerLeaf.binders occurrence = some sourceItem)
    (htarget : ConcreteElaboration.compileOccurrenceWith? signature
      layout.plugRaw
      (ConcreteElaboration.compileRegion? signature layout.plugRaw
        outputLeaf.fuel)
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      outputLeaf.binders (layout.mapFrameOccurrence occurrence) =
        some targetItem) :
    ItemIso signature
      combined
      outputWitness.toFocus.holeRels
      ((sourceItem.renameWires
        sourcePreparedMap).renameRelations
        (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf))
      (targetItem.castWiresEq
        (ConcreteElaboration.WireContext.length_extend
          outputLeaf.inheritedWires (layout.frameRegion input.site))) := by
  cases occurrence with
  | node node =>
      have hnodeRegion :=
        (ConcreteElaboration.mem_localOccurrences_node _ _ _).1 hoccurrence
      apply layout.compileHostNode_at_seam_iso_of_maps signature input
        hadmissible host outputWitness outputLeaf combined sourcePreparedMap
      · funext index
        have h := congrFun hwire index
        apply Fin.ext
        simpa only [FiniteEquiv.trans_apply, FiniteEquiv.finCast,
          Function.comp_apply] using congrArg Fin.val h
      · exact hnodeRegion
      · exact
        (by simpa [ConcreteElaboration.compileOccurrenceWith?,
          Input.coalesceFrame] using hsource)
      · exact (by simpa [mapFrameOccurrence,
          ConcreteElaboration.compileOccurrenceWith?] using htarget)
  | child child =>
      have hparent :=
        (ConcreteElaboration.mem_localOccurrences_child _ _ _).1 hoccurrence
      change (input.frame.val.regions child).parent? = some input.site at hparent
      have hbelow : input.coalesceFrameRaw.Encloses input.site child := by
        refine ⟨⟨1, by
          have := child.isLt
          omega⟩, ?_⟩
        simp [ConcreteDiagram.climb, hparent]
      have hchildNeSite : child ≠ input.site := by
        intro heq
        subst child
        exact ConcreteElaboration.checked_direct_child_not_encloses_parent
          (input.coalesceFrameRaw_wellFormed hadmissible) hparent
          (ConcreteDiagram.Encloses.refl input.coalesceFrameRaw input.site)
      have htargetParent :
          (layout.plugRaw.regions (layout.frameRegion child)).parent? =
            some (layout.frameRegion input.site) := by
        cases hchild : input.frame.val.regions child with
        | sheet => simp [hchild, CRegion.parent?] at hparent
        | cut parent =>
            have hparentEq : parent = input.site := by
              simpa [hchild, CRegion.parent?] using hparent
            subst parent
            simpa [CRegion.parent?] using congrArg CRegion.parent?
              (layout.plugRaw_frameRegion_cut child input.site hchild)
        | bubble parent arity =>
            have hparentEq : parent = input.site := by
              simpa [hchild, CRegion.parent?] using hparent
            subst parent
            simpa [CRegion.parent?] using congrArg CRegion.parent?
              (layout.plugRaw_frameRegion_bubble child input.site arity hchild)
      have hsourceChildExact := host.compilerLeaf.wiresExact.extend_child
        (input.coalesceFrameRaw_wellFormed hadmissible) hparent
      have htargetChildExact := outputLeaf.wiresExact.extend_child
        (layout.plugRaw_wellFormed signature input hadmissible) htargetParent
      let targetEq := ConcreteElaboration.WireContext.length_extend
        outputLeaf.inheritedWires (layout.frameRegion input.site)
      cases hchild : input.frame.val.regions child with
      | sheet =>
          simp [ConcreteElaboration.compileOccurrenceWith?, hchild] at hsource
      | cut parent =>
          have hparentEq : parent = input.site := by
            simpa [hchild, CRegion.parent?] using hparent
          subst parent
          have htargetChild := layout.plugRaw_frameRegion_cut child input.site
            hchild
          cases hsourceChild : ConcreteElaboration.compileRegion? signature
              input.coalesceFrameRaw host.compilerLeaf.fuel child
              (host.compilerLeaf.inheritedWires.extend input.site)
              host.compilerLeaf.binders with
          | none =>
              simp [ConcreteElaboration.compileOccurrenceWith?, hchild,
                hsourceChild] at hsource
          | some compiledSource =>
              simp [ConcreteElaboration.compileOccurrenceWith?, hchild,
                hsourceChild] at hsource
              have hsourceEq : sourceItem = Item.cut compiledSource :=
                (Option.some.inj hsource).symm
              subst sourceItem
              cases htargetChildResult : ConcreteElaboration.compileRegion?
                  signature layout.plugRaw outputLeaf.fuel
                  (layout.frameRegion child)
                  (outputLeaf.inheritedWires.extend
                    (layout.frameRegion input.site)) outputLeaf.binders with
              | none =>
                  simp [mapFrameOccurrence,
                    ConcreteElaboration.compileOccurrenceWith?, htargetChild,
                    htargetChildResult] at htarget
              | some compiledTarget =>
                  simp [mapFrameOccurrence,
                    ConcreteElaboration.compileOccurrenceWith?, htargetChild,
                    htargetChildResult] at htarget
                  have htargetEq : targetItem = Item.cut compiledTarget :=
                    htarget.symm
                  subst targetItem
                  have hrecursive := layout.compileFrameRegion_below_site
                    signature input hadmissible host.compilerLeaf.fuel
                    outputLeaf.fuel child hchildNeSite hbelow
                    (host.compilerLeaf.inheritedWires.extend input.site)
                    (outputLeaf.inheritedWires.extend
                      (layout.frameRegion input.site))
                    hsourceChildExact htargetChildExact
                    host.compilerLeaf.binders outputLeaf.binders
                    (ConcreteElaboration.BinderContext.covers_cut_child
                      host.compilerLeaf.bindersCover hchild)
                    (ConcreteElaboration.BinderContext.covers_cut_child
                      outputLeaf.bindersCover htargetChild)
                    (host.compilerLeaf.binderEnumeration.cutChild
                      (input.coalesceFrameRaw_wellFormed hadmissible) hchild)
                    (layout.hostSiteWireIndexMap host.intrinsicPath
                      host.compilerLeaf outputWitness outputLeaf)
                    (layout.hostSiteWireIndexMap_spec host.intrinsicPath
                      host.compilerLeaf outputWitness outputLeaf)
                    (layout.hostRelationRenaming host.intrinsicPath
                      host.compilerLeaf outputWitness outputLeaf)
                    (layout.frameRelationLookup_cutChild hadmissible input.site
                      child host.compilerLeaf.binders outputLeaf.binders
                      host.compilerLeaf.binderEnumeration hchild
                      (layout.hostRelationRenaming host.intrinsicPath
                        host.compilerLeaf outputWitness outputLeaf)
                      (layout.hostRelationRenaming_lookup host.intrinsicPath
                        host.compilerLeaf outputWitness outputLeaf))
                    compiledSource compiledTarget hsourceChild
                    htargetChildResult
                  have htransport := seamRecursiveRegionIso_of_maps combined
                    targetEq
                    sourcePreparedMap
                    (layout.hostSiteWireIndexMap host.intrinsicPath
                      host.compilerLeaf outputWitness outputLeaf)
                    hwire
                    (layout.hostRelationRenaming host.intrinsicPath
                      host.compilerLeaf outputWitness outputLeaf)
                    compiledSource compiledTarget hrecursive
                  simpa [Item.renameWires, Item.renameRelations] using
                    ItemIso.cut htransport
      | bubble parent arity =>
          have hparentEq : parent = input.site := by
            simpa [hchild, CRegion.parent?] using hparent
          subst parent
          have htargetChild := layout.plugRaw_frameRegion_bubble child
            input.site arity hchild
          cases hsourceChild : ConcreteElaboration.compileRegion? signature
              input.coalesceFrameRaw host.compilerLeaf.fuel child
              (host.compilerLeaf.inheritedWires.extend input.site)
              (host.compilerLeaf.binders.push child arity) with
          | none =>
              simp [ConcreteElaboration.compileOccurrenceWith?, hchild] at hsource
              let wrap := fun body : Region signature
                  (host.compilerLeaf.inheritedWires.extend input.site).length
                  (arity :: host.intrinsicPath.toFocus.holeRels) =>
                some (Item.bubble arity body)
              have hbound := congrArg (fun result => result.bind wrap)
                hsourceChild
              have himpossible : (none : Option (Item signature
                  (host.compilerLeaf.inheritedWires.extend input.site).length
                  host.intrinsicPath.toFocus.holeRels)) = some sourceItem := by
                exact (by simpa only [wrap, Option.bind_none] using
                  hbound.symm.trans hsource)
              contradiction
          | some compiledSource =>
              simp [ConcreteElaboration.compileOccurrenceWith?, hchild] at hsource
              let wrap := fun body : Region signature
                  (host.compilerLeaf.inheritedWires.extend input.site).length
                  (arity :: host.intrinsicPath.toFocus.holeRels) =>
                some (Item.bubble arity body)
              have hbound := congrArg (fun result => result.bind wrap)
                hsourceChild
              have hbubbleEq : Item.bubble arity compiledSource =
                  sourceItem := by
                exact Option.some.inj (by
                  simpa only [wrap, Option.bind_some] using
                    hbound.symm.trans hsource)
              have hsourceEq : sourceItem =
                  Item.bubble arity compiledSource :=
                hbubbleEq.symm
              subst sourceItem
              cases htargetChildResult : ConcreteElaboration.compileRegion?
                  signature layout.plugRaw outputLeaf.fuel
                  (layout.frameRegion child)
                  (outputLeaf.inheritedWires.extend
                    (layout.frameRegion input.site))
                  (outputLeaf.binders.push (layout.frameRegion child) arity) with
              | none =>
                  simp [mapFrameOccurrence,
                    ConcreteElaboration.compileOccurrenceWith?, htargetChild,
                    htargetChildResult] at htarget
              | some compiledTarget =>
                  simp [mapFrameOccurrence,
                    ConcreteElaboration.compileOccurrenceWith?, htargetChild,
                    htargetChildResult] at htarget
                  have htargetEq : targetItem =
                      Item.bubble arity compiledTarget :=
                    htarget.symm
                  subst targetItem
                  have hrecursive := layout.compileFrameRegion_below_site
                    signature input hadmissible host.compilerLeaf.fuel
                    outputLeaf.fuel child hchildNeSite hbelow
                    (host.compilerLeaf.inheritedWires.extend input.site)
                    (outputLeaf.inheritedWires.extend
                      (layout.frameRegion input.site))
                    hsourceChildExact htargetChildExact
                    (host.compilerLeaf.binders.push child arity)
                    (outputLeaf.binders.push (layout.frameRegion child) arity)
                    (ConcreteElaboration.BinderContext.push_covers_bubble_child
                      host.compilerLeaf.bindersCover hchild)
                    (ConcreteElaboration.BinderContext.push_covers_bubble_child
                      outputLeaf.bindersCover htargetChild)
                    (host.compilerLeaf.binderEnumeration.bubbleChild
                      (input.coalesceFrameRaw_wellFormed hadmissible) hchild)
                    (layout.hostSiteWireIndexMap host.intrinsicPath
                      host.compilerLeaf outputWitness outputLeaf)
                    (layout.hostSiteWireIndexMap_spec host.intrinsicPath
                      host.compilerLeaf outputWitness outputLeaf)
                    (RelationRenaming.lift
                      (layout.hostRelationRenaming host.intrinsicPath
                        host.compilerLeaf outputWitness outputLeaf) arity)
                    (layout.frameRelationLookup_bubbleChild hadmissible
                      input.site child host.compilerLeaf.binders
                      outputLeaf.binders host.compilerLeaf.binderEnumeration
                      arity hchild
                      (layout.hostRelationRenaming host.intrinsicPath
                        host.compilerLeaf outputWitness outputLeaf)
                      (layout.hostRelationRenaming_lookup host.intrinsicPath
                        host.compilerLeaf outputWitness outputLeaf))
                    compiledSource compiledTarget hsourceChild
                    htargetChildResult
                  have htransport := seamRecursiveRegionIso_of_maps combined
                    targetEq
                    sourcePreparedMap
                    (layout.hostSiteWireIndexMap host.intrinsicPath
                      host.compilerLeaf outputWitness outputLeaf)
                    hwire
                    (RelationRenaming.lift
                      (layout.hostRelationRenaming host.intrinsicPath
                        host.compilerLeaf outputWitness outputLeaf) arity)
                    compiledSource compiledTarget hrecursive
                  simpa [Item.renameWires, Item.renameRelations] using
                    ItemIso.bubble htransport

theorem compileHostOccurrence_at_seam_iso
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (occurrence : ConcreteElaboration.LocalOccurrence
      input.coalesceFrameRaw.regionCount input.coalesceFrameRaw.nodeCount)
    (hoccurrence : occurrence ∈ ConcreteElaboration.localOccurrences
      input.coalesceFrameRaw input.site)
    (sourceItem : Item signature
      (host.compilerLeaf.inheritedWires.extend input.site).length
      host.intrinsicPath.toFocus.holeRels)
    (targetItem : Item signature
      (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).length
      outputWitness.toFocus.holeRels)
    (hsource : ConcreteElaboration.compileOccurrenceWith? signature
      input.coalesceFrameRaw
      (ConcreteElaboration.compileRegion? signature input.coalesceFrameRaw
        host.compilerLeaf.fuel)
      (host.compilerLeaf.inheritedWires.extend input.site)
      host.compilerLeaf.binders occurrence = some sourceItem)
    (htarget : ConcreteElaboration.compileOccurrenceWith? signature
      layout.plugRaw
      (ConcreteElaboration.compileRegion? signature layout.plugRaw
        outputLeaf.fuel)
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      outputLeaf.binders (layout.mapFrameOccurrence occurrence) =
        some targetItem) :
    ItemIso signature
      (layout.siteCombinedWireEquivOfNonempty hadmissible host
        (outputWitness := outputWitness) (outputLeaf := outputLeaf) hnonempty)
      outputWitness.toFocus.holeRels
      ((sourceItem.renameWires
        (layout.hostSeamPreparedWireOfNonempty hadmissible host)).renameRelations
        (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf))
      (targetItem.castWiresEq
        (ConcreteElaboration.WireContext.length_extend
          outputLeaf.inheritedWires (layout.frameRegion input.site))) := by
  apply layout.compileHostOccurrence_at_seam_iso_of_maps signature input
    hadmissible host outputWitness outputLeaf
    (layout.siteCombinedWireEquivOfNonempty hadmissible host outputWitness
      outputLeaf hnonempty)
    (layout.hostSeamPreparedWireOfNonempty hadmissible host)
  · simpa only [FiniteEquiv.trans_apply, FiniteEquiv.finCast,
      Function.comp_def] using
      layout.hostSeamWireMapOfNonempty_eq hadmissible host outputWitness
        outputLeaf hnonempty
  · exact hoccurrence
  · exact hsource
  · exact htarget

theorem compileHostOccurrence_at_seam_iso_of_empty
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hzero : input.binderSpine.proxyCount = 0)
    (occurrence : ConcreteElaboration.LocalOccurrence
      input.coalesceFrameRaw.regionCount input.coalesceFrameRaw.nodeCount)
    (hoccurrence : occurrence ∈ ConcreteElaboration.localOccurrences
      input.coalesceFrameRaw input.site)
    (sourceItem : Item signature
      (host.compilerLeaf.inheritedWires.extend input.site).length
      host.intrinsicPath.toFocus.holeRels)
    (targetItem : Item signature
      (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).length
      outputWitness.toFocus.holeRels)
    (hsource : ConcreteElaboration.compileOccurrenceWith? signature
      input.coalesceFrameRaw
      (ConcreteElaboration.compileRegion? signature input.coalesceFrameRaw
        host.compilerLeaf.fuel)
      (host.compilerLeaf.inheritedWires.extend input.site)
      host.compilerLeaf.binders occurrence = some sourceItem)
    (htarget : ConcreteElaboration.compileOccurrenceWith? signature
      layout.plugRaw
      (ConcreteElaboration.compileRegion? signature layout.plugRaw
        outputLeaf.fuel)
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      outputLeaf.binders (layout.mapFrameOccurrence occurrence) =
        some targetItem) :
    ItemIso signature
      (layout.siteCombinedWireEquivOfEmpty hadmissible host
        (outputWitness := outputWitness) (outputLeaf := outputLeaf) hzero)
      outputWitness.toFocus.holeRels
      ((sourceItem.renameWires
        (layout.hostSeamPreparedWireOfEmpty hadmissible host)).renameRelations
        (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf))
      (targetItem.castWiresEq
        (ConcreteElaboration.WireContext.length_extend
          outputLeaf.inheritedWires (layout.frameRegion input.site))) := by
  apply layout.compileHostOccurrence_at_seam_iso_of_maps signature input
    hadmissible host outputWitness outputLeaf
    (layout.siteCombinedWireEquivOfEmpty hadmissible host outputWitness
      outputLeaf hzero)
    (layout.hostSeamPreparedWireOfEmpty hadmissible host)
  · simpa only [FiniteEquiv.trans_apply, FiniteEquiv.finCast,
      Function.comp_def] using
      layout.hostSeamWireMapOfEmpty_eq hadmissible host outputWitness
        outputLeaf hzero
  · exact hoccurrence
  · exact hsource
  · exact htarget

theorem terminalRelationLookup_bubbleChild
    (layout : PlugLayout input)
    (parent child : Fin input.pattern.val.diagram.regionCount)
    (hchildMaterial : input.binderSpine.IsMaterialRegion child)
    (sourceBinders : ConcreteElaboration.BinderContext
      input.pattern.val.diagram sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      layout.plugRaw targetRels)
    (sourceEnumeration : ConcreteElaboration.BinderContext.Enumeration
      input.pattern.val.diagram sourceBinders parent)
    (childArity : Nat)
    (hchild : input.pattern.val.diagram.regions child =
      .bubble parent childArity)
    (relationMap : RelationRenaming sourceRels targetRels)
    (relationSpec : ∀ {arity} (relation : Theory.RelVar sourceRels arity),
      targetBinders
          (layout.binderRegion
            (sourceEnumeration.binder relation.index)) =
        some ⟨arity, relationMap relation⟩)
    {arity : Nat}
    (relation : Theory.RelVar (childArity :: sourceRels) arity) :
    (targetBinders.push (layout.bodyRegion child) childArity)
        (layout.binderRegion
          ((sourceEnumeration.bubbleChild
            input.pattern.property.diagram_well_formed hchild).binder
              relation.index)) =
      some ⟨arity,
        RelationRenaming.lift relationMap childArity relation⟩ := by
  have hparent : (input.pattern.val.diagram.regions child).parent? =
      some parent := by simp [hchild, CRegion.parent?]
  rcases relation with ⟨index, hasArity⟩
  revert hasArity
  refine Fin.cases ?_ (fun tail => ?_) index
  · intro hasArity
    have harity : arity = childArity := by simpa using hasArity.symm
    subst arity
    change (targetBinders.push (layout.bodyRegion child) childArity)
        (layout.binderRegion child) =
      some ⟨childArity,
        RelationRenaming.lift relationMap childArity ⟨0, rfl⟩⟩
    rw [layout.binderRegion_material child hchildMaterial,
      ConcreteElaboration.BinderContext.push_self]
    rfl
  · intro hasArity
    let sourceRelation : Theory.RelVar sourceRels arity :=
      ⟨tail, by simpa using hasArity⟩
    obtain ⟨binderParent, hbinder⟩ := sourceEnumeration.bubble tail
    have hne := layout.binderRegion_ne_bodyRegion_directMaterialChild
      parent child (sourceEnumeration.binder tail) hchildMaterial hparent
      binderParent (sourceRels.get tail) hbinder
      (sourceEnumeration.encloses tail)
    change (targetBinders.push (layout.bodyRegion child) childArity)
        (layout.binderRegion (sourceEnumeration.binder tail)) =
      some ⟨arity,
        RelationRenaming.lift relationMap childArity
          ⟨tail.succ, hasArity⟩⟩
    rw [ConcreteElaboration.BinderContext.push_other targetBinders
      childArity hne, relationSpec sourceRelation]
    rfl

theorem compilePatternOccurrence_at_seam_iso
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Region.ContextPath.CompilerLeaf input.pattern.val.diagram
      input.binderSpine.bodyContainer patternWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (occurrence : ConcreteElaboration.LocalOccurrence
      input.pattern.val.diagram.regionCount
      input.pattern.val.diagram.nodeCount)
    (hoccurrence : occurrence ∈ ConcreteElaboration.localOccurrences
      input.pattern.val.diagram input.binderSpine.bodyContainer)
    (sourceItem : Item signature
      (patternLeaf.inheritedWires.extend
        input.binderSpine.bodyContainer).length
      patternWitness.toFocus.holeRels)
    (targetItem : Item signature
      (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).length
      outputWitness.toFocus.holeRels)
    (hsource : ConcreteElaboration.compileOccurrenceWith? signature
      input.pattern.val.diagram
      (ConcreteElaboration.compileRegion? signature input.pattern.val.diagram
        patternLeaf.fuel)
      (patternLeaf.inheritedWires.extend input.binderSpine.bodyContainer)
      patternLeaf.binders occurrence = some sourceItem)
    (htarget : ConcreteElaboration.compileOccurrenceWith? signature
      layout.plugRaw
      (ConcreteElaboration.compileRegion? signature layout.plugRaw
        outputLeaf.fuel)
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      outputLeaf.binders (layout.mapPatternOccurrence occurrence) =
        some targetItem) :
    ItemIso signature
      (layout.siteCombinedWireEquivOfNonempty hadmissible host
        (outputWitness := outputWitness) (outputLeaf := outputLeaf) hnonempty)
      outputWitness.toFocus.holeRels
      ((sourceItem.renameWires
        (layout.patternSeamPreparedWireOfNonempty hadmissible host
          patternWitness patternLeaf hnonempty)).renameRelations
        (fun {arity} relation =>
          layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
            outputWitness outputLeaf
            (layout.coalescedTerminalRelationRenaming hadmissible
              host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
              hnonempty relation)))
      (targetItem.castWiresEq
        (ConcreteElaboration.WireContext.length_extend
          outputLeaf.inheritedWires (layout.frameRegion input.site))) := by
  let combined := layout.siteCombinedWireEquivOfNonempty hadmissible host
    outputWitness outputLeaf hnonempty
  let targetEq := ConcreteElaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  let toTargetContext := combined.trans (FiniteEquiv.finCast targetEq.symm)
  have hwire : toTargetContext.toFun ∘
        layout.patternSeamPreparedWireOfNonempty hadmissible host
          patternWitness patternLeaf hnonempty =
      layout.patternSiteWireIndexMap hadmissible patternWitness patternLeaf
        outputWitness outputLeaf := by
    simpa only [toTargetContext, combined, FiniteEquiv.trans_apply,
      FiniteEquiv.finCast, Function.comp_def] using
      layout.patternSeamWireMapOfNonempty_eq hadmissible host patternWitness
        patternLeaf outputWitness outputLeaf hnonempty
  have hrelations := layout.terminalRelationRenaming_factor hadmissible
    host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
    outputWitness outputLeaf hnonempty
  cases occurrence with
  | node node =>
      have hnodeRegion :=
        (ConcreteElaboration.mem_localOccurrences_node _ _ _).1 hoccurrence
      exact layout.compilePatternNode_at_seam_iso signature input hadmissible
        host patternWitness patternLeaf outputWitness outputLeaf hnonempty node
        hnodeRegion sourceItem targetItem
        (by simpa [ConcreteElaboration.compileOccurrenceWith?] using hsource)
        (by simpa [mapPatternOccurrence,
          ConcreteElaboration.compileOccurrenceWith?] using htarget)
  | child child =>
      have hparent :=
        (ConcreteElaboration.mem_localOccurrences_child _ _ _).1 hoccurrence
      have hmaterial := directChildOfBody_material input child hparent
      cases hchild : input.pattern.val.diagram.regions child with
      | sheet =>
          simp [ConcreteElaboration.compileOccurrenceWith?, hchild] at hsource
      | cut parent =>
          have hparentEq : parent = input.binderSpine.bodyContainer := by
            simpa [hchild, CRegion.parent?] using hparent
          subst parent
          have htargetChild := layout.plugRaw_bodyRegion_cut child
            input.binderSpine.bodyContainer hmaterial hchild
          have htargetChildAtSite : layout.plugRaw.regions
              (layout.bodyRegion child) =
                CRegion.cut (layout.frameRegion input.site) := by
            simpa only [layout.bodyRegion_bodyContainer] using htargetChild
          have hsourceChildExact := patternLeaf.wiresExact.extend_child
            input.pattern.property.diagram_well_formed hparent
          have htargetParent :=
            (layout.bodyRegion_parent_exact child
              input.binderSpine.bodyContainer hmaterial hparent).trans
              (congrArg some layout.bodyRegion_bodyContainer)
          have htargetChildExact := outputLeaf.wiresExact.extend_child
            (layout.plugRaw_wellFormed signature input hadmissible)
            htargetParent
          cases hsourceChild : ConcreteElaboration.compileRegion? signature
              input.pattern.val.diagram patternLeaf.fuel child
              (patternLeaf.inheritedWires.extend
                input.binderSpine.bodyContainer) patternLeaf.binders with
          | none =>
              simp [ConcreteElaboration.compileOccurrenceWith?, hchild,
                hsourceChild] at hsource
          | some compiledSource =>
              simp [ConcreteElaboration.compileOccurrenceWith?, hchild,
                hsourceChild] at hsource
              have hsourceEq : sourceItem = Item.cut compiledSource :=
                hsource.symm
              subst sourceItem
              cases htargetChildResult : ConcreteElaboration.compileRegion?
                  signature layout.plugRaw outputLeaf.fuel
                  (layout.bodyRegion child)
                  (outputLeaf.inheritedWires.extend
                    (layout.frameRegion input.site)) outputLeaf.binders with
              | none =>
                  simp [mapPatternOccurrence,
                    ConcreteElaboration.compileOccurrenceWith?, htargetChild,
                    htargetChildResult] at htarget
              | some compiledTarget =>
                  simp [mapPatternOccurrence,
                    ConcreteElaboration.compileOccurrenceWith?, htargetChild,
                    htargetChildResult] at htarget
                  have htargetEq : targetItem = Item.cut compiledTarget :=
                    htarget.symm
                  subst targetItem
                  have hrecursive := layout.compilePatternRegion_at_material
                    signature input hadmissible patternLeaf.fuel
                    outputLeaf.fuel child hmaterial
                    (patternLeaf.inheritedWires.extend
                      input.binderSpine.bodyContainer)
                    (outputLeaf.inheritedWires.extend
                      (layout.frameRegion input.site))
                    hsourceChildExact htargetChildExact
                    patternLeaf.binders outputLeaf.binders
                    (ConcreteElaboration.BinderContext.covers_cut_child
                      patternLeaf.bindersCover hchild)
                    (ConcreteElaboration.BinderContext.covers_cut_child
                      outputLeaf.bindersCover htargetChildAtSite)
                    (patternLeaf.binderEnumeration.cutChild
                      input.pattern.property.diagram_well_formed hchild)
                    (layout.patternSiteWireIndexMap hadmissible patternWitness
                      patternLeaf outputWitness outputLeaf)
                    (layout.patternSiteWireIndexMap_spec hadmissible
                      patternWitness patternLeaf outputWitness outputLeaf)
                    (layout.patternRelationRenaming hadmissible patternWitness
                      patternLeaf outputWitness outputLeaf)
                    (layout.materialRelationLookup_cutChild
                      input.binderSpine.bodyContainer child patternLeaf.binders
                      outputLeaf.binders patternLeaf.binderEnumeration hchild
                      (layout.patternRelationRenaming hadmissible patternWitness
                        patternLeaf outputWitness outputLeaf)
                      (layout.patternRelationRenaming_lookup hadmissible
                        patternWitness patternLeaf outputWitness outputLeaf))
                    compiledSource compiledTarget hsourceChild
                    htargetChildResult
                  have htransport := seamRecursiveRegionIso_of_maps combined
                    targetEq
                    (layout.patternSeamPreparedWireOfNonempty hadmissible host
                      patternWitness patternLeaf hnonempty)
                    (layout.patternSiteWireIndexMap hadmissible patternWitness
                      patternLeaf outputWitness outputLeaf)
                    hwire
                    (layout.patternRelationRenaming hadmissible patternWitness
                      patternLeaf outputWitness outputLeaf)
                    compiledSource compiledTarget hrecursive
                  simpa [hrelations, Item.renameWires, Item.renameRelations] using
                    ItemIso.cut htransport
      | bubble parent arity =>
          have hparentEq : parent = input.binderSpine.bodyContainer := by
            simpa [hchild, CRegion.parent?] using hparent
          subst parent
          have htargetChild := layout.plugRaw_bodyRegion_bubble child
            input.binderSpine.bodyContainer arity hmaterial hchild
          have htargetChildAtSite : layout.plugRaw.regions
              (layout.bodyRegion child) =
                CRegion.bubble (layout.frameRegion input.site) arity := by
            simpa only [layout.bodyRegion_bodyContainer] using htargetChild
          have hsourceChildExact := patternLeaf.wiresExact.extend_child
            input.pattern.property.diagram_well_formed hparent
          have htargetParent :=
            (layout.bodyRegion_parent_exact child
              input.binderSpine.bodyContainer hmaterial hparent).trans
              (congrArg some layout.bodyRegion_bodyContainer)
          have htargetChildExact := outputLeaf.wiresExact.extend_child
            (layout.plugRaw_wellFormed signature input hadmissible)
            htargetParent
          cases hsourceChild : ConcreteElaboration.compileRegion? signature
              input.pattern.val.diagram patternLeaf.fuel child
              (patternLeaf.inheritedWires.extend
                input.binderSpine.bodyContainer)
              (patternLeaf.binders.push child arity) with
          | none =>
              simp [ConcreteElaboration.compileOccurrenceWith?, hchild] at hsource
              let wrap := fun body : Region signature
                  (patternLeaf.inheritedWires.extend
                    input.binderSpine.bodyContainer).length
                  (arity :: patternWitness.toFocus.holeRels) =>
                some (Item.bubble arity body)
              have hbound := congrArg (fun result => result.bind wrap)
                hsourceChild
              have himpossible : (none : Option (Item signature
                  (patternLeaf.inheritedWires.extend
                    input.binderSpine.bodyContainer).length
                  patternWitness.toFocus.holeRels)) = some sourceItem := by
                exact (by simpa only [wrap, Option.bind_none] using
                  hbound.symm.trans hsource)
              contradiction
          | some compiledSource =>
              simp [ConcreteElaboration.compileOccurrenceWith?, hchild] at hsource
              let wrap := fun body : Region signature
                  (patternLeaf.inheritedWires.extend
                    input.binderSpine.bodyContainer).length
                  (arity :: patternWitness.toFocus.holeRels) =>
                some (Item.bubble arity body)
              have hbound := congrArg (fun result => result.bind wrap)
                hsourceChild
              have hbubbleEq : Item.bubble arity compiledSource =
                  sourceItem := by
                exact Option.some.inj (by
                  simpa only [wrap, Option.bind_some] using
                    hbound.symm.trans hsource)
              have hsourceEq : sourceItem =
                  Item.bubble arity compiledSource := hbubbleEq.symm
              subst sourceItem
              cases htargetChildResult : ConcreteElaboration.compileRegion?
                  signature layout.plugRaw outputLeaf.fuel
                  (layout.bodyRegion child)
                  (outputLeaf.inheritedWires.extend
                    (layout.frameRegion input.site))
                  (outputLeaf.binders.push (layout.bodyRegion child) arity) with
              | none =>
                  simp [mapPatternOccurrence,
                    ConcreteElaboration.compileOccurrenceWith?, htargetChild,
                    htargetChildResult] at htarget
              | some compiledTarget =>
                  simp [mapPatternOccurrence,
                    ConcreteElaboration.compileOccurrenceWith?, htargetChild,
                    htargetChildResult] at htarget
                  have htargetEq : targetItem =
                      Item.bubble arity compiledTarget := htarget.symm
                  subst targetItem
                  have hrecursive := layout.compilePatternRegion_at_material
                    signature input hadmissible patternLeaf.fuel
                    outputLeaf.fuel child hmaterial
                    (patternLeaf.inheritedWires.extend
                      input.binderSpine.bodyContainer)
                    (outputLeaf.inheritedWires.extend
                      (layout.frameRegion input.site))
                    hsourceChildExact htargetChildExact
                    (patternLeaf.binders.push child arity)
                    (outputLeaf.binders.push (layout.bodyRegion child) arity)
                    (ConcreteElaboration.BinderContext.push_covers_bubble_child
                      patternLeaf.bindersCover hchild)
                    (ConcreteElaboration.BinderContext.push_covers_bubble_child
                      outputLeaf.bindersCover htargetChildAtSite)
                    (patternLeaf.binderEnumeration.bubbleChild
                      input.pattern.property.diagram_well_formed hchild)
                    (layout.patternSiteWireIndexMap hadmissible patternWitness
                      patternLeaf outputWitness outputLeaf)
                    (layout.patternSiteWireIndexMap_spec hadmissible
                      patternWitness patternLeaf outputWitness outputLeaf)
                    (RelationRenaming.lift
                      (layout.patternRelationRenaming hadmissible patternWitness
                        patternLeaf outputWitness outputLeaf) arity)
                    (layout.terminalRelationLookup_bubbleChild
                      input.binderSpine.bodyContainer child hmaterial
                      patternLeaf.binders outputLeaf.binders
                      patternLeaf.binderEnumeration arity hchild
                      (layout.patternRelationRenaming hadmissible patternWitness
                        patternLeaf outputWitness outputLeaf)
                      (layout.patternRelationRenaming_lookup hadmissible
                        patternWitness patternLeaf outputWitness outputLeaf))
                    compiledSource compiledTarget hsourceChild
                    htargetChildResult
                  have htransport := seamRecursiveRegionIso_of_maps combined
                    targetEq
                    (layout.patternSeamPreparedWireOfNonempty hadmissible host
                      patternWitness patternLeaf hnonempty)
                    (layout.patternSiteWireIndexMap hadmissible patternWitness
                      patternLeaf outputWitness outputLeaf)
                    hwire
                    (RelationRenaming.lift
                      (layout.patternRelationRenaming hadmissible patternWitness
                        patternLeaf outputWitness outputLeaf) arity)
                    compiledSource compiledTarget hrecursive
                  simpa [hrelations, Item.renameWires, Item.renameRelations] using
                    ItemIso.bubble htransport

/-- Direct empty-proxy pattern transport into the actual focused compiler
context.  This theorem needs no coalesced-host compiler view: root nodes use
the canonical open-root wire map, while proper children reuse the actual
compile equations supplied by the output leaf. -/
theorem compilePatternRootOccurrence_at_site_iso
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hzero : input.binderSpine.proxyCount = 0)
    (occurrence : ConcreteElaboration.LocalOccurrence
      input.pattern.val.diagram.regionCount
      input.pattern.val.diagram.nodeCount)
    (hoccurrence : occurrence ∈ ConcreteElaboration.localOccurrences
      input.pattern.val.diagram input.pattern.val.diagram.root)
    (sourceItem : Item signature
      (input.pattern.val.exposedWires ++
        input.pattern.val.hiddenWires).length [])
    (targetItem : Item signature
      (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).length
      outputWitness.toFocus.holeRels)
    (hsource : ConcreteElaboration.compileOccurrenceWith? signature
      input.pattern.val.diagram
      (ConcreteElaboration.compileRegion? signature input.pattern.val.diagram
        input.pattern.val.diagram.regionCount)
      (input.pattern.val.exposedWires ++ input.pattern.val.hiddenWires)
      ConcreteElaboration.BinderContext.empty occurrence = some sourceItem)
    (htarget : ConcreteElaboration.compileOccurrenceWith? signature
      layout.plugRaw
      (ConcreteElaboration.compileRegion? signature layout.plugRaw
        outputLeaf.fuel)
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      outputLeaf.binders (layout.mapPatternOccurrence occurrence) =
        some targetItem) :
    ItemIso signature
      (FiniteEquiv.refl (Fin
        (outputLeaf.inheritedWires.extend
          (layout.frameRegion input.site)).length))
      outputWitness.toFocus.holeRels
      ((sourceItem.renameWires
        (layout.patternRootWireIndexMap hadmissible hzero outputWitness
          outputLeaf))
          |>.renameRelations
            (emptyRelationRenaming outputWitness.toFocus.holeRels))
      targetItem := by
  let sourceExact := openRootWires_exact input.pattern
  let sourceCover := ConcreteElaboration.BinderContext.empty_covers_root
    input.pattern.property.diagram_well_formed
  let sourceEnumeration := ConcreteElaboration.BinderContext.Enumeration.empty
    input.pattern.val.diagram
  have hbody := input.binderSpine.body_eq_root_of_empty hzero
  cases occurrence with
  | node node =>
      have hnodeRegion :=
        (ConcreteElaboration.mem_localOccurrences_node _ _ _).1 hoccurrence
      have htransport := layout.compilePatternRootNode_at_site signature input
        hadmissible hzero outputWitness outputLeaf node hnodeRegion
      rw [show layout.mapPatternOccurrence
          (ConcreteElaboration.LocalOccurrence.node node) =
            ConcreteElaboration.LocalOccurrence.node
              (layout.patternNode node) by rfl] at htarget
      simp only [ConcreteElaboration.compileOccurrenceWith?] at hsource htarget
      rw [htarget] at htransport
      let transform := fun item : Item signature
          (input.pattern.val.exposedWires ++
            input.pattern.val.hiddenWires).length [] =>
        (item.renameWires
          (layout.patternRootWireIndexMap hadmissible hzero outputWitness
            outputLeaf)).renameRelations
          (emptyRelationRenaming outputWitness.toFocus.holeRels)
      have hmapped : Option.map transform
            (ConcreteElaboration.compileNode? signature
              input.pattern.val.diagram
              (input.pattern.val.exposedWires ++
                input.pattern.val.hiddenWires)
              ConcreteElaboration.BinderContext.empty node) =
          some (transform sourceItem) := by
        exact (congrArg (Option.map transform) hsource).trans rfl
      have htransport' : targetItem = transform sourceItem :=
        Option.some.inj (htransport.trans hmapped)
      subst targetItem
      have href := ItemIso.renameWiresEquiv (transform sourceItem)
        (FiniteEquiv.refl (Fin
          (outputLeaf.inheritedWires.extend
            (layout.frameRegion input.site)).length))
      have hfun :
          (FiniteEquiv.refl (Fin
            (outputLeaf.inheritedWires.extend
              (layout.frameRegion input.site)).length)).toFun = id := rfl
      rw [hfun, Item.renameWires_id] at href
      simpa only [transform] using href
  | child child =>
      have hparentRoot :=
        (ConcreteElaboration.mem_localOccurrences_child _ _ _).1 hoccurrence
      have hparent : (input.pattern.val.diagram.regions child).parent? =
          some input.binderSpine.bodyContainer := by
        simpa [hbody] using hparentRoot
      have hmaterial := directChildOfBody_material input child hparent
      cases hchild : input.pattern.val.diagram.regions child with
      | sheet =>
          simp [ConcreteElaboration.compileOccurrenceWith?, hchild] at hsource
      | cut parent =>
          have hparentEq : parent = input.pattern.val.diagram.root := by
            simpa [hchild, CRegion.parent?] using hparentRoot
          subst parent
          have hchildBody : input.pattern.val.diagram.regions child =
              CRegion.cut input.binderSpine.bodyContainer := by
            simpa [hbody] using hchild
          have htargetChild := layout.plugRaw_bodyRegion_cut child
            input.binderSpine.bodyContainer hmaterial hchildBody
          have htargetChildAtSite : layout.plugRaw.regions
              (layout.bodyRegion child) =
                CRegion.cut (layout.frameRegion input.site) := by
            simpa only [layout.bodyRegion_bodyContainer] using htargetChild
          have hsourceChildExact := sourceExact.extend_child
            input.pattern.property.diagram_well_formed hparentRoot
          have htargetParent :=
            (layout.bodyRegion_parent_exact child
              input.binderSpine.bodyContainer hmaterial hparent).trans
              (congrArg some layout.bodyRegion_bodyContainer)
          have htargetChildExact := outputLeaf.wiresExact.extend_child
            (layout.plugRaw_wellFormed signature input hadmissible)
            htargetParent
          cases hsourceChild : ConcreteElaboration.compileRegion? signature
              input.pattern.val.diagram input.pattern.val.diagram.regionCount
              child
              (input.pattern.val.exposedWires ++
                input.pattern.val.hiddenWires)
              ConcreteElaboration.BinderContext.empty with
          | none =>
              simp [ConcreteElaboration.compileOccurrenceWith?, hchild,
                hsourceChild] at hsource
          | some compiledSource =>
              simp [ConcreteElaboration.compileOccurrenceWith?, hchild,
                hsourceChild] at hsource
              have hsourceEq : sourceItem = Item.cut compiledSource :=
                hsource.symm
              subst sourceItem
              cases htargetChildResult : ConcreteElaboration.compileRegion?
                  signature layout.plugRaw outputLeaf.fuel
                  (layout.bodyRegion child)
                  (outputLeaf.inheritedWires.extend
                    (layout.frameRegion input.site)) outputLeaf.binders with
              | none =>
                  simp [mapPatternOccurrence,
                    ConcreteElaboration.compileOccurrenceWith?, htargetChild,
                    htargetChildResult] at htarget
              | some compiledTarget =>
                  simp [mapPatternOccurrence,
                    ConcreteElaboration.compileOccurrenceWith?, htargetChild,
                    htargetChildResult] at htarget
                  have htargetEq : targetItem = Item.cut compiledTarget :=
                    htarget.symm
                  subst targetItem
                  have hrecursive := layout.compilePatternRegion_at_material
                    signature input hadmissible
                    input.pattern.val.diagram.regionCount outputLeaf.fuel child
                    hmaterial
                    (input.pattern.val.exposedWires ++
                      input.pattern.val.hiddenWires)
                    (outputLeaf.inheritedWires.extend
                      (layout.frameRegion input.site))
                    hsourceChildExact htargetChildExact
                    ConcreteElaboration.BinderContext.empty outputLeaf.binders
                    (ConcreteElaboration.BinderContext.covers_cut_child
                      sourceCover hchild)
                    (ConcreteElaboration.BinderContext.covers_cut_child
                      outputLeaf.bindersCover htargetChildAtSite)
                    (sourceEnumeration.cutChild
                      input.pattern.property.diagram_well_formed hchild)
                    (layout.patternRootWireIndexMap hadmissible hzero
                      outputWitness outputLeaf)
                    (layout.patternRootWireIndexMap_spec hadmissible hzero
                      outputWitness outputLeaf)
                    (emptyRelationRenaming outputWitness.toFocus.holeRels)
                    (layout.materialRelationLookup_cutChild
                      input.pattern.val.diagram.root child
                      ConcreteElaboration.BinderContext.empty outputLeaf.binders
                      sourceEnumeration hchild
                      (emptyRelationRenaming outputWitness.toFocus.holeRels)
                      nofun)
                    compiledSource compiledTarget hsourceChild
                    htargetChildResult
                  simpa [Item.renameWires, Item.renameRelations] using
                    ItemIso.cut hrecursive
      | bubble parent arity =>
          have hparentEq : parent = input.pattern.val.diagram.root := by
            simpa [hchild, CRegion.parent?] using hparentRoot
          subst parent
          have hchildBody : input.pattern.val.diagram.regions child =
              CRegion.bubble input.binderSpine.bodyContainer arity := by
            simpa [hbody] using hchild
          have htargetChild := layout.plugRaw_bodyRegion_bubble child
            input.binderSpine.bodyContainer arity hmaterial hchildBody
          have htargetChildAtSite : layout.plugRaw.regions
              (layout.bodyRegion child) =
                CRegion.bubble (layout.frameRegion input.site) arity := by
            simpa only [layout.bodyRegion_bodyContainer] using htargetChild
          have hsourceChildExact := sourceExact.extend_child
            input.pattern.property.diagram_well_formed (by
              simpa [hbody] using hparent)
          have htargetParent :=
            (layout.bodyRegion_parent_exact child
              input.binderSpine.bodyContainer hmaterial hparent).trans
              (congrArg some layout.bodyRegion_bodyContainer)
          have htargetChildExact := outputLeaf.wiresExact.extend_child
            (layout.plugRaw_wellFormed signature input hadmissible)
            htargetParent
          cases hsourceChild : ConcreteElaboration.compileRegion? signature
              input.pattern.val.diagram input.pattern.val.diagram.regionCount
              child
              (input.pattern.val.exposedWires ++
                input.pattern.val.hiddenWires)
              (ConcreteElaboration.BinderContext.empty.push child arity) with
          | none =>
              simp [ConcreteElaboration.compileOccurrenceWith?, hchild] at hsource
              let wrap := fun body : Region signature
                  (input.pattern.val.exposedWires ++
                    input.pattern.val.hiddenWires).length [arity] =>
                some (Item.bubble arity body)
              have hbound := congrArg (fun result => result.bind wrap)
                hsourceChild
              have himpossible : (none : Option (Item signature
                  (input.pattern.val.exposedWires ++
                    input.pattern.val.hiddenWires).length [])) =
                  some sourceItem := by
                exact (by simpa only [wrap, Option.bind_none] using
                  hbound.symm.trans hsource)
              contradiction
          | some compiledSource =>
              simp [ConcreteElaboration.compileOccurrenceWith?, hchild] at hsource
              let wrap := fun body : Region signature
                  (input.pattern.val.exposedWires ++
                    input.pattern.val.hiddenWires).length [arity] =>
                some (Item.bubble arity body)
              have hbound := congrArg (fun result => result.bind wrap)
                hsourceChild
              have hbubbleEq : Item.bubble arity compiledSource =
                  sourceItem := by
                exact Option.some.inj (by
                  simpa only [wrap, Option.bind_some] using
                    hbound.symm.trans hsource)
              have hsourceEq : sourceItem =
                  Item.bubble arity compiledSource := hbubbleEq.symm
              subst sourceItem
              cases htargetChildResult : ConcreteElaboration.compileRegion?
                  signature layout.plugRaw outputLeaf.fuel
                  (layout.bodyRegion child)
                  (outputLeaf.inheritedWires.extend
                    (layout.frameRegion input.site))
                  (outputLeaf.binders.push
                    (layout.bodyRegion child) arity) with
              | none =>
                  simp [mapPatternOccurrence,
                    ConcreteElaboration.compileOccurrenceWith?, htargetChild,
                    htargetChildResult] at htarget
              | some compiledTarget =>
                  simp [mapPatternOccurrence,
                    ConcreteElaboration.compileOccurrenceWith?, htargetChild,
                    htargetChildResult] at htarget
                  have htargetEq : targetItem =
                      Item.bubble arity compiledTarget := htarget.symm
                  subst targetItem
                  have hrecursive := layout.compilePatternRegion_at_material
                    signature input hadmissible
                    input.pattern.val.diagram.regionCount outputLeaf.fuel child
                    hmaterial
                    (input.pattern.val.exposedWires ++
                      input.pattern.val.hiddenWires)
                    (outputLeaf.inheritedWires.extend
                      (layout.frameRegion input.site))
                    hsourceChildExact htargetChildExact
                    (ConcreteElaboration.BinderContext.empty.push child arity)
                    (outputLeaf.binders.push
                      (layout.bodyRegion child) arity)
                    (ConcreteElaboration.BinderContext.push_covers_bubble_child
                      sourceCover hchild)
                    (ConcreteElaboration.BinderContext.push_covers_bubble_child
                      outputLeaf.bindersCover htargetChildAtSite)
                    (sourceEnumeration.bubbleChild
                      input.pattern.property.diagram_well_formed hchild)
                    (layout.patternRootWireIndexMap hadmissible hzero
                      outputWitness outputLeaf)
                    (layout.patternRootWireIndexMap_spec hadmissible hzero
                      outputWitness outputLeaf)
                    (RelationRenaming.lift
                      (emptyRelationRenaming
                        outputWitness.toFocus.holeRels) arity)
                    (layout.terminalRelationLookup_bubbleChild
                      input.pattern.val.diagram.root child hmaterial
                      ConcreteElaboration.BinderContext.empty
                      outputLeaf.binders sourceEnumeration arity hchild
                      (emptyRelationRenaming outputWitness.toFocus.holeRels)
                      nofun)
                    compiledSource compiledTarget hsourceChild
                    htargetChildResult
                  simpa [Item.renameWires, Item.renameRelations] using
                    ItemIso.bubble hrecursive

/-- Empty-proxy counterpart of `compilePatternOccurrence_at_seam_iso`.
The pattern sheet root is compiled with its open root wire context and empty
lexical relation context; every proper direct child is material. -/
theorem compilePatternRootOccurrence_at_seam_iso
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hzero : input.binderSpine.proxyCount = 0)
    (occurrence : ConcreteElaboration.LocalOccurrence
      input.pattern.val.diagram.regionCount
      input.pattern.val.diagram.nodeCount)
    (hoccurrence : occurrence ∈ ConcreteElaboration.localOccurrences
      input.pattern.val.diagram input.pattern.val.diagram.root)
    (sourceItem : Item signature
      (input.pattern.val.exposedWires ++
        input.pattern.val.hiddenWires).length [])
    (targetItem : Item signature
      (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).length
      outputWitness.toFocus.holeRels)
    (hsource : ConcreteElaboration.compileOccurrenceWith? signature
      input.pattern.val.diagram
      (ConcreteElaboration.compileRegion? signature input.pattern.val.diagram
        input.pattern.val.diagram.regionCount)
      (input.pattern.val.exposedWires ++ input.pattern.val.hiddenWires)
      ConcreteElaboration.BinderContext.empty occurrence = some sourceItem)
    (htarget : ConcreteElaboration.compileOccurrenceWith? signature
      layout.plugRaw
      (ConcreteElaboration.compileRegion? signature layout.plugRaw
        outputLeaf.fuel)
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      outputLeaf.binders (layout.mapPatternOccurrence occurrence) =
        some targetItem) :
    ItemIso signature
      (layout.siteCombinedWireEquivOfEmpty hadmissible host
        (outputWitness := outputWitness) (outputLeaf := outputLeaf) hzero)
      outputWitness.toFocus.holeRels
      ((sourceItem.renameWires
        (layout.patternRootSeamPreparedWireOfEmpty hadmissible host))
          |>.renameRelations
            (emptyRelationRenaming outputWitness.toFocus.holeRels))
      (targetItem.castWiresEq
        (ConcreteElaboration.WireContext.length_extend
          outputLeaf.inheritedWires (layout.frameRegion input.site))) := by
  let combined := layout.siteCombinedWireEquivOfEmpty hadmissible host
    outputWitness outputLeaf hzero
  let targetEq := ConcreteElaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  let toTargetContext := combined.trans (FiniteEquiv.finCast targetEq.symm)
  have hwire : toTargetContext.toFun ∘
        layout.patternRootSeamPreparedWireOfEmpty hadmissible host =
      layout.patternRootWireIndexMap hadmissible hzero outputWitness
        outputLeaf := by
    simpa only [toTargetContext, combined, FiniteEquiv.trans_apply,
      FiniteEquiv.finCast, Function.comp_def] using
      layout.patternRootSeamWireMapOfEmpty_eq hadmissible host outputWitness
        outputLeaf hzero
  have hdirect := layout.compilePatternRootOccurrence_at_site_iso signature input
    hadmissible outputWitness outputLeaf hzero occurrence hoccurrence sourceItem
    targetItem hsource htarget
  let sourcePrepared :=
    (sourceItem.renameWires
      (layout.patternRootSeamPreparedWireOfEmpty hadmissible host))
        |>.renameRelations
          (emptyRelationRenaming outputWitness.toFocus.holeRels)
  have hfirstRaw := ItemIso.renameWiresEquiv sourcePrepared toTargetContext
  have hfirst : ItemIso signature toTargetContext
      outputWitness.toFocus.holeRels sourcePrepared
      ((sourceItem.renameWires
        (layout.patternRootWireIndexMap hadmissible hzero outputWitness
          outputLeaf)).renameRelations
        (emptyRelationRenaming outputWitness.toFocus.holeRels)) := by
    simpa only [sourcePrepared, Item.renameWires_renameRelations,
      Item.renameWires_comp, hwire] using hfirstRaw
  have hlastRaw := ItemIso.renameWiresEquiv targetItem
    (FiniteEquiv.finCast targetEq)
  have hlast : ItemIso signature (FiniteEquiv.finCast targetEq)
      outputWitness.toFocus.holeRels targetItem
      (targetItem.castWiresEq targetEq) := by
    simpa only [Item.castWiresEq_eq_renameWires,
      FiniteEquiv.finCast] using hlastRaw
  have hcombined := (hfirst.trans hdirect).trans hlast
  have hequiv :
      (toTargetContext.trans
        (FiniteEquiv.refl
          (Fin (outputLeaf.inheritedWires.extend
            (layout.frameRegion input.site)).length))).trans
          (FiniteEquiv.finCast targetEq) = combined := by
    apply FiniteEquiv.ext
    intro index
    apply Fin.ext
    rfl
  rw [hequiv] at hcombined
  exact hcombined

theorem compiledSiteItemsIsoOfNonempty
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Region.ContextPath.CompilerLeaf input.pattern.val.diagram
      input.binderSpine.bodyContainer patternWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0) :
    let hostPrepared :=
      (host.compilerLeaf.items.renameWires
        (layout.hostSeamPreparedWireOfNonempty hadmissible host)).renameRelations
        (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf)
    let patternPrepared :=
      (patternLeaf.items.renameWires
        (layout.patternSeamPreparedWireOfNonempty hadmissible host
          patternWitness patternLeaf hnonempty)).renameRelations
        (fun {arity} relation =>
          layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
            outputWitness outputLeaf
            (layout.coalescedTerminalRelationRenaming hadmissible
              host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
              hnonempty relation))
    ItemSeqIso signature
      (layout.siteCombinedWireEquivOfNonempty hadmissible host
        (outputWitness := outputWitness) (outputLeaf := outputLeaf) hnonempty)
      outputWitness.toFocus.holeRels
      (hostPrepared.append patternPrepared)
      (outputLeaf.items.castWiresEq
        (ConcreteElaboration.WireContext.length_extend
          outputLeaf.inheritedWires (layout.frameRegion input.site))) := by
  let hostPrepared :=
    (host.compilerLeaf.items.renameWires
      (layout.hostSeamPreparedWireOfNonempty hadmissible host)).renameRelations
      (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf)
  let patternPrepared :=
    (patternLeaf.items.renameWires
      (layout.patternSeamPreparedWireOfNonempty hadmissible host
        patternWitness patternLeaf hnonempty)).renameRelations
      (fun {arity} relation =>
        layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf
          (layout.coalescedTerminalRelationRenaming hadmissible
            host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
            hnonempty relation))
  let sourcePrepared := hostPrepared.append patternPrepared
  let targetEq := ConcreteElaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  let targetPrepared := outputLeaf.items.castWiresEq targetEq
  have hhostLength := ConcreteElaboration.compileOccurrencesWith?_length
    (ConcreteElaboration.compileRegion? signature input.coalesceFrameRaw
      host.compilerLeaf.fuel)
    (host.compilerLeaf.inheritedWires.extend input.site)
    host.compilerLeaf.binders host.compilerLeaf.itemsComputation
  have hpatternLength := ConcreteElaboration.compileOccurrencesWith?_length
    (ConcreteElaboration.compileRegion? signature input.pattern.val.diagram
      patternLeaf.fuel)
    (patternLeaf.inheritedWires.extend input.binderSpine.bodyContainer)
    patternLeaf.binders patternLeaf.itemsComputation
  have htargetLength := ConcreteElaboration.compileOccurrencesWith?_length
    (ConcreteElaboration.compileRegion? signature layout.plugRaw
      outputLeaf.fuel)
    (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
    outputLeaf.binders outputLeaf.itemsComputation
  have hhostRawLength : host.compilerLeaf.items.length =
      (ConcreteElaboration.localOccurrences input.coalesceFrameRaw
        input.site).length := by
    simpa [coalesceFrame] using hhostLength
  have hsourcePreparedLength : sourcePrepared.length =
      layout.semanticSiteOccurrences.length := by
    simp [sourcePrepared, hostPrepared, patternPrepared,
      semanticSiteOccurrences, hhostRawLength, hpatternLength,
      ItemSeq.length_append]
  have htargetPreparedLength : targetPrepared.length =
      (ConcreteElaboration.localOccurrences layout.plugRaw
        (layout.frameRegion input.site)).length := by
    simp [targetPrepared, htargetLength]
  let positions :=
    (FiniteEquiv.finCast hsourcePreparedLength).trans
      (layout.siteOccurrenceEquiv.trans
        (FiniteEquiv.finCast htargetPreparedLength.symm))
  apply ItemSeqIso.permute positions
  intro sourceIndex
  let splitIndex := Fin.cast
    (ItemSeq.length_append hostPrepared patternPrepared)
    sourceIndex
  have hsourceFromSplit :
      Fin.cast (ItemSeq.length_append hostPrepared patternPrepared).symm
          splitIndex = sourceIndex := by
    apply Fin.ext
    rfl
  revert hsourceFromSplit
  refine Fin.addCases (m := hostPrepared.length) (n := patternPrepared.length)
    (fun hostPreparedIndex hsourcePosition => ?_)
    (fun patternPreparedIndex hsourcePosition => ?_) splitIndex
  · let hostOriginalIndex : Fin host.compilerLeaf.items.length :=
      Fin.cast (by simp [hostPrepared]) hostPreparedIndex
    let hostOccurrenceIndex := Fin.cast hhostRawLength hostOriginalIndex
    let occurrenceIndex : Fin layout.semanticSiteOccurrences.length :=
      Fin.cast (by simp [semanticSiteOccurrences])
        (Fin.castAdd
          (ConcreteElaboration.localOccurrences input.pattern.val.diagram
            input.binderSpine.bodyContainer).length hostOccurrenceIndex)
    let targetOccurrenceIndex := layout.siteOccurrenceEquiv occurrenceIndex
    let targetOriginalIndex := Fin.cast htargetLength.symm
      targetOccurrenceIndex
    have hsourceGet := ConcreteElaboration.compileOccurrencesWith?_get
      (ConcreteElaboration.compileRegion? signature input.coalesceFrameRaw
        host.compilerLeaf.fuel)
      (host.compilerLeaf.inheritedWires.extend input.site)
      host.compilerLeaf.binders host.compilerLeaf.itemsComputation
      hostOccurrenceIndex
    have htargetGet := ConcreteElaboration.compileOccurrencesWith?_get
      (ConcreteElaboration.compileRegion? signature layout.plugRaw
        outputLeaf.fuel)
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      outputLeaf.binders outputLeaf.itemsComputation targetOccurrenceIndex
    rw [layout.siteOccurrenceEquiv_spec occurrenceIndex] at htargetGet
    have htargetGet' : ConcreteElaboration.compileOccurrenceWith? signature
        layout.plugRaw
        (ConcreteElaboration.compileRegion? signature layout.plugRaw
          outputLeaf.fuel)
        (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
        outputLeaf.binders
        (layout.mapFrameOccurrence
          ((ConcreteElaboration.localOccurrences input.coalesceFrameRaw
            input.site).get hostOccurrenceIndex)) =
          some (outputLeaf.items.get targetOriginalIndex) := by
      simpa [semanticSiteOccurrences, occurrenceIndex] using htargetGet
    have hitem := layout.compileHostOccurrence_at_seam_iso signature input
      hadmissible host outputWitness outputLeaf hnonempty
      ((ConcreteElaboration.localOccurrences input.coalesceFrameRaw
        input.site).get hostOccurrenceIndex)
      (List.get_mem _ hostOccurrenceIndex)
      (host.compilerLeaf.items.get hostOriginalIndex)
      (outputLeaf.items.get targetOriginalIndex) hsourceGet htargetGet'
    have hsourcePosition' :
        Fin.cast (ItemSeq.length_append hostPrepared patternPrepared).symm
          (Fin.castAdd patternPrepared.length hostPreparedIndex) =
            sourceIndex := by
      rw [← hsourcePosition]
    have hsemanticPosition :
        Fin.cast hsourcePreparedLength sourceIndex = occurrenceIndex := by
      rw [← hsourcePosition']
      apply Fin.ext
      rfl
    have htargetPosition :
        Fin.cast (ItemSeq.castWiresEq_length targetEq outputLeaf.items).symm
          targetOriginalIndex = positions sourceIndex := by
      simp only [positions, FiniteEquiv.trans_apply,
        FiniteEquiv.finCast]
      rw [hsemanticPosition]
      apply Fin.ext
      rfl
    have hpreparedGet : hostPrepared.get hostPreparedIndex =
        Item.renameRelations
          (layout.hostRelationRenaming host.intrinsicPath
            host.compilerLeaf outputWitness outputLeaf)
          (Item.renameWires
            (layout.hostSeamPreparedWireOfNonempty hadmissible host)
            (host.compilerLeaf.items.get hostOriginalIndex)) := by
      have hwire := ItemSeq.get_renameWires host.compilerLeaf.items
        (layout.hostSeamPreparedWireOfNonempty hadmissible host)
        hostOriginalIndex
      have hrelation := ItemSeq.get_renameRelations
        (host.compilerLeaf.items.renameWires
          (layout.hostSeamPreparedWireOfNonempty hadmissible host))
        (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf)
        (host.compilerLeaf.items.renameWiresPositionEquiv
          (layout.hostSeamPreparedWireOfNonempty hadmissible host)
          hostOriginalIndex)
      rw [hwire] at hrelation
      have hindex :
          Fin.cast
              (ItemSeq.renameRelations_length
                (host.compilerLeaf.items.renameWires
                  (layout.hostSeamPreparedWireOfNonempty hadmissible host))
                (layout.hostRelationRenaming host.intrinsicPath
                  host.compilerLeaf outputWitness outputLeaf)).symm
              (host.compilerLeaf.items.renameWiresPositionEquiv
                (layout.hostSeamPreparedWireOfNonempty hadmissible host)
                hostOriginalIndex) = hostPreparedIndex := by
        apply Fin.ext
        rfl
      simpa only [hostPrepared, hindex] using hrelation
    rw [← htargetPosition, ← hsourcePosition',
      ItemSeq.get_append_left]
    rw [hpreparedGet]
    simpa only [targetPrepared, ItemSeq.get_castWiresEq] using hitem
  · let patternOriginalIndex : Fin patternLeaf.items.length :=
      Fin.cast (by simp [patternPrepared]) patternPreparedIndex
    let patternOccurrenceIndex := Fin.cast hpatternLength patternOriginalIndex
    let occurrenceIndex : Fin layout.semanticSiteOccurrences.length :=
      Fin.cast (by simp [semanticSiteOccurrences])
        (Fin.natAdd
          (ConcreteElaboration.localOccurrences input.coalesceFrameRaw
            input.site).length patternOccurrenceIndex)
    let targetOccurrenceIndex := layout.siteOccurrenceEquiv occurrenceIndex
    let targetOriginalIndex := Fin.cast htargetLength.symm
      targetOccurrenceIndex
    have hsourceGet := ConcreteElaboration.compileOccurrencesWith?_get
      (ConcreteElaboration.compileRegion? signature input.pattern.val.diagram
        patternLeaf.fuel)
      (patternLeaf.inheritedWires.extend input.binderSpine.bodyContainer)
      patternLeaf.binders patternLeaf.itemsComputation patternOccurrenceIndex
    have htargetGet := ConcreteElaboration.compileOccurrencesWith?_get
      (ConcreteElaboration.compileRegion? signature layout.plugRaw
        outputLeaf.fuel)
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      outputLeaf.binders outputLeaf.itemsComputation targetOccurrenceIndex
    rw [layout.siteOccurrenceEquiv_spec occurrenceIndex] at htargetGet
    have htargetGet' : ConcreteElaboration.compileOccurrenceWith? signature
        layout.plugRaw
        (ConcreteElaboration.compileRegion? signature layout.plugRaw
          outputLeaf.fuel)
        (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
        outputLeaf.binders
        (layout.mapPatternOccurrence
          ((ConcreteElaboration.localOccurrences input.pattern.val.diagram
            input.binderSpine.bodyContainer).get patternOccurrenceIndex)) =
          some (outputLeaf.items.get targetOriginalIndex) := by
      simpa [semanticSiteOccurrences, occurrenceIndex] using htargetGet
    have hitem := layout.compilePatternOccurrence_at_seam_iso signature input
      hadmissible host patternWitness patternLeaf outputWitness outputLeaf
      hnonempty
      ((ConcreteElaboration.localOccurrences input.pattern.val.diagram
        input.binderSpine.bodyContainer).get patternOccurrenceIndex)
      (List.get_mem _ patternOccurrenceIndex)
      (patternLeaf.items.get patternOriginalIndex)
      (outputLeaf.items.get targetOriginalIndex) hsourceGet htargetGet'
    have hsourcePosition' :
        Fin.cast (ItemSeq.length_append hostPrepared patternPrepared).symm
          (Fin.natAdd hostPrepared.length patternPreparedIndex) =
            sourceIndex := by
      rw [← hsourcePosition]
    have hsemanticPosition :
        Fin.cast hsourcePreparedLength sourceIndex = occurrenceIndex := by
      rw [← hsourcePosition']
      apply Fin.ext
      simp [occurrenceIndex, patternOccurrenceIndex, patternOriginalIndex,
        hostPrepared, hhostRawLength]
    have htargetPosition :
        Fin.cast (ItemSeq.castWiresEq_length targetEq outputLeaf.items).symm
          targetOriginalIndex = positions sourceIndex := by
      simp only [positions, FiniteEquiv.trans_apply,
        FiniteEquiv.finCast]
      rw [hsemanticPosition]
      apply Fin.ext
      rfl
    have hpreparedGet : patternPrepared.get patternPreparedIndex =
        Item.renameRelations (fun {arity} relation =>
            layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
              outputWitness outputLeaf
              (layout.coalescedTerminalRelationRenaming hadmissible
                host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
                hnonempty relation))
          (Item.renameWires
            (layout.patternSeamPreparedWireOfNonempty hadmissible host
              patternWitness patternLeaf hnonempty)
            (patternLeaf.items.get patternOriginalIndex)) := by
      have hwire := ItemSeq.get_renameWires patternLeaf.items
        (layout.patternSeamPreparedWireOfNonempty hadmissible host
          patternWitness patternLeaf hnonempty) patternOriginalIndex
      have hrelation := ItemSeq.get_renameRelations
        (patternLeaf.items.renameWires
          (layout.patternSeamPreparedWireOfNonempty hadmissible host
            patternWitness patternLeaf hnonempty))
        (fun {arity} relation =>
          layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
            outputWitness outputLeaf
            (layout.coalescedTerminalRelationRenaming hadmissible
              host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
              hnonempty relation))
        (patternLeaf.items.renameWiresPositionEquiv
          (layout.patternSeamPreparedWireOfNonempty hadmissible host
            patternWitness patternLeaf hnonempty) patternOriginalIndex)
      rw [hwire] at hrelation
      have hindex :
          Fin.cast
              (ItemSeq.renameRelations_length
                (patternLeaf.items.renameWires
                  (layout.patternSeamPreparedWireOfNonempty hadmissible host
                    patternWitness patternLeaf hnonempty))
                (fun {arity} relation =>
                  layout.hostRelationRenaming host.intrinsicPath
                    host.compilerLeaf outputWitness outputLeaf
                    (layout.coalescedTerminalRelationRenaming hadmissible
                      host.intrinsicPath host.compilerLeaf patternWitness
                      patternLeaf hnonempty relation))).symm
              (patternLeaf.items.renameWiresPositionEquiv
                (layout.patternSeamPreparedWireOfNonempty hadmissible host
                  patternWitness patternLeaf hnonempty)
                patternOriginalIndex) = patternPreparedIndex := by
        apply Fin.ext
        rfl
      simpa only [patternPrepared, hindex] using hrelation
    rw [← htargetPosition, ← hsourcePosition',
      ItemSeq.get_append_right]
    rw [hpreparedGet]
    simpa only [targetPrepared, ItemSeq.get_castWiresEq] using hitem

/-- Empty-proxy item-sequence simulation.  The open pattern root contributes
its compiled root items after the host items, and `siteOccurrenceEquiv`
accounts for the concrete output ordering. -/
theorem compiledSiteItemsIsoOfEmpty
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hzero : input.binderSpine.proxyCount = 0)
    (patternItems : ItemSeq signature
      (input.pattern.val.exposedWires ++
        input.pattern.val.hiddenWires).length [])
    (patternItemsComputation :
      ConcreteElaboration.compileOccurrencesWith? signature
        input.pattern.val.diagram
        (ConcreteElaboration.compileRegion? signature
          input.pattern.val.diagram input.pattern.val.diagram.regionCount)
        (input.pattern.val.exposedWires ++ input.pattern.val.hiddenWires)
        ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences input.pattern.val.diagram
          input.pattern.val.diagram.root) = some patternItems) :
    let hostPrepared :=
      (host.compilerLeaf.items.renameWires
        (layout.hostSeamPreparedWireOfEmpty hadmissible host)).renameRelations
        (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf)
    let patternPrepared :=
      (patternItems.renameWires
        (layout.patternRootSeamPreparedWireOfEmpty hadmissible host))
          |>.renameRelations
            (emptyRelationRenaming outputWitness.toFocus.holeRels)
    ItemSeqIso signature
      (layout.siteCombinedWireEquivOfEmpty hadmissible host
        (outputWitness := outputWitness) (outputLeaf := outputLeaf) hzero)
      outputWitness.toFocus.holeRels
      (hostPrepared.append patternPrepared)
      (outputLeaf.items.castWiresEq
        (ConcreteElaboration.WireContext.length_extend
          outputLeaf.inheritedWires (layout.frameRegion input.site))) := by
  let hostPrepared :=
    (host.compilerLeaf.items.renameWires
      (layout.hostSeamPreparedWireOfEmpty hadmissible host)).renameRelations
      (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf)
  let patternPrepared :=
    (patternItems.renameWires
      (layout.patternRootSeamPreparedWireOfEmpty hadmissible host))
        |>.renameRelations
          (emptyRelationRenaming outputWitness.toFocus.holeRels)
  let sourcePrepared := hostPrepared.append patternPrepared
  let targetEq := ConcreteElaboration.WireContext.length_extend
    outputLeaf.inheritedWires (layout.frameRegion input.site)
  let targetPrepared := outputLeaf.items.castWiresEq targetEq
  have hbody := input.binderSpine.body_eq_root_of_empty hzero
  have hhostLength := ConcreteElaboration.compileOccurrencesWith?_length
    (ConcreteElaboration.compileRegion? signature input.coalesceFrameRaw
      host.compilerLeaf.fuel)
    (host.compilerLeaf.inheritedWires.extend input.site)
    host.compilerLeaf.binders host.compilerLeaf.itemsComputation
  have hpatternLength := ConcreteElaboration.compileOccurrencesWith?_length
    (ConcreteElaboration.compileRegion? signature input.pattern.val.diagram
      input.pattern.val.diagram.regionCount)
    (input.pattern.val.exposedWires ++ input.pattern.val.hiddenWires)
    ConcreteElaboration.BinderContext.empty patternItemsComputation
  have htargetLength := ConcreteElaboration.compileOccurrencesWith?_length
    (ConcreteElaboration.compileRegion? signature layout.plugRaw
      outputLeaf.fuel)
    (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
    outputLeaf.binders outputLeaf.itemsComputation
  have hhostRawLength : host.compilerLeaf.items.length =
      (ConcreteElaboration.localOccurrences input.coalesceFrameRaw
        input.site).length := by
    simpa [coalesceFrame] using hhostLength
  have hsourcePreparedLength : sourcePrepared.length =
      layout.semanticSiteOccurrences.length := by
    simp [sourcePrepared, hostPrepared, patternPrepared,
      semanticSiteOccurrences, hbody, hhostRawLength, hpatternLength,
      ItemSeq.length_append]
  have htargetPreparedLength : targetPrepared.length =
      (ConcreteElaboration.localOccurrences layout.plugRaw
        (layout.frameRegion input.site)).length := by
    simp [targetPrepared, htargetLength]
  let positions :=
    (FiniteEquiv.finCast hsourcePreparedLength).trans
      (layout.siteOccurrenceEquiv.trans
        (FiniteEquiv.finCast htargetPreparedLength.symm))
  apply ItemSeqIso.permute positions
  intro sourceIndex
  let splitIndex := Fin.cast
    (ItemSeq.length_append hostPrepared patternPrepared) sourceIndex
  have hsourceFromSplit :
      Fin.cast (ItemSeq.length_append hostPrepared patternPrepared).symm
          splitIndex = sourceIndex := by
    apply Fin.ext
    rfl
  revert hsourceFromSplit
  refine Fin.addCases (m := hostPrepared.length) (n := patternPrepared.length)
    (fun hostPreparedIndex hsourcePosition => ?_)
    (fun patternPreparedIndex hsourcePosition => ?_) splitIndex
  · let hostOriginalIndex : Fin host.compilerLeaf.items.length :=
      Fin.cast (by simp [hostPrepared]) hostPreparedIndex
    let hostOccurrenceIndex := Fin.cast hhostRawLength hostOriginalIndex
    let occurrenceIndex : Fin layout.semanticSiteOccurrences.length :=
      Fin.cast (by simp [semanticSiteOccurrences])
        (Fin.castAdd
          (ConcreteElaboration.localOccurrences input.pattern.val.diagram
            input.binderSpine.bodyContainer).length hostOccurrenceIndex)
    let targetOccurrenceIndex := layout.siteOccurrenceEquiv occurrenceIndex
    let targetOriginalIndex := Fin.cast htargetLength.symm
      targetOccurrenceIndex
    have hsourceGet := ConcreteElaboration.compileOccurrencesWith?_get
      (ConcreteElaboration.compileRegion? signature input.coalesceFrameRaw
        host.compilerLeaf.fuel)
      (host.compilerLeaf.inheritedWires.extend input.site)
      host.compilerLeaf.binders host.compilerLeaf.itemsComputation
      hostOccurrenceIndex
    have htargetGet := ConcreteElaboration.compileOccurrencesWith?_get
      (ConcreteElaboration.compileRegion? signature layout.plugRaw
        outputLeaf.fuel)
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      outputLeaf.binders outputLeaf.itemsComputation targetOccurrenceIndex
    rw [layout.siteOccurrenceEquiv_spec occurrenceIndex] at htargetGet
    have htargetGet' : ConcreteElaboration.compileOccurrenceWith? signature
        layout.plugRaw
        (ConcreteElaboration.compileRegion? signature layout.plugRaw
          outputLeaf.fuel)
        (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
        outputLeaf.binders
        (layout.mapFrameOccurrence
          ((ConcreteElaboration.localOccurrences input.coalesceFrameRaw
            input.site).get hostOccurrenceIndex)) =
          some (outputLeaf.items.get targetOriginalIndex) := by
      simpa [semanticSiteOccurrences, occurrenceIndex] using htargetGet
    have hitem := layout.compileHostOccurrence_at_seam_iso_of_empty signature
      input hadmissible host outputWitness outputLeaf hzero
      ((ConcreteElaboration.localOccurrences input.coalesceFrameRaw
        input.site).get hostOccurrenceIndex)
      (List.get_mem _ hostOccurrenceIndex)
      (host.compilerLeaf.items.get hostOriginalIndex)
      (outputLeaf.items.get targetOriginalIndex) hsourceGet htargetGet'
    have hsourcePosition' :
        Fin.cast (ItemSeq.length_append hostPrepared patternPrepared).symm
          (Fin.castAdd patternPrepared.length hostPreparedIndex) =
            sourceIndex := by
      rw [← hsourcePosition]
    have hsemanticPosition :
        Fin.cast hsourcePreparedLength sourceIndex = occurrenceIndex := by
      rw [← hsourcePosition']
      apply Fin.ext
      rfl
    have htargetPosition :
        Fin.cast (ItemSeq.castWiresEq_length targetEq outputLeaf.items).symm
          targetOriginalIndex = positions sourceIndex := by
      simp only [positions, FiniteEquiv.trans_apply, FiniteEquiv.finCast]
      rw [hsemanticPosition]
      apply Fin.ext
      rfl
    have hpreparedGet : hostPrepared.get hostPreparedIndex =
        Item.renameRelations
          (layout.hostRelationRenaming host.intrinsicPath
            host.compilerLeaf outputWitness outputLeaf)
          (Item.renameWires
            (layout.hostSeamPreparedWireOfEmpty hadmissible host)
            (host.compilerLeaf.items.get hostOriginalIndex)) := by
      have hwireGet := ItemSeq.get_renameWires host.compilerLeaf.items
        (layout.hostSeamPreparedWireOfEmpty hadmissible host)
        hostOriginalIndex
      have hrelationGet := ItemSeq.get_renameRelations
        (host.compilerLeaf.items.renameWires
          (layout.hostSeamPreparedWireOfEmpty hadmissible host))
        (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf)
        (host.compilerLeaf.items.renameWiresPositionEquiv
          (layout.hostSeamPreparedWireOfEmpty hadmissible host)
          hostOriginalIndex)
      rw [hwireGet] at hrelationGet
      have hindex :
          Fin.cast
              (ItemSeq.renameRelations_length
                (host.compilerLeaf.items.renameWires
                  (layout.hostSeamPreparedWireOfEmpty hadmissible host))
                (layout.hostRelationRenaming host.intrinsicPath
                  host.compilerLeaf outputWitness outputLeaf)).symm
              (host.compilerLeaf.items.renameWiresPositionEquiv
                (layout.hostSeamPreparedWireOfEmpty hadmissible host)
                hostOriginalIndex) = hostPreparedIndex := by
        apply Fin.ext
        rfl
      simpa only [hostPrepared, hindex] using hrelationGet
    rw [← htargetPosition, ← hsourcePosition', ItemSeq.get_append_left]
    rw [hpreparedGet]
    simpa only [targetPrepared, ItemSeq.get_castWiresEq] using hitem
  · let patternOriginalIndex : Fin patternItems.length :=
      Fin.cast (by simp [patternPrepared]) patternPreparedIndex
    let patternOccurrenceIndex := Fin.cast hpatternLength patternOriginalIndex
    have hpatternOccurrencesLength :
        (ConcreteElaboration.localOccurrences input.pattern.val.diagram
          input.pattern.val.diagram.root).length =
        (ConcreteElaboration.localOccurrences input.pattern.val.diagram
          input.binderSpine.bodyContainer).length := by
      rw [hbody]
    let patternOccurrenceAtBody :=
      Fin.cast hpatternOccurrencesLength patternOccurrenceIndex
    let occurrenceIndex : Fin layout.semanticSiteOccurrences.length :=
      Fin.cast (by simp [semanticSiteOccurrences])
        (Fin.natAdd
          (ConcreteElaboration.localOccurrences input.coalesceFrameRaw
            input.site).length
          patternOccurrenceAtBody)
    let targetOccurrenceIndex := layout.siteOccurrenceEquiv occurrenceIndex
    let targetOriginalIndex := Fin.cast htargetLength.symm
      targetOccurrenceIndex
    have hsourceGet := ConcreteElaboration.compileOccurrencesWith?_get
      (ConcreteElaboration.compileRegion? signature input.pattern.val.diagram
        input.pattern.val.diagram.regionCount)
      (input.pattern.val.exposedWires ++ input.pattern.val.hiddenWires)
      ConcreteElaboration.BinderContext.empty patternItemsComputation
      patternOccurrenceIndex
    have htargetGet := ConcreteElaboration.compileOccurrencesWith?_get
      (ConcreteElaboration.compileRegion? signature layout.plugRaw
        outputLeaf.fuel)
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      outputLeaf.binders outputLeaf.itemsComputation targetOccurrenceIndex
    rw [layout.siteOccurrenceEquiv_spec occurrenceIndex] at htargetGet
    have htargetGet' : ConcreteElaboration.compileOccurrenceWith? signature
        layout.plugRaw
        (ConcreteElaboration.compileRegion? signature layout.plugRaw
          outputLeaf.fuel)
        (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
        outputLeaf.binders
        (layout.mapPatternOccurrence
          ((ConcreteElaboration.localOccurrences input.pattern.val.diagram
            input.pattern.val.diagram.root).get patternOccurrenceIndex)) =
          some (outputLeaf.items.get targetOriginalIndex) := by
      simpa [semanticSiteOccurrences, occurrenceIndex, hbody] using htargetGet
    have hitem := layout.compilePatternRootOccurrence_at_seam_iso signature
      input hadmissible host outputWitness outputLeaf hzero
      ((ConcreteElaboration.localOccurrences input.pattern.val.diagram
        input.pattern.val.diagram.root).get patternOccurrenceIndex)
      (List.get_mem _ patternOccurrenceIndex)
      (patternItems.get patternOriginalIndex)
      (outputLeaf.items.get targetOriginalIndex) hsourceGet htargetGet'
    have hsourcePosition' :
        Fin.cast (ItemSeq.length_append hostPrepared patternPrepared).symm
          (Fin.natAdd hostPrepared.length patternPreparedIndex) =
            sourceIndex := by
      rw [← hsourcePosition]
    have hsemanticPosition :
        Fin.cast hsourcePreparedLength sourceIndex = occurrenceIndex := by
      rw [← hsourcePosition']
      apply Fin.ext
      simp [occurrenceIndex, patternOccurrenceAtBody,
        patternOccurrenceIndex, patternOriginalIndex, hostPrepared,
        hhostRawLength]
    have htargetPosition :
        Fin.cast (ItemSeq.castWiresEq_length targetEq outputLeaf.items).symm
          targetOriginalIndex = positions sourceIndex := by
      simp only [positions, FiniteEquiv.trans_apply, FiniteEquiv.finCast]
      rw [hsemanticPosition]
      apply Fin.ext
      rfl
    have hpreparedGet : patternPrepared.get patternPreparedIndex =
        Item.renameRelations
          (emptyRelationRenaming outputWitness.toFocus.holeRels)
          (Item.renameWires
            (layout.patternRootSeamPreparedWireOfEmpty hadmissible host)
            (patternItems.get patternOriginalIndex)) := by
      have hwireGet := ItemSeq.get_renameWires patternItems
        (layout.patternRootSeamPreparedWireOfEmpty hadmissible host)
        patternOriginalIndex
      have hrelationGet := ItemSeq.get_renameRelations
        (patternItems.renameWires
          (layout.patternRootSeamPreparedWireOfEmpty hadmissible host))
        (emptyRelationRenaming outputWitness.toFocus.holeRels)
        (patternItems.renameWiresPositionEquiv
          (layout.patternRootSeamPreparedWireOfEmpty hadmissible host)
          patternOriginalIndex)
      rw [hwireGet] at hrelationGet
      have hindex :
          Fin.cast
              (ItemSeq.renameRelations_length
                (patternItems.renameWires
                  (layout.patternRootSeamPreparedWireOfEmpty hadmissible host))
                (emptyRelationRenaming
                  outputWitness.toFocus.holeRels)).symm
              (patternItems.renameWiresPositionEquiv
                (layout.patternRootSeamPreparedWireOfEmpty hadmissible host)
                patternOriginalIndex) = patternPreparedIndex := by
        apply Fin.ext
        rfl
      simpa only [patternPrepared, hindex] using hrelationGet
    rw [← htargetPosition, ← hsourcePosition', ItemSeq.get_append_right]
    rw [hpreparedGet]
    simpa only [targetPrepared, ItemSeq.get_castWiresEq] using hitem

/-- The intrinsic capture-avoiding splice at a nonempty terminal body is
exactly the region compiled at the concrete output site, up to the canonical
inherited/local wire equivalences and executable occurrence order. -/
theorem compiledSiteRegionIsoOfNonempty
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Region.ContextPath.CompilerLeaf input.pattern.val.diagram
      input.binderSpine.bodyContainer patternWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0) :
    RegionIso signature
      (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf)
      outputWitness.toFocus.holeRels
      ((Region.spliceAt
          (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
            input.site).length
          (host.compilerLeaf.items.castWiresEq
            (ConcreteElaboration.WireContext.length_extend
              host.compilerLeaf.inheritedWires input.site))
          (ConcreteElaboration.finishRegion input.pattern.val.diagram
            patternLeaf.inheritedWires input.binderSpine.bodyContainer
            patternLeaf.items)
          (fun index => Fin.cast
            (ConcreteElaboration.WireContext.length_extend
              host.compilerLeaf.inheritedWires input.site)
            (layout.bodyTerminalWireRenaming hadmissible host patternWitness
              patternLeaf hnonempty index))
          (layout.coalescedTerminalRelationRenaming hadmissible
            host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
            hnonempty)).renameRelations
        (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf))
      (ConcreteElaboration.finishRegion layout.plugRaw
        outputLeaf.inheritedWires (layout.frameRegion input.site)
        outputLeaf.items) := by
  let hostPrepared :=
    (host.compilerLeaf.items.renameWires
      (layout.hostSeamPreparedWireOfNonempty hadmissible host)).renameRelations
      (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf)
  let patternPrepared :=
    (patternLeaf.items.renameWires
      (layout.patternSeamPreparedWireOfNonempty hadmissible host
        patternWitness patternLeaf hnonempty)).renameRelations
      (fun {arity} relation =>
        layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf
          (layout.coalescedTerminalRelationRenaming hadmissible
            host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
            hnonempty relation))
  have hitems := layout.compiledSiteItemsIsoOfNonempty signature input
    hadmissible host patternWitness patternLeaf outputWitness outputLeaf
    hnonempty
  have hregion := RegionIso.mk
    (layout.siteLocalWireEquivOfNonempty hnonempty) hitems
  have hpatternMap :
      Region.adjoinMaterialWire
          host.compilerLeaf.inheritedWires.length
          (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
            input.site).length
          (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
            input.binderSpine.bodyContainer).length ∘
        extendWireRenaming
          (fun index => Fin.cast
            (ConcreteElaboration.WireContext.length_extend
              host.compilerLeaf.inheritedWires input.site)
            (layout.bodyTerminalWireRenaming hadmissible host patternWitness
              patternLeaf hnonempty index))
          (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
            input.binderSpine.bodyContainer).length ∘
        Fin.cast
          (ConcreteElaboration.WireContext.length_extend
            patternLeaf.inheritedWires input.binderSpine.bodyContainer) =
      layout.patternSeamPreparedWireOfNonempty hadmissible host
        patternWitness patternLeaf hnonempty := by
    funext index
    let split := Fin.cast
      (ConcreteElaboration.WireContext.length_extend
        patternLeaf.inheritedWires input.binderSpine.bodyContainer) index
    have hrecover : Fin.cast
        (ConcreteElaboration.WireContext.length_extend
          patternLeaf.inheritedWires input.binderSpine.bodyContainer).symm
          split = index := by
      apply Fin.ext
      rfl
    rw [← hrecover]
    refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_) split
    · apply Fin.ext
      simp [patternSeamPreparedWireOfNonempty, Function.comp_apply,
        extendWireRenaming, Region.adjoinMaterialWire,
        Region.adjoinHostWire]
    · apply Fin.ext
      simp [patternSeamPreparedWireOfNonempty, Function.comp_apply,
        extendWireRenaming, Region.adjoinMaterialWire]
  have hsourceEq :
      ((Region.spliceAt
          (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
            input.site).length
          (host.compilerLeaf.items.castWiresEq
            (ConcreteElaboration.WireContext.length_extend
              host.compilerLeaf.inheritedWires input.site))
          (ConcreteElaboration.finishRegion input.pattern.val.diagram
            patternLeaf.inheritedWires input.binderSpine.bodyContainer
            patternLeaf.items)
          (fun index => Fin.cast
            (ConcreteElaboration.WireContext.length_extend
              host.compilerLeaf.inheritedWires input.site)
            (layout.bodyTerminalWireRenaming hadmissible host patternWitness
              patternLeaf hnonempty index))
          (layout.coalescedTerminalRelationRenaming hadmissible
            host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
            hnonempty)).renameRelations
        (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf)) =
        Region.mk
          ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
              input.site).length +
            (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
              input.binderSpine.bodyContainer).length)
          (hostPrepared.append patternPrepared) := by
    simp only [Region.spliceAt, Region.adjoinAt,
      ConcreteElaboration.finishRegion, Region.renameWires,
      Region.renameRelations]
    rw [ItemSeq.renameRelations_append _ _ _]
    rw [← ItemSeq.renameWires_renameRelations]
    rw [ItemSeq.renameRelations_comp]
    simp only [ItemSeq.castWiresEq_eq_renameWires,
      ItemSeq.renameWires_comp]
    apply congrArg (Region.mk
      ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
          input.site).length +
        (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
          input.binderSpine.bodyContainer).length))
    congr 1
    unfold patternPrepared
    exact congrArg
      (fun wireMap =>
        (patternLeaf.items.renameWires wireMap).renameRelations
          (fun {arity} relation =>
            layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
              outputWitness outputLeaf
              (layout.coalescedTerminalRelationRenaming hadmissible
                host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
                hnonempty relation)))
      hpatternMap
  have hnormalized : RegionIso signature
      (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf)
      outputWitness.toFocus.holeRels
      (Region.mk
        ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
            input.site).length +
          (ConcreteElaboration.exactScopeWires input.pattern.val.diagram
            input.binderSpine.bodyContainer).length)
        (hostPrepared.append patternPrepared))
      (ConcreteElaboration.finishRegion layout.plugRaw
        outputLeaf.inheritedWires (layout.frameRegion input.site)
        outputLeaf.items) := by
    simpa only [ConcreteElaboration.finishRegion] using hregion
  exact hsourceEq.symm ▸ hnormalized

/-- The nonempty-site compiler theorem commutes at the complete elaborated
root, not merely at the focused site.  The statement is parametric in the
root's ambient wire and relation environments, so it can be reused for open
proof-state replay as well as closed diagrams. -/
theorem compiledWholeRootDenotationOfNonempty
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Region.ContextPath.CompilerLeaf input.pattern.val.diagram
      input.binderSpine.bodyContainer patternWitness)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin outputOuter → model.Carrier)
    (relEnv : RelEnv model.Carrier outputRels) :
    let source :=
      ((Region.spliceAt
          (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
            input.site).length
          (host.compilerLeaf.items.castWiresEq
            (ConcreteElaboration.WireContext.length_extend
              host.compilerLeaf.inheritedWires input.site))
          (ConcreteElaboration.finishRegion input.pattern.val.diagram
            patternLeaf.inheritedWires input.binderSpine.bodyContainer
            patternLeaf.items)
          (fun index => Fin.cast
            (ConcreteElaboration.WireContext.length_extend
              host.compilerLeaf.inheritedWires input.site)
            (layout.bodyTerminalWireRenaming hadmissible host patternWitness
              patternLeaf hnonempty index))
          (layout.coalescedTerminalRelationRenaming hadmissible
            host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
            hnonempty)).renameRelations
        (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf))
    let rootWireEquiv :=
      (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf).trans
        (FiniteEquiv.finCast outputLeaf.inheritedLength)
    denoteRegion model named env relEnv
        (outputWitness.toFocus.context.fill
          (source.renameWires rootWireEquiv)) ↔
      denoteRegion model named env relEnv outputBody := by
  dsimp only
  have hiso := layout.compiledSiteRegionIsoOfNonempty signature input
    hadmissible host patternWitness patternLeaf outputWitness outputLeaf
    hnonempty
  have hlift := regionIso_fill_denotation_cast hiso
    outputLeaf.inheritedLength outputWitness.toFocus.context model named env
    relEnv
  rw [← outputLeaf.bodyComputation,
    outputWitness.toFocus.rebuild] at hlift
  exact hlift

/-- Ordered-open-interface form of the nonempty whole-root compiler theorem.
The replacement body shares the output's external carrier and exact boundary
class map, so repeated boundary positions remain repeated positions. -/
theorem compiledOpenWholeRootDenotationOfNonempty
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {patternBody : Region signature patternOuter patternRels}
    {patternPath : List Nat}
    (patternWitness : Region.ContextPath patternBody patternPath)
    (patternLeaf : Region.ContextPath.CompilerLeaf input.pattern.val.diagram
      input.binderSpine.bodyContainer patternWitness)
    (output : OpenDiagram signature arity)
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath output.body outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hnonempty : input.binderSpine.proxyCount ≠ 0)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin arity → model.Carrier) :
    let source :=
      ((Region.spliceAt
          (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
            input.site).length
          (host.compilerLeaf.items.castWiresEq
            (ConcreteElaboration.WireContext.length_extend
              host.compilerLeaf.inheritedWires input.site))
          (ConcreteElaboration.finishRegion input.pattern.val.diagram
            patternLeaf.inheritedWires input.binderSpine.bodyContainer
            patternLeaf.items)
          (fun index => Fin.cast
            (ConcreteElaboration.WireContext.length_extend
              host.compilerLeaf.inheritedWires input.site)
            (layout.bodyTerminalWireRenaming hadmissible host patternWitness
              patternLeaf hnonempty index))
          (layout.coalescedTerminalRelationRenaming hadmissible
            host.intrinsicPath host.compilerLeaf patternWitness patternLeaf
            hnonempty)).renameRelations
        (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf))
    let rootWireEquiv :=
      (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf).trans
        (FiniteEquiv.finCast outputLeaf.inheritedLength)
    let sourceBody := outputWitness.toFocus.context.fill
      (source.renameWires rootWireEquiv)
    denoteOpen model named (replaceOpenBody output sourceBody) args ↔
      denoteOpen model named output args := by
  dsimp only
  apply denote_replaceOpenBody_iff
  intro env
  exact layout.compiledWholeRootDenotationOfNonempty signature input
    hadmissible host patternWitness patternLeaf outputWitness outputLeaf
    hnonempty model named env PUnit.unit

/-- The concrete compiler implements intrinsic capture-avoiding splicing when
the proxy spine is empty.  Here the material is the open sheet root: exposed
wires are substituted into the host site and hidden root wires become the
new local block. -/
theorem compiledSiteRegionIsoOfEmpty
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hzero : input.binderSpine.proxyCount = 0)
    (patternItems : ItemSeq signature
      (input.pattern.val.exposedWires ++
        input.pattern.val.hiddenWires).length [])
    (patternItemsComputation :
      ConcreteElaboration.compileOccurrencesWith? signature
        input.pattern.val.diagram
        (ConcreteElaboration.compileRegion? signature
          input.pattern.val.diagram input.pattern.val.diagram.regionCount)
        (input.pattern.val.exposedWires ++ input.pattern.val.hiddenWires)
        ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences input.pattern.val.diagram
          input.pattern.val.diagram.root) = some patternItems) :
    RegionIso signature
      (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf)
      outputWitness.toFocus.holeRels
      ((Region.spliceAt
          (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
            input.site).length
          (host.compilerLeaf.items.castWiresEq
            (ConcreteElaboration.WireContext.length_extend
              host.compilerLeaf.inheritedWires input.site))
          (ConcreteElaboration.finishRoot input.pattern.val.exposedWires
            input.pattern.val.hiddenWires patternItems)
          (fun index => Fin.cast
            (ConcreteElaboration.WireContext.length_extend
              host.compilerLeaf.inheritedWires input.site)
            (layout.exposedWireRenaming hadmissible host index))
          (emptyRelationRenaming host.intrinsicPath.toFocus.holeRels))
        |>.renameRelations
          (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
            outputWitness outputLeaf))
      (ConcreteElaboration.finishRegion layout.plugRaw
        outputLeaf.inheritedWires (layout.frameRegion input.site)
        outputLeaf.items) := by
  let hostPrepared :=
    (host.compilerLeaf.items.renameWires
      (layout.hostSeamPreparedWireOfEmpty hadmissible host)).renameRelations
      (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf)
  let patternPrepared :=
    (patternItems.renameWires
      (layout.patternRootSeamPreparedWireOfEmpty hadmissible host))
        |>.renameRelations
          (emptyRelationRenaming outputWitness.toFocus.holeRels)
  have hitems := layout.compiledSiteItemsIsoOfEmpty signature input
    hadmissible host outputWitness outputLeaf hzero patternItems
    patternItemsComputation
  have hregion := RegionIso.mk
    (layout.siteLocalWireEquivOfEmpty hzero) hitems
  have hpatternMap :
      Region.adjoinMaterialWire
          host.compilerLeaf.inheritedWires.length
          (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
            input.site).length
          input.pattern.val.hiddenWires.length ∘
        extendWireRenaming
          (fun index => Fin.cast
            (ConcreteElaboration.WireContext.length_extend
              host.compilerLeaf.inheritedWires input.site)
            (layout.exposedWireRenaming hadmissible host index))
          input.pattern.val.hiddenWires.length ∘
        Fin.cast (by simp) =
      layout.patternRootSeamPreparedWireOfEmpty hadmissible host := by
    funext index
    let split : Fin (input.pattern.val.exposedWires.length +
        input.pattern.val.hiddenWires.length) := Fin.cast (by simp) index
    have hrecover : Fin.cast (by simp) split = index := by
      apply Fin.ext
      rfl
    rw [← hrecover]
    refine Fin.addCases (fun exposed => ?_) (fun hidden => ?_) split
    · apply Fin.ext
      simp [patternRootSeamPreparedWireOfEmpty, Function.comp_apply,
        extendWireRenaming, hostSeamPreparedWireOfEmpty,
        Region.adjoinMaterialWire, Region.adjoinHostWire]
    · apply Fin.ext
      simp [patternRootSeamPreparedWireOfEmpty, Function.comp_apply,
        extendWireRenaming, Region.adjoinMaterialWire, Input.coalesceFrame]
      omega
  have hrelations :
      ((fun {arity} (relation : Theory.RelVar [] arity) =>
        layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf
          (emptyRelationRenaming host.intrinsicPath.toFocus.holeRels
            relation)) : RelationRenaming []
              outputWitness.toFocus.holeRels) =
        ((fun {arity} (relation : Theory.RelVar [] arity) =>
          emptyRelationRenaming outputWitness.toFocus.holeRels relation) :
          RelationRenaming [] outputWitness.toFocus.holeRels) := by
    apply @funext
    intro arity
    funext relation
    exact Fin.elim0 relation.index
  have hsourceEq :
      ((Region.spliceAt
          (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
            input.site).length
          (host.compilerLeaf.items.castWiresEq
            (ConcreteElaboration.WireContext.length_extend
              host.compilerLeaf.inheritedWires input.site))
          (ConcreteElaboration.finishRoot input.pattern.val.exposedWires
            input.pattern.val.hiddenWires patternItems)
          (fun index => Fin.cast
            (ConcreteElaboration.WireContext.length_extend
              host.compilerLeaf.inheritedWires input.site)
            (layout.exposedWireRenaming hadmissible host index))
          (emptyRelationRenaming host.intrinsicPath.toFocus.holeRels))
        |>.renameRelations
          (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
            outputWitness outputLeaf)) =
        Region.mk
          ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
              input.site).length + input.pattern.val.hiddenWires.length)
          (hostPrepared.append patternPrepared) := by
    simp only [Region.spliceAt, Region.adjoinAt,
      ConcreteElaboration.finishRoot, Region.renameWires,
      Region.renameRelations]
    rw [ItemSeq.renameRelations_append _ _ _]
    rw [← ItemSeq.renameWires_renameRelations]
    rw [ItemSeq.renameRelations_comp]
    simp only [ItemSeq.castWiresEq_eq_renameWires,
      ItemSeq.renameWires_comp, hrelations]
    apply congrArg (Region.mk
      ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
          input.site).length + input.pattern.val.hiddenWires.length))
    congr 1
    unfold patternPrepared
    exact congrArg
      (fun wireMap =>
        (patternItems.renameWires wireMap).renameRelations
          (emptyRelationRenaming outputWitness.toFocus.holeRels))
      hpatternMap
  have hnormalized : RegionIso signature
      (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf)
      outputWitness.toFocus.holeRels
      (Region.mk
        ((ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
            input.site).length + input.pattern.val.hiddenWires.length)
        (hostPrepared.append patternPrepared))
      (ConcreteElaboration.finishRegion layout.plugRaw
        outputLeaf.inheritedWires (layout.frameRegion input.site)
        outputLeaf.items) := by
    simpa only [ConcreteElaboration.finishRegion] using hregion
  exact hsourceEq.symm ▸ hnormalized

/-- Empty-spine counterpart of `compiledWholeRootDenotationOfNonempty`.
The open sheet root is substituted at the site, then the local compiler
equivalence is lifted through every enclosing cut or bubble to the complete
elaborated root. -/
theorem compiledWholeRootDenotationOfEmpty
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {outputBody : Region signature outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hzero : input.binderSpine.proxyCount = 0)
    (patternItems : ItemSeq signature
      (input.pattern.val.exposedWires ++
        input.pattern.val.hiddenWires).length [])
    (patternItemsComputation :
      ConcreteElaboration.compileOccurrencesWith? signature
        input.pattern.val.diagram
        (ConcreteElaboration.compileRegion? signature
          input.pattern.val.diagram input.pattern.val.diagram.regionCount)
        (input.pattern.val.exposedWires ++ input.pattern.val.hiddenWires)
        ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences input.pattern.val.diagram
          input.pattern.val.diagram.root) = some patternItems)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (env : Fin outputOuter → model.Carrier)
    (relEnv : RelEnv model.Carrier outputRels) :
    let source :=
      ((Region.spliceAt
          (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
            input.site).length
          (host.compilerLeaf.items.castWiresEq
            (ConcreteElaboration.WireContext.length_extend
              host.compilerLeaf.inheritedWires input.site))
          (ConcreteElaboration.finishRoot input.pattern.val.exposedWires
            input.pattern.val.hiddenWires patternItems)
          (fun index => Fin.cast
            (ConcreteElaboration.WireContext.length_extend
              host.compilerLeaf.inheritedWires input.site)
            (layout.exposedWireRenaming hadmissible host index))
          (emptyRelationRenaming host.intrinsicPath.toFocus.holeRels))
        |>.renameRelations
          (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
            outputWitness outputLeaf))
    let rootWireEquiv :=
      (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf).trans
        (FiniteEquiv.finCast outputLeaf.inheritedLength)
    denoteRegion model named env relEnv
        (outputWitness.toFocus.context.fill
          (source.renameWires rootWireEquiv)) ↔
      denoteRegion model named env relEnv outputBody := by
  dsimp only
  have hiso := layout.compiledSiteRegionIsoOfEmpty signature input
    hadmissible host outputWitness outputLeaf hzero patternItems
    patternItemsComputation
  have hlift := regionIso_fill_denotation_cast hiso
    outputLeaf.inheritedLength outputWitness.toFocus.context model named env
    relEnv
  rw [← outputLeaf.bodyComputation,
    outputWitness.toFocus.rebuild] at hlift
  exact hlift

/-- Ordered-open-interface form of the empty-spine whole-root theorem. -/
theorem compiledOpenWholeRootDenotationOfEmpty
    (signature : List Nat)
    (input : Input signature)
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    (output : OpenDiagram signature arity)
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath output.body outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    (hzero : input.binderSpine.proxyCount = 0)
    (patternItems : ItemSeq signature
      (input.pattern.val.exposedWires ++
        input.pattern.val.hiddenWires).length [])
    (patternItemsComputation :
      ConcreteElaboration.compileOccurrencesWith? signature
        input.pattern.val.diagram
        (ConcreteElaboration.compileRegion? signature
          input.pattern.val.diagram input.pattern.val.diagram.regionCount)
        (input.pattern.val.exposedWires ++ input.pattern.val.hiddenWires)
        ConcreteElaboration.BinderContext.empty
        (ConcreteElaboration.localOccurrences input.pattern.val.diagram
          input.pattern.val.diagram.root) = some patternItems)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin arity → model.Carrier) :
    let source :=
      ((Region.spliceAt
          (ConcreteElaboration.exactScopeWires input.coalesceFrameRaw
            input.site).length
          (host.compilerLeaf.items.castWiresEq
            (ConcreteElaboration.WireContext.length_extend
              host.compilerLeaf.inheritedWires input.site))
          (ConcreteElaboration.finishRoot input.pattern.val.exposedWires
            input.pattern.val.hiddenWires patternItems)
          (fun index => Fin.cast
            (ConcreteElaboration.WireContext.length_extend
              host.compilerLeaf.inheritedWires input.site)
            (layout.exposedWireRenaming hadmissible host index))
          (emptyRelationRenaming host.intrinsicPath.toFocus.holeRels))
        |>.renameRelations
          (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
            outputWitness outputLeaf))
    let rootWireEquiv :=
      (layout.inheritedWireEquiv host.intrinsicPath host.compilerLeaf
        outputWitness outputLeaf).trans
        (FiniteEquiv.finCast outputLeaf.inheritedLength)
    let sourceBody := outputWitness.toFocus.context.fill
      (source.renameWires rootWireEquiv)
    denoteOpen model named (replaceOpenBody output sourceBody) args ↔
      denoteOpen model named output args := by
  dsimp only
  apply denote_replaceOpenBody_iff
  intro env
  exact layout.compiledWholeRootDenotationOfEmpty signature input
    hadmissible host outputWitness outputLeaf hzero patternItems
    patternItemsComputation model named env PUnit.unit

end PlugLayout

end VisualProof.Diagram.Splice.Input
