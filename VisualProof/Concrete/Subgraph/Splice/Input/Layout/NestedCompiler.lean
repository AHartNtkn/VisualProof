import VisualProof.Concrete.Subgraph.Splice.Input.Layout.OccurrenceCompiler

namespace VisualProof.Concrete.Splice.Input

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram
open VisualProof.Concrete.Elaboration

namespace PlugLayout


/-- Root counterpart of `compileFrameSiblings_targetCoordinates`.  At a
proper nested site the caller's open-root split itself is an exact context,
so siblings are compiled directly in open coordinates. -/
noncomputable def compileNestedRootSiblings
    (input : Input )
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (sourceBoundary : List (Fin input.frame.val.wireCount))
    (sourceRoot : ∀ wire, wire ∈ sourceBoundary →
      (input.frame.val.wires wire).scope = input.frame.val.root)
    (hnested : input.site ≠ input.frame.val.root)
    (child : Fin input.coalesceFrameRaw.regionCount)
    (hparent : (input.coalesceFrameRaw.regions child).parent? =
      some input.coalesceFrameRaw.root)
    (sourcePosition : Fin (Elaboration.localOccurrences
      input.coalesceFrameRaw input.coalesceFrameRaw.root).length)
    (hposition : indexOf? (Elaboration.localOccurrences
      input.coalesceFrameRaw input.coalesceFrameRaw.root) (.child child) =
        some sourcePosition)
    (tail : RegionRoute input.coalesceFrameRaw child input.site rest)
    (sourceItems : ItemSeq
      (coalescedOpenRoot input sourceBoundary).rootWires.length [])
    (targetItems : ItemSeq
      (outputOpenRoot input layout sourceBoundary).rootWires.length [])
    (hsourceItems : Elaboration.compileOccurrencesWith?
      input.coalesceFrameRaw
      (Elaboration.compileRegion?  input.coalesceFrameRaw
        input.coalesceFrameRaw.regionCount)
      (coalescedOpenRoot input sourceBoundary).rootWires
      Elaboration.BinderContext.empty
      (Elaboration.localOccurrences input.coalesceFrameRaw
        input.coalesceFrameRaw.root) = some sourceItems)
    (htargetItems : Elaboration.compileOccurrencesWith?
      layout.plugRaw
      (Elaboration.compileRegion?  layout.plugRaw
        layout.plugRaw.regionCount)
      (outputOpenRoot input layout sourceBoundary).rootWires
      Elaboration.BinderContext.empty
      (Elaboration.localOccurrences layout.plugRaw
        layout.plugRaw.root) = some targetItems) :
    ItemSeqIso.Frame.Indexed sourceItems targetItems
      (nestedRootWireEquiv input layout sourceBoundary hnested)
      sourcePosition.val
      (layout.frameOccurrenceEquiv input.coalesceFrameRaw.root
        (by intro heq; exact hnested heq.symm) sourcePosition).val := by
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
  let sourceCover := Elaboration.BinderContext.empty_covers_root
    (input.coalesceFrameRaw_wellFormed hadmissible)
  let targetCover := Elaboration.BinderContext.empty_covers_root
    (layout.plugRaw_wellFormed  input hadmissible)
  let sourceEnumeration :=
    Elaboration.BinderContext.Enumeration.empty
      input.coalesceFrameRaw
  have sourceLength := Elaboration.compileOccurrencesWith?_length
    (Elaboration.compileRegion?  input.coalesceFrameRaw
      input.coalesceFrameRaw.regionCount)
    sourceOpen.rootWires Elaboration.BinderContext.empty hsourceItems
  have targetLength := Elaboration.compileOccurrencesWith?_length
    (Elaboration.compileRegion?  layout.plugRaw
      layout.plugRaw.regionCount)
    targetOpen.rootWires Elaboration.BinderContext.empty htargetItems
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
  refine ⟨sourceIndex, targetIndex, rfl, rfl, {
    positions := positions
    mapped := hmapped
    siblings := ?_
  }⟩
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
  have hsourceGet := Elaboration.compileOccurrencesWith?_get
    (Elaboration.compileRegion?  input.coalesceFrameRaw
      input.coalesceFrameRaw.regionCount)
    sourceOpen.rootWires Elaboration.BinderContext.empty hsourceItems
    occurrenceIndex
  have htargetGet := Elaboration.compileOccurrencesWith?_get
    (Elaboration.compileRegion?  layout.plugRaw
      layout.plugRaw.regionCount)
    targetOpen.rootWires Elaboration.BinderContext.empty htargetItems
    targetOccurrenceIndex
  have htargetOccurrence :
      (Elaboration.localOccurrences layout.plugRaw
        layout.plugRaw.root).get targetOccurrenceIndex =
        layout.mapFrameOccurrence
          ((Elaboration.localOccurrences input.coalesceFrameRaw
            input.coalesceFrameRaw.root).get occurrenceIndex) := by
    change
      (Elaboration.localOccurrences layout.plugRaw
        (layout.frameRegion input.coalesceFrameRaw.root)).get
          (layout.frameOccurrenceEquiv input.coalesceFrameRaw.root hrootNe
            occurrenceIndex) = _
    exact layout.frameOccurrenceEquiv_spec input.coalesceFrameRaw.root
      hrootNe occurrenceIndex
  rw [htargetOccurrence] at htargetGet
  let occurrence := (Elaboration.localOccurrences
    input.coalesceFrameRaw input.coalesceFrameRaw.root).get occurrenceIndex
  have hoccurrenceMem := List.get_mem
    (Elaboration.localOccurrences input.coalesceFrameRaw
      input.coalesceFrameRaw.root) occurrenceIndex
  change occurrence ∈ Elaboration.localOccurrences
    input.coalesceFrameRaw input.coalesceFrameRaw.root at hoccurrenceMem
  change Elaboration.compileOccurrenceWith?
    input.coalesceFrameRaw
    (Elaboration.compileRegion?  input.coalesceFrameRaw
      input.coalesceFrameRaw.regionCount)
    sourceOpen.rootWires Elaboration.BinderContext.empty occurrence =
      some (sourceItems.get sourceOriginalIndex) at hsourceGet
  change Elaboration.compileOccurrenceWith?  layout.plugRaw
    (Elaboration.compileRegion?  layout.plugRaw
      layout.plugRaw.regionCount)
    targetOpen.rootWires Elaboration.BinderContext.empty
      (layout.mapFrameOccurrence occurrence) =
        some (targetItems.get targetOriginalIndex) at htargetGet
  have childAway : ∀ sibling, occurrence = .child sibling →
      ¬ input.coalesceFrameRaw.Encloses sibling input.site := by
    intro sibling hsibling
    have siblingParent :=
      (Elaboration.mem_localOccurrences_child _ _ _).1
        (show Elaboration.LocalOccurrence.child sibling ∈
          Elaboration.localOccurrences input.coalesceFrameRaw
            input.coalesceFrameRaw.root by
          rw [← hsibling]
          exact hoccurrenceMem)
    have hsiblingNe : sibling ≠ child := by
      intro heq
      subst sibling
      have hindexOf := indexOf?_get_eq_some_of_nodup
        (Elaboration.localOccurrences_nodup _ _) occurrenceIndex
      have hsome : some occurrenceIndex = some sourcePosition := by
        rw [← hindexOf, ← hposition]
        congr 1
      exact hoccurrenceNe (Option.some.inj hsome)
    exact RegionRoute.distinctSibling_away
      (input.coalesceFrameRaw_wellFormed hadmissible) tail hparent
      siblingParent hsiblingNe
  have hitem : ItemIso  rootWire []
      (sourceItems.get sourceOriginalIndex)
      (targetItems.get targetOriginalIndex) := by
    cases hoccurrence : occurrence with
    | node node =>
        rw [hoccurrence] at hoccurrenceMem hsourceGet htargetGet
        have hnodeRegion :=
          (Elaboration.mem_localOccurrences_node _ _ _).1
            hoccurrenceMem
        have hmap := layout.compileFrameNode_at_region_of_maps  input
          hadmissible input.coalesceFrameRaw.root sourceOpen.rootWires
          targetOpen.rootWires sourceExact targetExact
          Elaboration.BinderContext.empty
          Elaboration.BinderContext.empty sourceCover sourceEnumeration
          rootWire (nestedRootWireEquiv_spec input layout sourceBoundary hnested)
          (fun {_} relation => relation)
          (by intro arity relation; exact Fin.elim0 relation.index)
          node hnodeRegion
        have hsourceNode : Elaboration.compileNode?
            input.coalesceFrameRaw sourceOpen.rootWires
              Elaboration.BinderContext.empty node =
            some (sourceItems.get sourceOriginalIndex) := by
          simpa [occurrence, Elaboration.compileOccurrenceWith?] using
            hsourceGet
        have htargetNode : Elaboration.compileNode?
            layout.plugRaw targetOpen.rootWires
              Elaboration.BinderContext.empty (layout.frameNode node) =
            some (targetItems.get targetOriginalIndex) := by
          simpa [occurrence, PlugLayout.mapFrameOccurrence,
            Elaboration.compileOccurrenceWith?] using htargetGet
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
          (Elaboration.mem_localOccurrences_child _ _ _).1
            hoccurrenceMem
        cases hsibling : input.coalesceFrameRaw.regions sibling with
        | sheet =>
            change input.frame.val.regions sibling = .sheet at hsibling
            simp [Elaboration.compileOccurrenceWith?,
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
              (layout.plugRaw_wellFormed  input hadmissible)
              htargetParent
            cases hsourceChild : Elaboration.compileRegion?
                input.coalesceFrameRaw input.coalesceFrameRaw.regionCount
                sibling sourceOpen.rootWires
                Elaboration.BinderContext.empty with
            | none =>
                change Elaboration.compileRegion?
                  input.coalesceFrameRaw input.frame.val.regionCount sibling
                  sourceOpen.rootWires
                    Elaboration.BinderContext.empty = none at hsourceChild
                simp [Elaboration.compileOccurrenceWith?, hsibling,
                  hsourceChild] at hsourceGet
            | some compiledSource =>
                change Elaboration.compileRegion?
                  input.coalesceFrameRaw input.frame.val.regionCount sibling
                  sourceOpen.rootWires
                    Elaboration.BinderContext.empty =
                      some compiledSource at hsourceChild
                simp [Elaboration.compileOccurrenceWith?, hsibling,
                  hsourceChild] at hsourceGet
                cases htargetChild : Elaboration.compileRegion?
                     layout.plugRaw layout.plugRaw.regionCount
                    (layout.frameRegion sibling) targetOpen.rootWires
                    Elaboration.BinderContext.empty with
                | none =>
                    simp [PlugLayout.mapFrameOccurrence,
                      Elaboration.compileOccurrenceWith?,
                      htargetSibling, htargetChild] at htargetGet
                | some compiledTarget =>
                    simp [PlugLayout.mapFrameOccurrence,
                      Elaboration.compileOccurrenceWith?,
                      htargetSibling, htargetChild] at htargetGet
                    have hrecursive := layout.compileFrameRegion_away_from_site
                       input hadmissible input.coalesceFrameRaw.regionCount
                      layout.plugRaw.regionCount sibling haway
                      sourceOpen.rootWires targetOpen.rootWires
                      hsourceChildExact htargetChildExact
                      Elaboration.BinderContext.empty
                      Elaboration.BinderContext.empty
                      (Elaboration.BinderContext.covers_cut_child
                        sourceCover hsibling)
                      (Elaboration.BinderContext.covers_cut_child
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
                    have hrecursive' : RegionIso
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
                    have hcut : ItemIso  rootWire []
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
              (layout.plugRaw_wellFormed  input hadmissible)
              htargetParent
            cases hsourceChild : Elaboration.compileRegion?
                input.coalesceFrameRaw input.coalesceFrameRaw.regionCount
                sibling sourceOpen.rootWires
                (Elaboration.BinderContext.empty.push sibling arity) with
            | none =>
                change Elaboration.compileRegion?
                  input.coalesceFrameRaw input.frame.val.regionCount sibling
                  sourceOpen.rootWires
                    (Elaboration.BinderContext.empty.push sibling
                      arity) = none at hsourceChild
                simp [Elaboration.compileOccurrenceWith?, hsibling,
                  hsourceChild] at hsourceGet
            | some compiledSource =>
                change Elaboration.compileRegion?
                  input.coalesceFrameRaw input.frame.val.regionCount sibling
                  sourceOpen.rootWires
                    (Elaboration.BinderContext.empty.push sibling
                      arity) = some compiledSource at hsourceChild
                simp [Elaboration.compileOccurrenceWith?, hsibling,
                  hsourceChild] at hsourceGet
                cases htargetChild : Elaboration.compileRegion?
                     layout.plugRaw layout.plugRaw.regionCount
                    (layout.frameRegion sibling) targetOpen.rootWires
                    (Elaboration.BinderContext.empty.push
                      (layout.frameRegion sibling) arity) with
                | none =>
                    simp [PlugLayout.mapFrameOccurrence,
                      Elaboration.compileOccurrenceWith?,
                      htargetSibling, htargetChild] at htargetGet
                | some compiledTarget =>
                    simp [PlugLayout.mapFrameOccurrence,
                      Elaboration.compileOccurrenceWith?,
                      htargetSibling, htargetChild] at htargetGet
                    have hrecursive := layout.compileFrameRegion_away_from_site
                       input hadmissible input.coalesceFrameRaw.regionCount
                      layout.plugRaw.regionCount sibling haway
                      sourceOpen.rootWires targetOpen.rootWires
                      hsourceChildExact htargetChildExact
                      (Elaboration.BinderContext.empty.push sibling arity)
                      (Elaboration.BinderContext.empty.push
                        (layout.frameRegion sibling) arity)
                      (Elaboration.BinderContext.push_covers_bubble_child
                        sourceCover hsibling)
                      (Elaboration.BinderContext.push_covers_bubble_child
                        targetCover htargetSibling)
                      (sourceEnumeration.bubbleChild
                        (input.coalesceFrameRaw_wellFormed hadmissible) hsibling)
                      rootWire
                      (nestedRootWireEquiv_spec input layout sourceBoundary
                        hnested)
                      (RelationRenaming.lift (fun {_} relation => relation) arity)
                      (layout.frameRelationLookup_bubbleChild hadmissible
                        input.coalesceFrameRaw.root sibling
                        Elaboration.BinderContext.empty
                        Elaboration.BinderContext.empty
                        sourceEnumeration arity hsibling
                        (fun {_} relation => relation)
                        (by intro a relation; exact Fin.elim0 relation.index))
                      compiledSource compiledTarget hsourceChild htargetChild
                    have hrename := RegionIso.renameWiresEquiv compiledSource
                      rootWire
                    have hrecursive' : RegionIso
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
                    have hbubble : ItemIso  rootWire []
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

noncomputable def compileHostOccurrence_at_seam_iso_of_maps
    (input : Input )
    (layout : PlugLayout input)
    (hadmissible : input.Admissible)
    (host : SiteView (input.coalesceFrame hadmissible) input.site)
    {outputBody : Region  outputOuter outputRels}
    {outputPath : List Nat}
    (outputWitness : Region.ContextPath outputBody outputPath)
    (outputLeaf : Region.ContextPath.CompilerLeaf layout.plugRaw
      (layout.frameRegion input.site) outputWitness)
    {preparedWires : Nat}
    (combined : FiniteEquiv (Fin preparedWires)
      (Fin (outputLeaf.inheritedWires.length +
        (Elaboration.exactScopeWires layout.plugRaw
          (layout.frameRegion input.site)).length)))
    (sourcePreparedMap : Fin
        (host.compilerLeaf.inheritedWires.extend input.site).length →
      Fin preparedWires)
    (hwire :
      (combined.trans (FiniteEquiv.finCast
        (Elaboration.WireContext.length_extend
          outputLeaf.inheritedWires
          (layout.frameRegion input.site)).symm)).toFun ∘
          sourcePreparedMap =
        layout.hostSiteWireIndexMap host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf)
    (occurrence : Elaboration.LocalOccurrence
      input.coalesceFrameRaw.regionCount input.coalesceFrameRaw.nodeCount)
    (hoccurrence : occurrence ∈ Elaboration.localOccurrences
      input.coalesceFrameRaw input.site)
    (sourceItem : Item
      (host.compilerLeaf.inheritedWires.extend input.site).length
      host.intrinsicPath.toFocus.holeRels)
    (targetItem : Item
      (outputLeaf.inheritedWires.extend
        (layout.frameRegion input.site)).length
      outputWitness.toFocus.holeRels)
    (hsource : Elaboration.compileOccurrenceWith?
      input.coalesceFrameRaw
      (Elaboration.compileRegion?  input.coalesceFrameRaw
        host.compilerLeaf.fuel)
      (host.compilerLeaf.inheritedWires.extend input.site)
      host.compilerLeaf.binders occurrence = some sourceItem)
    (htarget : Elaboration.compileOccurrenceWith?
      layout.plugRaw
      (Elaboration.compileRegion?  layout.plugRaw
        outputLeaf.fuel)
      (outputLeaf.inheritedWires.extend (layout.frameRegion input.site))
      outputLeaf.binders (layout.mapFrameOccurrence occurrence) =
        some targetItem) :
    ItemIso
      combined
      outputWitness.toFocus.holeRels
      ((sourceItem.renameWires
        sourcePreparedMap).renameRelations
        (layout.hostRelationRenaming host.intrinsicPath host.compilerLeaf
          outputWitness outputLeaf))
      (targetItem.castWiresEq
        (Elaboration.WireContext.length_extend
          outputLeaf.inheritedWires (layout.frameRegion input.site))) := by
  cases occurrence with
  | node node =>
      have hnodeRegion :=
        (Elaboration.mem_localOccurrences_node _ _ _).1 hoccurrence
      apply layout.compileHostNode_at_seam_iso_of_maps  input
        hadmissible host outputWitness outputLeaf combined sourcePreparedMap
      · funext index
        have h := congrFun hwire index
        apply Fin.ext
        simpa only [FiniteEquiv.trans_apply, FiniteEquiv.finCast,
          Function.comp_apply] using congrArg Fin.val h
      · exact hnodeRegion
      · exact
        (by simpa [Elaboration.compileOccurrenceWith?,
          Input.coalesceFrame] using hsource)
      · exact (by simpa [mapFrameOccurrence,
          Elaboration.compileOccurrenceWith?] using htarget)
  | child child =>
      have hparent :=
        (Elaboration.mem_localOccurrences_child _ _ _).1 hoccurrence
      change (input.frame.val.regions child).parent? = some input.site at hparent
      have hbelow : input.coalesceFrameRaw.Encloses input.site child := by
        refine ⟨⟨1, by
          have := child.isLt
          omega⟩, ?_⟩
        simp [Diagram.climb, hparent]
      have hchildNeSite : child ≠ input.site := by
        intro heq
        subst child
        exact Elaboration.checked_direct_child_not_encloses_parent
          (input.coalesceFrameRaw_wellFormed hadmissible) hparent
          (Diagram.Encloses.refl input.coalesceFrameRaw input.site)
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
        (layout.plugRaw_wellFormed  input hadmissible) htargetParent
      let targetEq := Elaboration.WireContext.length_extend
        outputLeaf.inheritedWires (layout.frameRegion input.site)
      cases hchild : input.frame.val.regions child with
      | sheet =>
          simp [Elaboration.compileOccurrenceWith?, hchild] at hsource
      | cut parent =>
          have hparentEq : parent = input.site := by
            simpa [hchild, CRegion.parent?] using hparent
          subst parent
          have htargetChild := layout.plugRaw_frameRegion_cut child input.site
            hchild
          cases hsourceChild : Elaboration.compileRegion?
              input.coalesceFrameRaw host.compilerLeaf.fuel child
              (host.compilerLeaf.inheritedWires.extend input.site)
              host.compilerLeaf.binders with
          | none =>
              simp [Elaboration.compileOccurrenceWith?, hchild,
                hsourceChild] at hsource
          | some compiledSource =>
              simp [Elaboration.compileOccurrenceWith?, hchild,
                hsourceChild] at hsource
              have hsourceEq : sourceItem = Item.cut compiledSource :=
                (Option.some.inj hsource).symm
              subst sourceItem
              cases htargetChildResult : Elaboration.compileRegion?
                   layout.plugRaw outputLeaf.fuel
                  (layout.frameRegion child)
                  (outputLeaf.inheritedWires.extend
                    (layout.frameRegion input.site)) outputLeaf.binders with
              | none =>
                  simp [mapFrameOccurrence,
                    Elaboration.compileOccurrenceWith?, htargetChild,
                    htargetChildResult] at htarget
              | some compiledTarget =>
                  simp [mapFrameOccurrence,
                    Elaboration.compileOccurrenceWith?, htargetChild,
                    htargetChildResult] at htarget
                  have htargetEq : targetItem = Item.cut compiledTarget :=
                    htarget.symm
                  subst targetItem
                  have hrecursive := layout.compileFrameRegion_below_site
                     input hadmissible host.compilerLeaf.fuel
                    outputLeaf.fuel child hchildNeSite hbelow
                    (host.compilerLeaf.inheritedWires.extend input.site)
                    (outputLeaf.inheritedWires.extend
                      (layout.frameRegion input.site))
                    hsourceChildExact htargetChildExact
                    host.compilerLeaf.binders outputLeaf.binders
                    (Elaboration.BinderContext.covers_cut_child
                      host.compilerLeaf.bindersCover hchild)
                    (Elaboration.BinderContext.covers_cut_child
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
          cases hsourceChild : Elaboration.compileRegion?
              input.coalesceFrameRaw host.compilerLeaf.fuel child
              (host.compilerLeaf.inheritedWires.extend input.site)
              (host.compilerLeaf.binders.push child arity) with
          | none =>
              simp [Elaboration.compileOccurrenceWith?, hchild] at hsource
              let wrap := fun body : Region
                  (host.compilerLeaf.inheritedWires.extend input.site).length
                  (arity :: host.intrinsicPath.toFocus.holeRels) =>
                some (Item.bubble arity body)
              have hbound := congrArg (fun result => result.bind wrap)
                hsourceChild
              have himpossible : (none : Option (Item
                  (host.compilerLeaf.inheritedWires.extend input.site).length
                  host.intrinsicPath.toFocus.holeRels)) = some sourceItem := by
                exact (by simpa only [wrap, Option.bind_none] using
                  hbound.symm.trans hsource)
              contradiction
          | some compiledSource =>
              simp [Elaboration.compileOccurrenceWith?, hchild] at hsource
              let wrap := fun body : Region
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
              cases htargetChildResult : Elaboration.compileRegion?
                   layout.plugRaw outputLeaf.fuel
                  (layout.frameRegion child)
                  (outputLeaf.inheritedWires.extend
                    (layout.frameRegion input.site))
                  (outputLeaf.binders.push (layout.frameRegion child) arity) with
              | none =>
                  simp [mapFrameOccurrence,
                    Elaboration.compileOccurrenceWith?, htargetChild,
                    htargetChildResult] at htarget
              | some compiledTarget =>
                  simp [mapFrameOccurrence,
                    Elaboration.compileOccurrenceWith?, htargetChild,
                    htargetChildResult] at htarget
                  have htargetEq : targetItem =
                      Item.bubble arity compiledTarget :=
                    htarget.symm
                  subst targetItem
                  have hrecursive := layout.compileFrameRegion_below_site
                     input hadmissible host.compilerLeaf.fuel
                    outputLeaf.fuel child hchildNeSite hbelow
                    (host.compilerLeaf.inheritedWires.extend input.site)
                    (outputLeaf.inheritedWires.extend
                      (layout.frameRegion input.site))
                    hsourceChildExact htargetChildExact
                    (host.compilerLeaf.binders.push child arity)
                    (outputLeaf.binders.push (layout.frameRegion child) arity)
                    (Elaboration.BinderContext.push_covers_bubble_child
                      host.compilerLeaf.bindersCover hchild)
                    (Elaboration.BinderContext.push_covers_bubble_child
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

end PlugLayout

end VisualProof.Concrete.Splice.Input
