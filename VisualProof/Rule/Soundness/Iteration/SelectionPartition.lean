import VisualProof.Rule.Soundness.Modal
import VisualProof.Diagram.Concrete.Subgraph.Splice.Trace
import VisualProof.Diagram.ContextPathIsomorphism

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Rule.ModalSoundness

/-- The canonical position equivalence induced by a permutation of two
duplicate-free occurrence lists. -/
noncomputable def permIndexEquiv [DecidableEq α]
    (source target : List α) (permutation : source.Perm target)
    (sourceNodup : source.Nodup) (targetNodup : target.Nodup) :
    FiniteEquiv (Fin source.length) (Fin target.length) where
  toFun := fun index => Classical.choose
    (indexOf?_complete ((permutation.mem_iff).1 (List.get_mem source index)))
  invFun := fun index => Classical.choose
    (indexOf?_complete ((permutation.mem_iff).2 (List.get_mem target index)))
  left_inv := by
    intro index
    apply Fin.ext
    apply (List.getElem_inj sourceNodup).mp
    have forward := indexOf?_sound (Classical.choose_spec
      (indexOf?_complete ((permutation.mem_iff).1
        (List.get_mem source index))))
    have backward := indexOf?_sound (Classical.choose_spec
      (indexOf?_complete ((permutation.mem_iff).2
        (List.get_mem target (Classical.choose
          (indexOf?_complete ((permutation.mem_iff).1
            (List.get_mem source index))))))))
    exact backward.trans forward
  right_inv := by
    intro index
    apply Fin.ext
    apply (List.getElem_inj targetNodup).mp
    have backward := indexOf?_sound (Classical.choose_spec
      (indexOf?_complete ((permutation.mem_iff).2
        (List.get_mem target index))))
    have forward := indexOf?_sound (Classical.choose_spec
      (indexOf?_complete ((permutation.mem_iff).1
        (List.get_mem source (Classical.choose
          (indexOf?_complete ((permutation.mem_iff).2
            (List.get_mem target index))))))))
    exact forward.trans backward

theorem permIndexEquiv_spec [DecidableEq α]
    (source target : List α) (permutation : source.Perm target)
    (sourceNodup : source.Nodup) (targetNodup : target.Nodup)
    (index : Fin source.length) :
    target.get (permIndexEquiv source target permutation sourceNodup
      targetNodup index) = source.get index := by
  unfold permIndexEquiv
  exact indexOf?_sound (Classical.choose_spec
    (indexOf?_complete ((permutation.mem_iff).1
      (List.get_mem source index))))

/-- A compiler occurrence permutation is an intrinsic item-sequence
isomorphism, retaining its exact position equivalence for later focused
replacement. -/
theorem compileOccurrencesWith?_perm_iso
    (diagram : ConcreteDiagram)
    (recurse : ∀ {rels : RelCtx},
      (region : Fin diagram.regionCount) →
      (context : ConcreteElaboration.WireContext diagram) →
      ConcreteElaboration.BinderContext diagram rels →
      Option (Region signature context.length rels))
    (context : ConcreteElaboration.WireContext diagram)
    (binders : ConcreteElaboration.BinderContext diagram rels)
    {sourceOccurrences targetOccurrences : List
      (ConcreteElaboration.LocalOccurrence diagram.regionCount
        diagram.nodeCount)}
    (permutation : sourceOccurrences.Perm targetOccurrences)
    (sourceNodup : sourceOccurrences.Nodup)
    (targetNodup : targetOccurrences.Nodup)
    {sourceItems targetItems : ItemSeq signature context.length rels}
    (sourceCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature diagram recurse
        context binders sourceOccurrences = some sourceItems)
    (targetCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature diagram recurse
        context binders targetOccurrences = some targetItems) :
    ItemSeqIso signature (FiniteEquiv.refl (Fin context.length)) rels
      sourceItems targetItems := by
  let positions := permIndexEquiv sourceOccurrences targetOccurrences
    permutation sourceNodup targetNodup
  have sourceLength := ConcreteElaboration.compileOccurrencesWith?_length
    recurse context binders sourceCompiled
  have targetLength := ConcreteElaboration.compileOccurrencesWith?_length
    recurse context binders targetCompiled
  let itemPositions := (FiniteEquiv.finCast sourceLength).trans
    (positions.trans (FiniteEquiv.finCast targetLength.symm))
  refine ItemSeqIso.permute itemPositions ?_
  intro sourceIndex
  let occurrenceIndex := Fin.cast sourceLength sourceIndex
  have sourceGet := ConcreteElaboration.compileOccurrencesWith?_get recurse
    context binders sourceCompiled occurrenceIndex
  have targetGet := ConcreteElaboration.compileOccurrencesWith?_get recurse
    context binders targetCompiled (positions occurrenceIndex)
  have occurrenceEq : targetOccurrences.get (positions occurrenceIndex) =
      sourceOccurrences.get occurrenceIndex :=
    permIndexEquiv_spec sourceOccurrences targetOccurrences permutation
      sourceNodup targetNodup occurrenceIndex
  rw [occurrenceEq, sourceGet] at targetGet
  have itemEq : targetItems.get (itemPositions sourceIndex) =
      sourceItems.get sourceIndex := by
    have unique := Option.some.inj targetGet
    simpa [itemPositions, occurrenceIndex] using unique.symm
  rw [← itemEq]
  exact ItemIso.refl _

theorem compileOccurrencesWith?_append
    (diagram : ConcreteDiagram)
    (recurse : ∀ {rels : RelCtx},
      (region : Fin diagram.regionCount) →
      (context : ConcreteElaboration.WireContext diagram) →
      ConcreteElaboration.BinderContext diagram rels →
      Option (Region signature context.length rels))
    (context : ConcreteElaboration.WireContext diagram)
    (binders : ConcreteElaboration.BinderContext diagram rels)
    (first second : List (ConcreteElaboration.LocalOccurrence
      diagram.regionCount diagram.nodeCount))
    {firstItems secondItems : ItemSeq signature context.length rels}
    (firstCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature diagram recurse
        context binders first = some firstItems)
    (secondCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature diagram recurse
        context binders second = some secondItems) :
    ConcreteElaboration.compileOccurrencesWith? signature diagram recurse
        context binders (first ++ second) =
      some (firstItems.append secondItems) := by
  induction first generalizing firstItems with
  | nil =>
      simp only [ConcreteElaboration.compileOccurrencesWith?] at firstCompiled
      cases firstCompiled
      simpa using secondCompiled
  | cons head tail induction =>
      simp only [ConcreteElaboration.compileOccurrencesWith?] at firstCompiled ⊢
      cases headResult : ConcreteElaboration.compileOccurrenceWith? signature
          diagram recurse context binders head with
      | none => simp [headResult] at firstCompiled
      | some headItem =>
          cases tailResult : ConcreteElaboration.compileOccurrencesWith?
              signature diagram recurse context binders tail with
          | none => simp [headResult, tailResult] at firstCompiled
          | some tailItems =>
              simp [headResult, tailResult] at firstCompiled
              subst firstItems
              simp [ConcreteElaboration.compileOccurrencesWith?, headResult,
                induction tailResult]
              rfl

/-- The semantic selection partition also retains the exact intrinsic
occurrence permutation used by the compiler. -/
theorem compilerLeaf_partition_iso
    {signature : List Nat}
    (input : CheckedDiagram signature)
    (anchor : Fin input.val.regionCount)
    {outer : Nat} {rels : RelCtx}
    {body : Region signature outer rels}
    (leaf : VisualProof.Diagram.Splice.Region.ContextPath.CompilerLeaf
      input.val anchor (.here body))
    (kept selected : List (ConcreteElaboration.LocalOccurrence
      input.val.regionCount input.val.nodeCount))
    (partition : (kept ++ selected).Perm
      (ConcreteElaboration.localOccurrences input.val anchor))
    {keptItems selectedItems : ItemSeq signature
      (leaf.inheritedWires.extend anchor).length rels}
    (keptCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature input.val
          (ConcreteElaboration.compileRegion? signature input.val leaf.fuel)
          (leaf.inheritedWires.extend anchor) leaf.binders kept =
        some keptItems)
    (selectedCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature input.val
          (ConcreteElaboration.compileRegion? signature input.val leaf.fuel)
          (leaf.inheritedWires.extend anchor) leaf.binders selected =
        some selectedItems) :
    ItemSeqIso signature
      (FiniteEquiv.refl (Fin (leaf.inheritedWires.extend anchor).length)) rels
      (keptItems.append selectedItems) leaf.items := by
  let recurse : ∀ {rels : RelCtx},
      (region : Fin input.val.regionCount) →
      (context : ConcreteElaboration.WireContext input.val) →
      ConcreteElaboration.BinderContext input.val rels →
      Option (Region signature context.length rels) :=
    fun {rels} => ConcreteElaboration.compileRegion? signature input.val
      leaf.fuel
  have sourceCompiled := compileOccurrencesWith?_append input.val recurse
    (leaf.inheritedWires.extend anchor) leaf.binders kept selected
    keptCompiled selectedCompiled
  have sourceNodup : (kept ++ selected).Nodup :=
    (partition.nodup_iff).2
      (ConcreteElaboration.localOccurrences_nodup input.val anchor)
  exact compileOccurrencesWith?_perm_iso input.val recurse
    (leaf.inheritedWires.extend anchor) leaf.binders partition sourceNodup
    (ConcreteElaboration.localOccurrences_nodup input.val anchor)
    sourceCompiled leaf.itemsComputation

/-- A retained non-root path survives insertion of selected root siblings and
then follows the compiler's authoritative occurrence permutation to the
corresponding focus in the complete leaf. -/
theorem compilerLeaf_partition_alignRetainedPath
    {signature : List Nat}
    (input : CheckedDiagram signature)
    (anchor : Fin input.val.regionCount)
    {outer : Nat} {rels : RelCtx}
    {body : Region signature outer rels}
    (leaf : VisualProof.Diagram.Splice.Region.ContextPath.CompilerLeaf
      input.val anchor (.here body))
    (kept selected : List (ConcreteElaboration.LocalOccurrence
      input.val.regionCount input.val.nodeCount))
    (partition : (kept ++ selected).Perm
      (ConcreteElaboration.localOccurrences input.val anchor))
    {keptItems selectedItems : ItemSeq signature
      (leaf.inheritedWires.extend anchor).length rels}
    (keptCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature input.val
          (ConcreteElaboration.compileRegion? signature input.val leaf.fuel)
          (leaf.inheritedWires.extend anchor) leaf.binders kept =
        some keptItems)
    (selectedCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature input.val
          (ConcreteElaboration.compileRegion? signature input.val leaf.fuel)
          (leaf.inheritedWires.extend anchor) leaf.binders selected =
        some selectedItems)
    {index : Nat} {rest : List Nat}
    (retained : Region.ContextPath (Region.mk 0 keptItems) (index :: rest)) :
    let extended := retained.appendRootItemsRight selectedItems
    ∃ iso : RegionIso signature
        (FiniteEquiv.refl
          (Fin (leaf.inheritedWires.extend anchor).length)) rels
        (Region.mk 0 (keptItems.append selectedItems))
        (Region.mk 0 leaf.items),
      Nonempty (RegionIso.ContextPathAlignment iso extended) := by
  dsimp only
  have itemIso := compilerLeaf_partition_iso input anchor leaf kept selected
    partition keptCompiled selectedCompiled
  have extendedRefl :
      extendWireEquiv
          (FiniteEquiv.refl
            (Fin (leaf.inheritedWires.extend anchor).length))
          (FiniteEquiv.refl (Fin 0)) =
        FiniteEquiv.refl
          (Fin ((leaf.inheritedWires.extend anchor).length + 0)) := by
    apply FiniteEquiv.ext
    intro wire
    refine Fin.addCases (fun index => ?_) (fun index => ?_) wire
    · simp only [extendWireEquiv_outer, FiniteEquiv.refl_apply]
    · exact Fin.elim0 index
  let iso : RegionIso signature
      (FiniteEquiv.refl
        (Fin (leaf.inheritedWires.extend anchor).length)) rels
      (Region.mk 0 (keptItems.append selectedItems))
      (Region.mk 0 leaf.items) := by
    apply RegionIso.mk (FiniteEquiv.refl (Fin 0))
    rw [extendedRefl]
    simpa using itemIso
  exact ⟨iso, iso.alignContextPath
    (retained.appendRootItemsRight selectedItems)⟩

/-- Exact form of retained-path alignment.  The occurrence certificates pin
the compiler permutation to the concrete authoritative position, so the
resulting target path is the route path rather than merely some isomorphic
focus. -/
theorem compilerLeaf_partition_alignRetainedOccurrence
    {signature : List Nat}
    (input : CheckedDiagram signature)
    (anchor : Fin input.val.regionCount)
    {outer : Nat} {rels : RelCtx}
    {body : Region signature outer rels}
    (leaf : VisualProof.Diagram.Splice.Region.ContextPath.CompilerLeaf
      input.val anchor (.here body))
    (kept selected : List (ConcreteElaboration.LocalOccurrence
      input.val.regionCount input.val.nodeCount))
    (partition : (kept ++ selected).Perm
      (ConcreteElaboration.localOccurrences input.val anchor))
    {keptItems selectedItems : ItemSeq signature
      (leaf.inheritedWires.extend anchor).length rels}
    (keptCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature input.val
          (ConcreteElaboration.compileRegion? signature input.val leaf.fuel)
          (leaf.inheritedWires.extend anchor) leaf.binders kept =
        some keptItems)
    (selectedCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature input.val
          (ConcreteElaboration.compileRegion? signature input.val leaf.fuel)
          (leaf.inheritedWires.extend anchor) leaf.binders selected =
        some selectedItems)
    (occurrence : ConcreteElaboration.LocalOccurrence
      input.val.regionCount input.val.nodeCount)
    (keptPosition : Fin kept.length)
    (fullPosition : Fin
      (ConcreteElaboration.localOccurrences input.val anchor).length)
    (keptAt : indexOf? kept occurrence = some keptPosition)
    (fullAt : indexOf?
      (ConcreteElaboration.localOccurrences input.val anchor) occurrence =
        some fullPosition)
    {rest : List Nat}
    (retained : Region.ContextPath (Region.mk 0 keptItems)
      (keptPosition.val :: rest)) :
    let extended := retained.appendRootItemsRight selectedItems
    ∃ (iso : RegionIso signature
        (FiniteEquiv.refl
          (Fin (leaf.inheritedWires.extend anchor).length)) rels
        (Region.mk 0 (keptItems.append selectedItems))
        (Region.mk 0 leaf.items))
      (alignment : RegionIso.ContextPathAlignment iso extended),
      alignment.targetPath = fullPosition.val :: rest ∧
        ∀ index, (alignment.holeWire index).val = index.val := by
  dsimp only
  let recurse : ∀ {rels : RelCtx},
      (region : Fin input.val.regionCount) →
      (context : ConcreteElaboration.WireContext input.val) →
      ConcreteElaboration.BinderContext input.val rels →
      Option (Region signature context.length rels) :=
    fun {rels} => ConcreteElaboration.compileRegion? signature input.val
      leaf.fuel
  have sourceCompiled := compileOccurrencesWith?_append input.val recurse
    (leaf.inheritedWires.extend anchor) leaf.binders kept selected
    keptCompiled selectedCompiled
  have sourceNodup : (kept ++ selected).Nodup :=
    (partition.nodup_iff).2
      (ConcreteElaboration.localOccurrences_nodup input.val anchor)
  have targetNodup :=
    ConcreteElaboration.localOccurrences_nodup input.val anchor
  let positions := permIndexEquiv (kept ++ selected)
    (ConcreteElaboration.localOccurrences input.val anchor) partition
    sourceNodup targetNodup
  have sourceLength := ConcreteElaboration.compileOccurrencesWith?_length
    recurse (leaf.inheritedWires.extend anchor) leaf.binders sourceCompiled
  have targetLength := ConcreteElaboration.compileOccurrencesWith?_length
    recurse (leaf.inheritedWires.extend anchor) leaf.binders
      leaf.itemsComputation
  let sourceOccurrenceIndex : Fin (kept ++ selected).length :=
    ⟨keptPosition.val, by simp only [List.length_append]; omega⟩
  have sourceOccurrenceGet :
      (kept ++ selected).get sourceOccurrenceIndex = occurrence := by
    have keptGet := indexOf?_sound keptAt
    simpa [sourceOccurrenceIndex, List.get_eq_getElem] using keptGet
  have targetOccurrenceGet :
      (ConcreteElaboration.localOccurrences input.val anchor).get
        fullPosition = occurrence := by
    simpa only [List.get_eq_getElem] using indexOf?_sound fullAt
  have positionMap : positions sourceOccurrenceIndex = fullPosition := by
    apply Fin.ext
    apply (List.getElem_inj targetNodup).mp
    calc
      (ConcreteElaboration.localOccurrences input.val anchor).get
          (positions sourceOccurrenceIndex) =
          (kept ++ selected).get sourceOccurrenceIndex :=
        permIndexEquiv_spec (kept ++ selected)
          (ConcreteElaboration.localOccurrences input.val anchor) partition
          sourceNodup targetNodup sourceOccurrenceIndex
      _ = occurrence := sourceOccurrenceGet
      _ = (ConcreteElaboration.localOccurrences input.val anchor).get
          fullPosition := targetOccurrenceGet.symm
  let itemPositions := (FiniteEquiv.finCast sourceLength).trans
    (positions.trans (FiniteEquiv.finCast targetLength.symm))
  let sourceItemIndex : Fin (keptItems.append selectedItems).length :=
    Fin.cast sourceLength.symm sourceOccurrenceIndex
  let targetItemIndex : Fin leaf.items.length :=
    Fin.cast targetLength.symm fullPosition
  have itemPositionMap : itemPositions sourceItemIndex = targetItemIndex := by
    apply Fin.ext
    change (positions
      (Fin.cast sourceLength
        (Fin.cast sourceLength.symm sourceOccurrenceIndex))).val =
      fullPosition.val
    have castCancel : Fin.cast sourceLength
        (Fin.cast sourceLength.symm sourceOccurrenceIndex) =
          sourceOccurrenceIndex := by
      apply Fin.ext
      rfl
    rw [castCancel, positionMap]
  have itemEq : ∀ sourceIndex,
      leaf.items.get (itemPositions sourceIndex) =
        (keptItems.append selectedItems).get sourceIndex := by
    intro sourceIndex
    let occurrenceIndex := Fin.cast sourceLength sourceIndex
    have sourceGet := ConcreteElaboration.compileOccurrencesWith?_get recurse
      (leaf.inheritedWires.extend anchor) leaf.binders sourceCompiled
      occurrenceIndex
    have targetGet := ConcreteElaboration.compileOccurrencesWith?_get recurse
      (leaf.inheritedWires.extend anchor) leaf.binders leaf.itemsComputation
      (positions occurrenceIndex)
    have occurrenceEq :
        (ConcreteElaboration.localOccurrences input.val anchor).get
            (positions occurrenceIndex) =
          (kept ++ selected).get occurrenceIndex :=
      permIndexEquiv_spec (kept ++ selected)
        (ConcreteElaboration.localOccurrences input.val anchor) partition
        sourceNodup targetNodup occurrenceIndex
    rw [occurrenceEq, sourceGet] at targetGet
    have unique := Option.some.inj targetGet
    simpa [itemPositions, occurrenceIndex] using unique.symm
  have itemIsos : ∀ sourceIndex,
      ItemIso signature
        (FiniteEquiv.refl
          (Fin (leaf.inheritedWires.extend anchor).length)) rels
        ((keptItems.append selectedItems).get sourceIndex)
        (leaf.items.get (itemPositions sourceIndex)) := by
    intro sourceIndex
    rw [itemEq sourceIndex]
    exact ItemIso.refl _
  have extendedRefl :
      extendWireEquiv
          (FiniteEquiv.refl
            (Fin (leaf.inheritedWires.extend anchor).length))
          (FiniteEquiv.refl (Fin 0)) =
        FiniteEquiv.refl
          (Fin ((leaf.inheritedWires.extend anchor).length + 0)) := by
    apply FiniteEquiv.ext
    intro wire
    refine Fin.addCases (fun index => ?_) (fun index => ?_) wire
    · simp only [extendWireEquiv_outer, FiniteEquiv.refl_apply]
    · exact Fin.elim0 index
  let itemSeqIso : ItemSeqIso signature
      (FiniteEquiv.refl
        (Fin (leaf.inheritedWires.extend anchor).length)) rels
      (keptItems.append selectedItems) leaf.items :=
    .permute itemPositions itemIsos
  let iso : RegionIso signature
      (FiniteEquiv.refl
        (Fin (leaf.inheritedWires.extend anchor).length)) rels
      (Region.mk 0 (keptItems.append selectedItems))
      (Region.mk 0 leaf.items) := by
    apply RegionIso.mk (FiniteEquiv.refl (Fin 0))
    rw [extendedRefl]
    exact itemSeqIso
  cases retained with
  | cut focus atIndex isCut nested =>
      let sourceFocus := focus.appendAfter selectedItems
      have sourceAt := ItemSeq.focusAt?_append_left keptItems selectedItems
        keptPosition.val focus atIndex
      have sourceIndexEq : sourceItemIndex =
          ⟨keptPosition.val,
            ItemSeq.focusAt?_index_lt _ _ sourceFocus sourceAt⟩ := by
        apply Fin.ext
        rfl
      obtain ⟨targetFocus, targetAt, targetGet⟩ :=
        ItemSeq.focusAt?_complete leaf.items targetItemIndex
      have targetItemEq : targetFocus.item = sourceFocus.item := by
        have sourceGet := ItemSeq.focusAt?_item _ _ sourceFocus sourceAt
        have mapped := itemEq sourceItemIndex
        rw [itemPositionMap, ← targetGet] at mapped
        rw [sourceIndexEq] at mapped
        rw [← sourceGet] at mapped
        exact mapped
      have targetIsCut : targetFocus.item = .cut _ :=
        targetItemEq.trans (by simpa [sourceFocus] using isCut)
      obtain ⟨child, childPath, childWire⟩ := nested.identityAlignment
      let targetWitness : Region.ContextPath (Region.mk 0 leaf.items)
          (fullPosition.val :: child.targetPath) :=
        .cut targetFocus targetAt targetIsCut child.targetWitness
      let holeRelsEq : targetWitness.toFocus.holeRels =
          nested.toFocus.holeRels := by
        simpa [targetWitness, Region.ContextPath.toFocus] using
          child.holeRelsEq
      let frame : ItemSeqIso.Frame
          (extendWireEquiv
            (FiniteEquiv.refl
              (Fin (leaf.inheritedWires.extend anchor).length))
            (FiniteEquiv.refl (Fin 0)))
          ⟨keptPosition.val,
            ItemSeq.focusAt?_index_lt _ _ sourceFocus sourceAt⟩
          targetItemIndex := by
        apply ItemSeqIso.Frame.castWire extendedRefl.symm
        exact {
          positions := itemPositions
          mapped := by simpa [sourceIndexEq] using itemPositionMap
          siblings := fun sibling _ => itemIsos sibling
        }
      let alignment : RegionIso.ContextPathAlignment iso
          (Region.ContextPath.cut sourceFocus sourceAt isCut nested) := {
        targetPath := fullPosition.val :: child.targetPath
        targetWitness := targetWitness
        holeRelsEq := holeRelsEq
        holeWire := child.holeWire
        context := by
          have childContext : DiagramContextIso signature
              (extendWireEquiv
                (FiniteEquiv.refl
                  (Fin (leaf.inheritedWires.extend anchor).length))
                (FiniteEquiv.refl (Fin 0))) child.holeWire rels
              nested.toFocus.holeRels nested.toFocus.context
              (child.holeRelsEq ▸
                child.targetWitness.toFocus.context) := by
            rw [extendedRefl]
            exact child.context
          have layer := DiagramContextIso.cutFrame
            (FiniteEquiv.refl (Fin 0))
            sourceFocus targetFocus sourceAt targetAt frame
            nested.toFocus.context
            (child.holeRelsEq ▸ child.targetWitness.toFocus.context)
            childContext
          have proofEq : holeRelsEq = child.holeRelsEq :=
            Subsingleton.elim _ _
          rw [proofEq]
          change DiagramContextIso signature _ child.holeWire rels
            nested.toFocus.holeRels
            (DiagramContext.cut 0 sourceFocus.before sourceFocus.after
              nested.toFocus.context)
            (child.holeRelsEq ▸ DiagramContext.cut 0 targetFocus.before
              targetFocus.after child.targetWitness.toFocus.context)
          rw [DiagramContext.castHoleRels_cut]
          exact layer
        body := by
          simpa [targetWitness, Region.ContextPath.toFocus] using child.body
      }
      refine ⟨iso, alignment, ?_, ?_⟩
      · simp only [alignment]
        rw [childPath]
      · intro index
        exact childWire index
  | bubble focus atIndex isBubble nested =>
      let sourceFocus := focus.appendAfter selectedItems
      have sourceAt := ItemSeq.focusAt?_append_left keptItems selectedItems
        keptPosition.val focus atIndex
      have sourceIndexEq : sourceItemIndex =
          ⟨keptPosition.val,
            ItemSeq.focusAt?_index_lt _ _ sourceFocus sourceAt⟩ := by
        apply Fin.ext
        rfl
      obtain ⟨targetFocus, targetAt, targetGet⟩ :=
        ItemSeq.focusAt?_complete leaf.items targetItemIndex
      have targetItemEq : targetFocus.item = sourceFocus.item := by
        have sourceGet := ItemSeq.focusAt?_item _ _ sourceFocus sourceAt
        have mapped := itemEq sourceItemIndex
        rw [itemPositionMap, ← targetGet] at mapped
        rw [sourceIndexEq] at mapped
        rw [← sourceGet] at mapped
        exact mapped
      have targetIsBubble : targetFocus.item = .bubble _ _ :=
        targetItemEq.trans (by simpa [sourceFocus] using isBubble)
      obtain ⟨child, childPath, childWire⟩ := nested.identityAlignment
      let targetWitness : Region.ContextPath (Region.mk 0 leaf.items)
          (fullPosition.val :: child.targetPath) :=
        .bubble targetFocus targetAt targetIsBubble child.targetWitness
      let holeRelsEq : targetWitness.toFocus.holeRels =
          nested.toFocus.holeRels := by
        simpa [targetWitness, Region.ContextPath.toFocus] using
          child.holeRelsEq
      let frame : ItemSeqIso.Frame
          (extendWireEquiv
            (FiniteEquiv.refl
              (Fin (leaf.inheritedWires.extend anchor).length))
            (FiniteEquiv.refl (Fin 0)))
          ⟨keptPosition.val,
            ItemSeq.focusAt?_index_lt _ _ sourceFocus sourceAt⟩
          targetItemIndex := by
        apply ItemSeqIso.Frame.castWire extendedRefl.symm
        exact {
          positions := itemPositions
          mapped := by simpa [sourceIndexEq] using itemPositionMap
          siblings := fun sibling _ => itemIsos sibling
        }
      let alignment : RegionIso.ContextPathAlignment iso
          (Region.ContextPath.bubble sourceFocus sourceAt isBubble nested) := {
        targetPath := fullPosition.val :: child.targetPath
        targetWitness := targetWitness
        holeRelsEq := holeRelsEq
        holeWire := child.holeWire
        context := by
          have childContext : DiagramContextIso signature
              (extendWireEquiv
                (FiniteEquiv.refl
                  (Fin (leaf.inheritedWires.extend anchor).length))
                (FiniteEquiv.refl (Fin 0))) child.holeWire (_ :: rels)
              nested.toFocus.holeRels nested.toFocus.context
              (child.holeRelsEq ▸
                child.targetWitness.toFocus.context) := by
            rw [extendedRefl]
            exact child.context
          have layer := DiagramContextIso.bubbleFrame
            (FiniteEquiv.refl (Fin 0))
            sourceFocus targetFocus sourceAt targetAt frame
            nested.toFocus.context
            (child.holeRelsEq ▸ child.targetWitness.toFocus.context)
            childContext
          have proofEq : holeRelsEq = child.holeRelsEq :=
            Subsingleton.elim _ _
          rw [proofEq]
          change DiagramContextIso signature _ child.holeWire rels
            nested.toFocus.holeRels
            (DiagramContext.bubble 0 sourceFocus.before sourceFocus.after _
              nested.toFocus.context)
            (child.holeRelsEq ▸ DiagramContext.bubble 0
              targetFocus.before targetFocus.after _
              child.targetWitness.toFocus.context)
          rw [DiagramContext.castHoleRels_bubble]
          exact layer
        body := by
          simpa [targetWitness, Region.ContextPath.toFocus] using child.body
      }
      refine ⟨iso, alignment, ?_, ?_⟩
      · simp only [alignment]
        rw [childPath]
      · intro index
        exact childWire index

/-- A compiler leaf factors along any proved partition of its direct
occurrences.  This is the diagram-generic kernel behind selection factoring. -/
theorem compilerLeaf_partition_of_perm
    {signature : List Nat}
    (input : CheckedDiagram signature)
    (anchor : Fin input.val.regionCount)
    {outer : Nat} {rels : RelCtx}
    {body : Region signature outer rels}
    (leaf : VisualProof.Diagram.Splice.Region.ContextPath.CompilerLeaf
      input.val anchor (.here body))
    (kept selected : List (ConcreteElaboration.LocalOccurrence
      input.val.regionCount input.val.nodeCount))
    (partition : (kept ++ selected).Perm
      (ConcreteElaboration.localOccurrences input.val anchor)) :
    ∃ (keptItems selectedItems : ItemSeq signature
        (leaf.inheritedWires.extend anchor).length rels),
      ConcreteElaboration.compileOccurrencesWith? signature input.val
          (ConcreteElaboration.compileRegion? signature input.val leaf.fuel)
          (leaf.inheritedWires.extend anchor) leaf.binders kept =
            some keptItems ∧
        ConcreteElaboration.compileOccurrencesWith? signature input.val
          (ConcreteElaboration.compileRegion? signature input.val leaf.fuel)
          (leaf.inheritedWires.extend anchor) leaf.binders selected =
            some selectedItems ∧
        ∀ (model : Lambda.LambdaModel)
          (named : NamedEnv model.Carrier signature)
          (env : Fin (leaf.inheritedWires.extend anchor).length →
            model.Carrier)
          (relEnv : RelEnv model.Carrier rels),
          denoteItemSeq model named env relEnv leaf.items ↔
            denoteItemSeq model named env relEnv
              (keptItems.append selectedItems) := by
  let recurse : ∀ {rels : RelCtx},
      (region : Fin input.val.regionCount) →
      (context : ConcreteElaboration.WireContext input.val) →
      ConcreteElaboration.BinderContext input.val rels →
      Option (Region signature context.length rels) :=
    fun {rels} => ConcreteElaboration.compileRegion? signature input.val
      leaf.fuel
  have allCompiled :
      ConcreteElaboration.compileOccurrencesWith? signature input.val recurse
          (leaf.inheritedWires.extend anchor) leaf.binders
          (ConcreteElaboration.localOccurrences input.val anchor) =
            some leaf.items := by
    simpa [recurse] using leaf.itemsComputation
  have eachPartitioned : ∀ occurrence,
      occurrence ∈ kept ++ selected →
      ∃ item,
        ConcreteElaboration.compileOccurrenceWith? signature input.val recurse
          (leaf.inheritedWires.extend anchor) leaf.binders occurrence =
            some item := by
    intro occurrence member
    apply compileOccurrence_success_of_mem input.val recurse
      (leaf.inheritedWires.extend anchor) leaf.binders allCompiled
    exact partition.mem_iff.mp member
  obtain ⟨partitionItems, partitionCompiled⟩ :=
    ConcreteElaboration.compileOccurrencesWith?_complete recurse
      (leaf.inheritedWires.extend anchor) leaf.binders (kept ++ selected)
      eachPartitioned
  obtain ⟨keptItems, selectedItems, keptCompiled, selectedCompiled,
      partitionEq⟩ :=
    ConcreteElaboration.compileOccurrencesWith?_append_split recurse
      (leaf.inheritedWires.extend anchor) leaf.binders kept selected
      partitionItems partitionCompiled
  refine ⟨keptItems, selectedItems, ?_, ?_, ?_⟩
  · simpa [recurse] using keptCompiled
  · simpa [recurse] using selectedCompiled
  · intro model named env relEnv
    have permuted := compileOccurrences_denote_perm input.val recurse
      (leaf.inheritedWires.extend anchor) leaf.binders partition.symm
      allCompiled partitionCompiled model named env relEnv
    rw [partitionEq] at permuted
    exact permuted

/-- The compiler items at a selection anchor split into the unselected and
selected occurrence blocks.  This is a semantic partition, not a second
elaboration: both blocks are compiled by the same recursive compiler, wire
context, binder context, and fuel retained by the authoritative leaf. -/
theorem compilerLeaf_selection_partition
    {signature : List Nat}
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    {outer : Nat} {rels : RelCtx}
    {body : Region signature outer rels}
    (leaf : VisualProof.Diagram.Splice.Region.ContextPath.CompilerLeaf
      input.val selection.val.anchor (.here body)) :
    ∃ (keptItems selectedItems : ItemSeq signature
        (leaf.inheritedWires.extend selection.val.anchor).length rels),
      ConcreteElaboration.compileOccurrencesWith? signature input.val
          (ConcreteElaboration.compileRegion? signature input.val leaf.fuel)
          (leaf.inheritedWires.extend selection.val.anchor) leaf.binders
          (keptOccurrences input.val selection) = some keptItems ∧
        ConcreteElaboration.compileOccurrencesWith? signature input.val
          (ConcreteElaboration.compileRegion? signature input.val leaf.fuel)
          (leaf.inheritedWires.extend selection.val.anchor) leaf.binders
          (selectedOccurrences input.val selection) = some selectedItems ∧
        ∀ (model : Lambda.LambdaModel)
          (named : NamedEnv model.Carrier signature)
          (env : Fin (leaf.inheritedWires.extend
            selection.val.anchor).length → model.Carrier)
          (relEnv : RelEnv model.Carrier rels),
          denoteItemSeq model named env relEnv leaf.items ↔
          denoteItemSeq model named env relEnv
              (keptItems.append selectedItems) :=
  compilerLeaf_partition_of_perm input selection.val.anchor leaf
    (keptOccurrences input.val selection)
    (selectedOccurrences input.val selection)
    (anchorOccurrences_perm_partition input.val selection)

end VisualProof.Rule.IterationSoundness
