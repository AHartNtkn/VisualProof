import VisualProof.Concrete.Subgraph.Splice.Trace
import VisualProof.Diagram.ContextPathIsomorphism

namespace VisualProof.Refinement.Implementation.IterationPartition

open VisualProof
open VisualProof.Concrete
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

def occurrenceSelected (selection : CheckedSelection input) :
    Concrete.Elaboration.LocalOccurrence input.regionCount input.nodeCount →
      Bool
  | .node node => decide (node ∈ selection.val.directNodes)
  | .child child => decide (child ∈ selection.val.childRoots)

def selectedOccurrences
    (input : Concrete.Diagram) (selection : CheckedSelection input) :
    List (Concrete.Elaboration.LocalOccurrence input.regionCount
      input.nodeCount) :=
  (Concrete.Elaboration.localOccurrences input selection.val.anchor).filter
    (occurrenceSelected selection)

def keptOccurrences
    (input : Concrete.Diagram) (selection : CheckedSelection input) :
    List (Concrete.Elaboration.LocalOccurrence input.regionCount
      input.nodeCount) :=
  (Concrete.Elaboration.localOccurrences input selection.val.anchor).filter
    (fun occurrence => !(occurrenceSelected selection occurrence))

theorem occurrences_perm
    (input : Concrete.Diagram) (selection : CheckedSelection input) :
    List.Perm
      (selectedOccurrences input selection ++ keptOccurrences input selection)
      (Concrete.Elaboration.localOccurrences input selection.val.anchor) := by
  simpa only [selectedOccurrences, keptOccurrences, Bool.not_not] using
    (List.filter_append_perm
      (occurrenceSelected selection)
      (Concrete.Elaboration.localOccurrences input selection.val.anchor))

theorem compileOccurrence_success_of_mem
    (diagram : Concrete.Diagram)
    (recurse : ∀ {rels : RelCtx},
      (region : Fin diagram.regionCount) →
      (context : Concrete.Elaboration.WireContext diagram) →
      Concrete.Elaboration.BinderContext diagram rels →
      Option (Region context.length rels))
    (context : Concrete.Elaboration.WireContext diagram)
    (binders : Concrete.Elaboration.BinderContext diagram rels)
    {occurrences : List
      (Concrete.Elaboration.LocalOccurrence diagram.regionCount
        diagram.nodeCount)}
    {items : ItemSeq context.length rels}
    (compiled :
      Concrete.Elaboration.compileOccurrencesWith? diagram recurse
        context binders occurrences = some items)
    {occurrence} (member : occurrence ∈ occurrences) :
    ∃ item,
      Concrete.Elaboration.compileOccurrenceWith? diagram recurse
        context binders occurrence = some item := by
  induction occurrences generalizing items with
  | nil => simp at member
  | cons head tail induction =>
      simp only [Concrete.Elaboration.compileOccurrencesWith?] at compiled
      cases headResult : Concrete.Elaboration.compileOccurrenceWith?
          diagram recurse context binders head with
      | none => simp [headResult] at compiled
      | some headItem =>
          cases tailResult : Concrete.Elaboration.compileOccurrencesWith?
              diagram recurse context binders tail with
          | none => simp [headResult, tailResult] at compiled
          | some tailItems =>
              simp [headResult, tailResult] at compiled
              subst items
              rcases List.mem_cons.mp member with rfl | member
              · exact ⟨headItem, headResult⟩
              · exact induction tailResult member

theorem compileOccurrences_append
    (diagram : Concrete.Diagram)
    (recurse : ∀ {rels : RelCtx},
      (region : Fin diagram.regionCount) →
      (context : Concrete.Elaboration.WireContext diagram) →
      Concrete.Elaboration.BinderContext diagram rels →
      Option (Region context.length rels))
    (context : Concrete.Elaboration.WireContext diagram)
    (binders : Concrete.Elaboration.BinderContext diagram rels)
    (first second : List (Concrete.Elaboration.LocalOccurrence
      diagram.regionCount diagram.nodeCount))
    {firstItems secondItems : ItemSeq context.length rels}
    (firstCompiled :
      Concrete.Elaboration.compileOccurrencesWith? diagram recurse
        context binders first = some firstItems)
    (secondCompiled :
      Concrete.Elaboration.compileOccurrencesWith? diagram recurse
        context binders second = some secondItems) :
    Concrete.Elaboration.compileOccurrencesWith? diagram recurse
        context binders (first ++ second) =
      some (firstItems.append secondItems) := by
  induction first generalizing firstItems with
  | nil =>
      simp only [Concrete.Elaboration.compileOccurrencesWith?] at firstCompiled
      cases firstCompiled
      simpa using secondCompiled
  | cons head tail induction =>
      simp only [Concrete.Elaboration.compileOccurrencesWith?] at firstCompiled ⊢
      cases headResult : Concrete.Elaboration.compileOccurrenceWith?
          diagram recurse context binders head with
      | none => simp [headResult] at firstCompiled
      | some headItem =>
          cases tailResult : Concrete.Elaboration.compileOccurrencesWith?
              diagram recurse context binders tail with
          | none => simp [headResult, tailResult] at firstCompiled
          | some tailItems =>
              simp [headResult, tailResult] at firstCompiled
              subst firstItems
              simp [Concrete.Elaboration.compileOccurrencesWith?, headResult,
                induction tailResult]
              rfl

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

noncomputable def compileOccurrences_perm_iso
    (diagram : Concrete.Diagram)
    (recurse : ∀ {rels : RelCtx},
      (region : Fin diagram.regionCount) →
      (context : Concrete.Elaboration.WireContext diagram) →
      Concrete.Elaboration.BinderContext diagram rels →
      Option (Region context.length rels))
    (context : Concrete.Elaboration.WireContext diagram)
    (binders : Concrete.Elaboration.BinderContext diagram rels)
    {sourceOccurrences targetOccurrences : List
      (Concrete.Elaboration.LocalOccurrence diagram.regionCount
        diagram.nodeCount)}
    (permutation : sourceOccurrences.Perm targetOccurrences)
    (sourceNodup : sourceOccurrences.Nodup)
    (targetNodup : targetOccurrences.Nodup)
    {sourceItems targetItems : ItemSeq context.length rels}
    (sourceCompiled :
      Concrete.Elaboration.compileOccurrencesWith? diagram recurse
        context binders sourceOccurrences = some sourceItems)
    (targetCompiled :
      Concrete.Elaboration.compileOccurrencesWith? diagram recurse
        context binders targetOccurrences = some targetItems) :
    ItemSeqIso (FiniteEquiv.refl (Fin context.length)) rels
      sourceItems targetItems := by
  let positions := permIndexEquiv sourceOccurrences targetOccurrences
    permutation sourceNodup targetNodup
  have sourceLength := Concrete.Elaboration.compileOccurrencesWith?_length
    recurse context binders sourceCompiled
  have targetLength := Concrete.Elaboration.compileOccurrencesWith?_length
    recurse context binders targetCompiled
  let itemPositions := (FiniteEquiv.finCast sourceLength).trans
    (positions.trans (FiniteEquiv.finCast targetLength.symm))
  refine ItemSeqIso.permute itemPositions ?_
  intro sourceIndex
  let occurrenceIndex := Fin.cast sourceLength sourceIndex
  have sourceGet := Concrete.Elaboration.compileOccurrencesWith?_get recurse
    context binders sourceCompiled occurrenceIndex
  have targetGet := Concrete.Elaboration.compileOccurrencesWith?_get recurse
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

structure PartitionResult
    (input : Concrete.Checked)
    (anchor : Fin input.val.regionCount)
    {outer : Nat} {rels : RelCtx}
    {body : Region outer rels}
    (leaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      anchor (.here body))
    (selected kept : List (Concrete.Elaboration.LocalOccurrence
      input.val.regionCount input.val.nodeCount)) where
  selectedItems : ItemSeq (leaf.inheritedWires.extend anchor).length rels
  keptItems : ItemSeq (leaf.inheritedWires.extend anchor).length rels
  selectedCompiled :
    Concrete.Elaboration.compileOccurrencesWith? input.val
        (Concrete.Elaboration.compileRegion? input.val leaf.fuel)
        (leaf.inheritedWires.extend anchor) leaf.binders selected =
      some selectedItems
  keptCompiled :
    Concrete.Elaboration.compileOccurrencesWith? input.val
        (Concrete.Elaboration.compileRegion? input.val leaf.fuel)
        (leaf.inheritedWires.extend anchor) leaf.binders kept =
      some keptItems
  iso : RegionIso
    (FiniteEquiv.refl (Fin (leaf.inheritedWires.extend anchor).length))
    rels (Region.mk 0 (selectedItems.append keptItems)) (Region.mk 0 leaf.items)

noncomputable def partition_complete_of_perm
    (input : Concrete.Checked)
    (anchor : Fin input.val.regionCount)
    {outer : Nat} {rels : RelCtx}
    {body : Region outer rels}
    (leaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      anchor (.here body))
    (selected kept : List (Concrete.Elaboration.LocalOccurrence
      input.val.regionCount input.val.nodeCount))
    (partition : (selected ++ kept).Perm
      (Concrete.Elaboration.localOccurrences input.val anchor)) :
    PartitionResult input anchor leaf selected kept := by
  let recurse : ∀ {rels : RelCtx},
      (region : Fin input.val.regionCount) →
      (context : Concrete.Elaboration.WireContext input.val) →
      Concrete.Elaboration.BinderContext input.val rels →
      Option (Region context.length rels) :=
    fun {rels} => Concrete.Elaboration.compileRegion? input.val leaf.fuel
  have allCompiled :
      Concrete.Elaboration.compileOccurrencesWith? input.val recurse
          (leaf.inheritedWires.extend anchor) leaf.binders
          (Concrete.Elaboration.localOccurrences input.val anchor) =
        some leaf.items := by
    simpa [recurse] using leaf.itemsComputation
  let partitioned := selected ++ kept
  have eachCompiled : ∀ occurrence, occurrence ∈ partitioned →
      ∃ item, Concrete.Elaboration.compileOccurrenceWith? input.val recurse
        (leaf.inheritedWires.extend anchor) leaf.binders occurrence =
          some item := by
    intro occurrence member
    exact compileOccurrence_success_of_mem input.val recurse
      (leaf.inheritedWires.extend anchor) leaf.binders allCompiled
      (partition.mem_iff.mp member)
  have selectedEach : ∀ occurrence, occurrence ∈ selected →
      ∃ item, Concrete.Elaboration.compileOccurrenceWith? input.val recurse
        (leaf.inheritedWires.extend anchor) leaf.binders occurrence = some item :=
    fun occurrence member => eachCompiled occurrence
      (List.mem_append_left kept member)
  have keptEach : ∀ occurrence, occurrence ∈ kept →
      ∃ item, Concrete.Elaboration.compileOccurrenceWith? input.val recurse
        (leaf.inheritedWires.extend anchor) leaf.binders occurrence = some item :=
    fun occurrence member => eachCompiled occurrence
      (List.mem_append_right selected member)
  cases selectedResult : Concrete.Elaboration.compileOccurrencesWith? input.val
      recurse (leaf.inheritedWires.extend anchor) leaf.binders selected with
  | none =>
      have impossible : False := by
        obtain ⟨items, compiled⟩ :=
          Concrete.Elaboration.compileOccurrencesWith?_complete recurse
            (leaf.inheritedWires.extend anchor) leaf.binders selected selectedEach
        rw [selectedResult] at compiled
        contradiction
      exact impossible.elim
  | some selectedItems =>
    cases keptResult : Concrete.Elaboration.compileOccurrencesWith? input.val
        recurse (leaf.inheritedWires.extend anchor) leaf.binders kept with
    | none =>
      have impossible : False := by
        obtain ⟨items, compiled⟩ :=
          Concrete.Elaboration.compileOccurrencesWith?_complete recurse
            (leaf.inheritedWires.extend anchor) leaf.binders kept keptEach
        rw [keptResult] at compiled
        contradiction
      exact impossible.elim
    | some keptItems =>
      have combinedCompiled :
          Concrete.Elaboration.compileOccurrencesWith? input.val recurse
              (leaf.inheritedWires.extend anchor) leaf.binders partitioned =
            some (selectedItems.append keptItems) := by
        simpa [partitioned] using compileOccurrences_append input.val recurse
          (leaf.inheritedWires.extend anchor) leaf.binders selected kept
          selectedResult keptResult
      have partitionNodup : partitioned.Nodup :=
        (partition.nodup_iff).2
          (Concrete.Elaboration.localOccurrences_nodup input.val anchor)
      have itemIso := compileOccurrences_perm_iso input.val recurse
        (leaf.inheritedWires.extend anchor) leaf.binders partition partitionNodup
        (Concrete.Elaboration.localOccurrences_nodup input.val anchor)
        combinedCompiled allCompiled
      refine ⟨selectedItems, keptItems,
        by simpa [recurse] using selectedResult,
        by simpa [recurse] using keptResult, ?_⟩
      apply RegionIso.mk (FiniteEquiv.refl (Fin 0))
      have extendedRefl :
          extendWireEquiv
              (FiniteEquiv.refl (Fin (leaf.inheritedWires.extend anchor).length))
              (FiniteEquiv.refl (Fin 0)) =
            FiniteEquiv.refl
              (Fin ((leaf.inheritedWires.extend anchor).length + 0)) := by
        apply FiniteEquiv.ext
        intro wire
        refine Fin.addCases (fun index => ?_) (fun index => ?_) wire
        · simp only [extendWireEquiv_outer, FiniteEquiv.refl_apply]
        · exact Fin.elim0 index
      rw [extendedRefl]
      simpa using itemIso

noncomputable def partition_complete
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    {outer : Nat} {rels : RelCtx}
    {body : Region outer rels}
    (leaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here body)) :
    PartitionResult input selection.val.anchor leaf
      (selectedOccurrences input.val selection)
      (keptOccurrences input.val selection) := by
  exact partition_complete_of_perm input selection.val.anchor leaf
    (selectedOccurrences input.val selection)
    (keptOccurrences input.val selection) (occurrences_perm input.val selection)

end VisualProof.Refinement.Implementation.IterationPartition
