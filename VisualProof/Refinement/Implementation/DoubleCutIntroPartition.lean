import VisualProof.Refinement.Implementation.DoubleCutTransport
import VisualProof.Refinement.Implementation.IterationPartition

namespace VisualProof.Refinement.Implementation.DoubleCutIntroPartition

open VisualProof
open VisualProof.Concrete
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory
open VisualProof.Refinement.Implementation.DoubleCutTransport

def liftOccurrence (input : Concrete.Diagram) :
    Concrete.Elaboration.LocalOccurrence input.regionCount input.nodeCount →
      Concrete.Elaboration.LocalOccurrence (input.regionCount + 2)
        input.nodeCount
  | .node node => .node node
  | .child child => .child (Fin.castAdd 2 child)

def occurrenceSelected (selection : CheckedSelection input) :
    Concrete.Elaboration.LocalOccurrence input.regionCount input.nodeCount → Bool
  | .node node => decide (node ∈ selection.val.directNodes)
  | .child child => decide (child ∈ selection.val.childRoots)

def selectedOccurrences (input : Concrete.Diagram)
    (selection : CheckedSelection input) :=
  (Concrete.Elaboration.localOccurrences input selection.val.anchor).filter
    (occurrenceSelected selection)

def keptOccurrences (input : Concrete.Diagram)
    (selection : CheckedSelection input) :=
  (Concrete.Elaboration.localOccurrences input selection.val.anchor).filter
    (fun occurrence => !(occurrenceSelected selection occurrence))

private def canonicalSelectedOccurrences
    (input : Concrete.Diagram) (selection : CheckedSelection input) :
    List (Concrete.Elaboration.LocalOccurrence input.regionCount
      input.nodeCount) :=
  (filterFin fun node =>
      decide (node ∈ selection.val.directNodes)).map
        Concrete.Elaboration.LocalOccurrence.node ++
    (filterFin fun child =>
      decide (child ∈ selection.val.childRoots)).map
        Concrete.Elaboration.LocalOccurrence.child

private def canonicalKeptOccurrences
    (input : Concrete.Diagram) (selection : CheckedSelection input) :
    List (Concrete.Elaboration.LocalOccurrence input.regionCount
      input.nodeCount) :=
  (filterFin fun node => decide
      ((input.nodes node).region = selection.val.anchor ∧
        node ∉ selection.val.directNodes)).map
      Concrete.Elaboration.LocalOccurrence.node ++
    (filterFin fun child => decide
      ((input.regions child).parent? = some selection.val.anchor ∧
        child ∉ selection.val.childRoots)).map
      Concrete.Elaboration.LocalOccurrence.child

private theorem keptOccurrences_eq_canonical
    (input : Concrete.Diagram) (selection : CheckedSelection input) :
    keptOccurrences input selection =
      canonicalKeptOccurrences input selection := by
  unfold keptOccurrences canonicalKeptOccurrences
    Concrete.Elaboration.localOccurrences occurrenceSelected filterFin
  simp only [List.filter_append, List.filter_map, List.filter_filter]
  congr 1
  · apply congrArg
      (List.map Concrete.Elaboration.LocalOccurrence.node)
    apply congrArg
      (fun predicate => List.filter predicate (allFin input.nodeCount))
    funext node
    apply Bool.eq_iff_iff.mpr
    simp [and_comm]
  · apply congrArg
      (List.map Concrete.Elaboration.LocalOccurrence.child)
    apply congrArg
      (fun predicate => List.filter predicate (allFin input.regionCount))
    funext child
    apply Bool.eq_iff_iff.mpr
    simp [and_comm]

private theorem selectedOccurrences_eq_canonical
    (input : Concrete.Diagram) (selection : CheckedSelection input) :
    selectedOccurrences input selection =
      canonicalSelectedOccurrences input selection := by
  unfold selectedOccurrences canonicalSelectedOccurrences
    Concrete.Elaboration.localOccurrences occurrenceSelected filterFin
  simp only [List.filter_append, List.filter_map, List.filter_filter]
  congr 1
  · apply congrArg
      (List.map Concrete.Elaboration.LocalOccurrence.node)
    apply congrArg
      (fun predicate => List.filter predicate (allFin input.nodeCount))
    funext node
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply, Bool.and_eq_true,
      decide_eq_true_eq]
    constructor
    · exact And.left
    · intro selected
      exact ⟨selected,
        selection.property.directNodes_at_anchor node selected⟩
  · apply congrArg
      (List.map Concrete.Elaboration.LocalOccurrence.child)
    apply congrArg
      (fun predicate => List.filter predicate (allFin input.regionCount))
    funext child
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply, Bool.and_eq_true,
      decide_eq_true_eq]
    constructor
    · exact And.left
    · intro selected
      exact ⟨selected,
        selection.property.childRoots_direct child selected⟩

theorem inner_localOccurrences
    (input : Concrete.Diagram) (selection : CheckedSelection input) :
    Concrete.Elaboration.localOccurrences
        (doubleCutIntroRaw input selection) (inner input) =
      (selectedOccurrences input selection).map (liftOccurrence input) := by
  rw [selectedOccurrences_eq_canonical]
  unfold Concrete.Elaboration.localOccurrences canonicalSelectedOccurrences
    filterFin
  simp only [nodeCount, regionCount, List.map_append, List.map_map]
  rw [allFin_add input.regionCount 2, List.filter_append,
    List.filter_map]
  simp only [List.map_append, List.map_map]
  have liftNode :
      (liftOccurrence input ∘ Concrete.Elaboration.LocalOccurrence.node) =
        Concrete.Elaboration.LocalOccurrence.node := by
    funext node
    rfl
  have liftChild :
      (liftOccurrence input ∘ Concrete.Elaboration.LocalOccurrence.child) =
        (Concrete.Elaboration.LocalOccurrence.child ∘ Fin.castAdd 2) := by
    funext child
    rfl
  rw [liftNode, liftChild]
  congr 1
  · apply congrArg
      (List.map Concrete.Elaboration.LocalOccurrence.node)
    apply congrArg
      (fun predicate => List.filter predicate (allFin input.nodeCount))
    funext node
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    by_cases selected : node ∈ selection.val.directNodes
    · have regionEq := node_region input selection node
      rw [if_pos selected] at regionEq
      exact ⟨fun _ => selected, fun _ => regionEq⟩
    · have regionEq := node_region input selection node
      rw [if_neg selected] at regionEq
      constructor
      · intro equality
        exact False.elim (inner_ne_lift input
          (input.nodes node).region (equality.symm.trans regionEq))
      · intro impossible
        exact False.elim (selected impossible)
  · let newRegions : List (Fin (input.regionCount + 2)) :=
      List.filter
        (fun child => decide
          (((doubleCutIntroRaw input selection).regions child).parent? =
            some (inner input)))
        (List.map (Fin.natAdd input.regionCount) (allFin 2))
    have newChildRegions : newRegions = [] := by
      unfold newRegions
      apply List.filter_eq_nil_iff.mpr
      intro added member selected
      obtain ⟨small, _, rfl⟩ := List.mem_map.mp member
      have parent := decide_eq_true_eq.mp selected
      have smallCases : small = 0 ∨ small = 1 := by
        by_cases zero : small.val = 0
        · left
          apply Fin.ext
          exact zero
        · right
          apply Fin.ext
          omega
      rcases smallCases with zero | one
      · subst small
        have indexEq : Fin.natAdd input.regionCount (0 : Fin 2) =
            outer input := by
          apply Fin.ext
          rfl
        rw [indexEq, outer_parent] at parent
        exact inner_ne_lift input selection.val.anchor
          (Option.some.inj parent).symm
      · subst small
        have indexEq : Fin.natAdd input.regionCount (1 : Fin 2) =
            inner input := by
          apply Fin.ext
          rfl
        rw [indexEq, inner_parent] at parent
        exact outer_ne_inner input (Option.some.inj parent)
    change _ ++
      List.map
        (Concrete.Elaboration.LocalOccurrence.child
          (nodes := input.nodeCount)) newRegions = _
    simp only [newChildRegions, List.map_nil]
    have oldRegionsEq :
        List.filter
            ((fun child =>
              decide (((doubleCutIntroRaw input selection).regions child).parent? =
                some (inner input))) ∘ Fin.castAdd 2)
            (allFin input.regionCount) =
          List.filter (fun child =>
            decide (child ∈ selection.val.childRoots))
            (allFin input.regionCount) := by
      apply congrArg
        (fun predicate => List.filter predicate (allFin input.regionCount))
      funext child
      apply Bool.eq_iff_iff.mpr
      simp only [Function.comp_apply, decide_eq_true_eq]
      have parentEq := oldRegion_parent input selection child
      by_cases selected : child ∈ selection.val.childRoots
      · rw [if_pos selected] at parentEq
        exact ⟨fun _ => selected, fun _ => parentEq⟩
      · rw [if_neg selected] at parentEq
        constructor
        · intro targetParent
          rw [parentEq] at targetParent
          cases oldParent : (input.regions child).parent? with
          | none => simp [oldParent] at targetParent
          | some parent =>
              simp [oldParent] at targetParent
              exact False.elim (inner_ne_lift input parent
                targetParent.symm)
        · intro impossible
          exact False.elim (selected impossible)
    have oldMappedEq := congrArg
      (List.map
        (fun child =>
          Concrete.Elaboration.LocalOccurrence.child
            (nodes := input.nodeCount) (Fin.castAdd 2 child)))
      oldRegionsEq
    exact (List.append_nil _).trans oldMappedEq

theorem outer_localOccurrences
    (input : Concrete.Diagram) (selection : CheckedSelection input) :
    Concrete.Elaboration.localOccurrences
        (doubleCutIntroRaw input selection) (outer input) =
      [Concrete.Elaboration.LocalOccurrence.child (inner input)] := by
  unfold Concrete.Elaboration.localOccurrences filterFin
  simp only [nodeCount, regionCount]
  rw [allFin_add input.regionCount 2, List.filter_append,
    List.map_append]
  let nodeRegions :
      List (Fin (doubleCutIntroRaw input selection).nodeCount) :=
    List.filter
      (fun node => decide
        (((doubleCutIntroRaw input selection).nodes node).region = outer input))
      (allFin input.nodeCount)
  have noNodes : nodeRegions = [] := by
    unfold nodeRegions
    apply List.filter_eq_nil_iff.mpr
    intro node _ selected
    have owner := decide_eq_true_eq.mp selected
    have ownerEq := node_region input selection node
    split at ownerEq
    · exact outer_ne_inner input (owner.symm.trans ownerEq)
    · exact outer_ne_lift input (input.nodes node).region
        (owner.symm.trans ownerEq)
  change List.map Concrete.Elaboration.LocalOccurrence.node nodeRegions ++ _ = _
  simp only [noNodes, List.map_nil, List.nil_append]
  let oldRegions : List (Fin input.regionCount) :=
    List.filter
      ((fun child => decide
        (((doubleCutIntroRaw input selection).regions child).parent? =
          some (outer input))) ∘ Fin.castAdd 2)
      (allFin input.regionCount)
  have noOldChildren : oldRegions = [] := by
    unfold oldRegions
    apply List.filter_eq_nil_iff.mpr
    intro child _ selected
    have parent := decide_eq_true_eq.mp selected
    have parentEq := oldRegion_parent input selection child
    by_cases chosen : child ∈ selection.val.childRoots
    · rw [if_pos chosen] at parentEq
      rw [parentEq] at parent
      exact outer_ne_inner input (Option.some.inj parent).symm
    · rw [if_neg chosen] at parentEq
      rw [parentEq] at parent
      cases oldParent : (input.regions child).parent? with
      | none => simp [oldParent] at parent
      | some old =>
          simp [oldParent] at parent
          exact outer_ne_lift input old parent.symm
  rw [List.filter_map]
  change List.map Concrete.Elaboration.LocalOccurrence.child
      (List.map (Fin.castAdd 2) oldRegions) ++ _ = _
  simp only [noOldChildren, List.map_nil, List.nil_append]
  change List.map Concrete.Elaboration.LocalOccurrence.child
      (List.filter _ (List.map (Fin.natAdd input.regionCount) (allFin 2))) = [_]
  have addedFilter :
      List.filter
          (fun child => decide
            (((doubleCutIntroRaw input selection).regions child).parent? =
              some (outer input)))
          (List.map (Fin.natAdd input.regionCount) (allFin 2)) =
        [inner input] := by
    rw [show allFin 2 = [(0 : Fin 2), (1 : Fin 2)] by decide]
    simp only [List.map_cons, List.map_nil, List.filter_cons, List.filter_nil]
    have outerIndex : Fin.natAdd input.regionCount (0 : Fin 2) =
        outer input := by
      apply Fin.ext
      rfl
    have innerIndex : Fin.natAdd input.regionCount (1 : Fin 2) =
        inner input := by
      apply Fin.ext
      rfl
    rw [outerIndex, innerIndex]
    have outerNotParent :
        ¬((doubleCutIntroRaw input selection).regions
            (outer input)).parent? = some (outer input) := by
      rw [outer_parent]
      intro equality
      exact outer_ne_lift input selection.val.anchor
        (Option.some.inj equality).symm
    have innerIsParent :
        ((doubleCutIntroRaw input selection).regions
            (inner input)).parent? = some (outer input) :=
      inner_parent input selection
    rw [decide_eq_false outerNotParent, decide_eq_true innerIsParent]
    rfl
  have mappedAdded := congrArg
    (List.map
      (Concrete.Elaboration.LocalOccurrence.child
        (nodes := input.nodeCount)))
    addedFilter
  simpa only [List.map_cons, List.map_nil] using mappedAdded

theorem anchor_localOccurrences
    (input : Concrete.Diagram) (selection : CheckedSelection input) :
    Concrete.Elaboration.localOccurrences
        (doubleCutIntroRaw input selection)
        (Fin.castAdd 2 selection.val.anchor) =
      (keptOccurrences input selection).map (liftOccurrence input) ++
        [Concrete.Elaboration.LocalOccurrence.child (outer input)] := by
  rw [keptOccurrences_eq_canonical]
  unfold Concrete.Elaboration.localOccurrences canonicalKeptOccurrences filterFin
  simp only [nodeCount, regionCount, List.map_append, List.map_map]
  rw [allFin_add input.regionCount 2, List.filter_append,
    List.filter_map, List.map_append]
  have liftNode :
      (liftOccurrence input ∘ Concrete.Elaboration.LocalOccurrence.node) =
        Concrete.Elaboration.LocalOccurrence.node := by
    funext node
    rfl
  have liftChild :
      (liftOccurrence input ∘ Concrete.Elaboration.LocalOccurrence.child) =
        (Concrete.Elaboration.LocalOccurrence.child ∘ Fin.castAdd 2) := by
    funext child
    rfl
  rw [liftNode, liftChild, List.append_assoc]
  congr 1
  · apply congrArg
      (List.map Concrete.Elaboration.LocalOccurrence.node)
    apply congrArg
      (fun predicate => List.filter predicate (allFin input.nodeCount))
    funext node
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    have ownerEq := node_region input selection node
    by_cases chosen : node ∈ selection.val.directNodes
    · constructor
      · intro owner
        have selectedOwner :
            ((doubleCutIntroRaw input selection).nodes node).region =
              inner input := by
          simpa only [if_pos chosen] using ownerEq
        exact False.elim (inner_ne_lift input selection.val.anchor
          (selectedOwner.symm.trans owner))
      · intro impossible
        exact False.elim (impossible.2 chosen)
    · have liftedOwner :
          ((doubleCutIntroRaw input selection).nodes node).region =
            Fin.castAdd 2 (input.nodes node).region := by
        simpa only [if_neg chosen] using ownerEq
      constructor
      · intro owner
        refine ⟨?_, chosen⟩
        apply Fin.ext
        exact congrArg
          (fun value : Fin (input.regionCount + 2) => value.val)
          (liftedOwner.symm.trans owner)
      · rintro ⟨owner, _⟩
        exact liftedOwner.trans (congrArg (Fin.castAdd 2) owner)
  · let newRegions :
        List (Fin (doubleCutIntroRaw input selection).regionCount) :=
      List.filter
        (fun child => decide
          (((doubleCutIntroRaw input selection).regions child).parent? =
            some (Fin.castAdd 2 selection.val.anchor)))
        (List.map (Fin.natAdd input.regionCount) (allFin 2))
    have newRegionsEq : newRegions = [outer input] := by
      unfold newRegions
      rw [show allFin 2 = [(0 : Fin 2), (1 : Fin 2)] by decide]
      simp only [List.map_cons, List.map_nil, List.filter_cons, List.filter_nil]
      have outerIndex : Fin.natAdd input.regionCount (0 : Fin 2) =
          outer input := by
        apply Fin.ext
        rfl
      have innerIndex : Fin.natAdd input.regionCount (1 : Fin 2) =
          inner input := by
        apply Fin.ext
        rfl
      rw [outerIndex, innerIndex]
      have outerParent :
          ((doubleCutIntroRaw input selection).regions
              (outer input)).parent? =
            some (Fin.castAdd 2 selection.val.anchor) :=
        outer_parent input selection
      have innerNotParent :
          ¬((doubleCutIntroRaw input selection).regions
              (inner input)).parent? =
            some (Fin.castAdd 2 selection.val.anchor) := by
        rw [inner_parent]
        intro equality
        exact outer_ne_lift input selection.val.anchor
          (Option.some.inj equality)
      rw [decide_eq_true outerParent, decide_eq_false innerNotParent]
      rfl
    have oldRegionsEq :
        List.filter
            ((fun child => decide
              (((doubleCutIntroRaw input selection).regions child).parent? =
                some (Fin.castAdd 2 selection.val.anchor))) ∘ Fin.castAdd 2)
            (allFin input.regionCount) =
          List.filter (fun child => decide
            ((input.regions child).parent? = some selection.val.anchor ∧
              child ∉ selection.val.childRoots))
            (allFin input.regionCount) := by
      apply congrArg
        (fun predicate => List.filter predicate (allFin input.regionCount))
      funext child
      apply Bool.eq_iff_iff.mpr
      simp only [Function.comp_apply, decide_eq_true_eq]
      have parentEq := oldRegion_parent input selection child
      by_cases chosen : child ∈ selection.val.childRoots
      · constructor
        · intro parent
          rw [if_pos chosen] at parentEq
          rw [parentEq] at parent
          exact False.elim (inner_ne_lift input selection.val.anchor
            (Option.some.inj parent))
        · intro impossible
          exact False.elim (impossible.2 chosen)
      · rw [if_neg chosen] at parentEq
        constructor
        · intro parent
          rw [parentEq] at parent
          cases oldParent : (input.regions child).parent? with
          | none => simp [oldParent] at parent
          | some old =>
              simp [oldParent] at parent
              refine ⟨?_, chosen⟩
              apply congrArg some
              apply Fin.ext
              exact congrArg
                (fun value : Fin (input.regionCount + 2) => value.val) parent
        · rintro ⟨parent, _⟩
          rw [parentEq, parent]
          rfl
    have oldMappedEq := congrArg
      (List.map
        (Concrete.Elaboration.LocalOccurrence.child
          (nodes := input.nodeCount) ∘ Fin.castAdd 2))
      oldRegionsEq
    have newMappedEq :
        List.map
            (Concrete.Elaboration.LocalOccurrence.child
              (regions := input.regionCount + 2) (nodes := input.nodeCount))
            (List.filter
              (fun child => decide
                (((doubleCutIntroRaw input selection).regions child).parent? =
                  some (Fin.castAdd 2 selection.val.anchor)))
              (List.map (Fin.natAdd input.regionCount) (allFin 2))) =
          [Concrete.Elaboration.LocalOccurrence.child
            (regions := input.regionCount + 2) (outer input)] := by
      change List.map
          (Concrete.Elaboration.LocalOccurrence.child
            (regions := input.regionCount + 2) (nodes := input.nodeCount))
          newRegions =
        [Concrete.Elaboration.LocalOccurrence.child
          (regions := input.regionCount + 2) (outer input)]
      rw [newRegionsEq]
      rfl
    calc
      _ =
          List.map
              (Concrete.Elaboration.LocalOccurrence.child
                (nodes := input.nodeCount) ∘ Fin.castAdd 2)
              (List.filter (fun child => decide
                ((input.regions child).parent? = some selection.val.anchor ∧
                  child ∉ selection.val.childRoots))
                (allFin input.regionCount)) ++
            List.map
              (Concrete.Elaboration.LocalOccurrence.child
                (regions := input.regionCount + 2) (nodes := input.nodeCount))
              (List.filter
                (fun child => decide
                  (((doubleCutIntroRaw input selection).regions child).parent? =
                    some (Fin.castAdd 2 selection.val.anchor)))
                (List.map (Fin.natAdd input.regionCount) (allFin 2))) := by
          simpa only [List.map_map] using
            congrArg
              (fun occurrences => occurrences ++
                List.map
                  (Concrete.Elaboration.LocalOccurrence.child
                    (regions := input.regionCount + 2)
                    (nodes := input.nodeCount))
                  (List.filter
                    (fun child => decide
                      (((doubleCutIntroRaw input selection).regions child).parent? =
                        some (Fin.castAdd 2 selection.val.anchor)))
                    (List.map (Fin.natAdd input.regionCount) (allFin 2))))
              oldMappedEq
      _ = _ := by rw [newMappedEq]

theorem occurrences_perm (input : Concrete.Diagram)
    (selection : CheckedSelection input) :
    List.Perm (keptOccurrences input selection ++
        selectedOccurrences input selection)
      (Concrete.Elaboration.localOccurrences input selection.val.anchor) := by
  simpa only [keptOccurrences, selectedOccurrences, Bool.not_not] using
    (List.filter_append_perm
      (fun occurrence => !(occurrenceSelected selection occurrence))
      (Concrete.Elaboration.localOccurrences input selection.val.anchor))

theorem selected_mem_local {occurrence}
    (member : occurrence ∈ selectedOccurrences input selection) :
    occurrence ∈ Concrete.Elaboration.localOccurrences input
      selection.val.anchor := by
  exact (List.mem_filter.mp member).1

theorem kept_mem_local {occurrence}
    (member : occurrence ∈ keptOccurrences input selection) :
    occurrence ∈ Concrete.Elaboration.localOccurrences input
      selection.val.anchor := by
  exact (List.mem_filter.mp member).1

theorem selected_node_iff (node : Fin input.nodeCount) :
    Concrete.Elaboration.LocalOccurrence.node node ∈
        selectedOccurrences input selection ↔
      node ∈ selection.val.directNodes := by
  constructor
  · intro member
    simpa [occurrenceSelected] using (List.mem_filter.mp member).2
  · intro selected
    apply List.mem_filter.mpr
    refine ⟨Concrete.Elaboration.mem_localOccurrences_node input
      selection.val.anchor node |>.2
        (selection.property.directNodes_at_anchor node selected), ?_⟩
    simpa [occurrenceSelected] using selected

theorem kept_node_iff (node : Fin input.nodeCount) :
    Concrete.Elaboration.LocalOccurrence.node node ∈
        keptOccurrences input selection ↔
      (input.nodes node).region = selection.val.anchor ∧
        node ∉ selection.val.directNodes := by
  simp [keptOccurrences, occurrenceSelected]

theorem selected_child_iff (child : Fin input.regionCount) :
    Concrete.Elaboration.LocalOccurrence.child child ∈
        selectedOccurrences input selection ↔
      child ∈ selection.val.childRoots := by
  constructor
  · intro member
    simpa [occurrenceSelected] using (List.mem_filter.mp member).2
  · intro selected
    apply List.mem_filter.mpr
    refine ⟨Concrete.Elaboration.mem_localOccurrences_child input
      selection.val.anchor child |>.2
        (selection.property.childRoots_direct child selected), ?_⟩
    simpa [occurrenceSelected] using selected

theorem kept_child_iff (child : Fin input.regionCount) :
    Concrete.Elaboration.LocalOccurrence.child child ∈
        keptOccurrences input selection ↔
      (input.regions child).parent? = some selection.val.anchor ∧
        child ∉ selection.val.childRoots := by
  simp [keptOccurrences, occurrenceSelected]

structure SourceItemsPartitionResult
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (recurse : ∀ {rels : RelCtx},
      (region : Fin input.val.regionCount) →
      (context : Concrete.Elaboration.WireContext input.val) →
      Concrete.Elaboration.BinderContext input.val rels →
      Option (Region context.length rels))
    (context : Concrete.Elaboration.WireContext input.val)
    (binders : Concrete.Elaboration.BinderContext input.val rels)
    (items : ItemSeq context.length rels) where
  kept : ItemSeq context.length rels
  selected : ItemSeq context.length rels
  keptCompiled : Concrete.Elaboration.compileOccurrencesWith? input.val recurse
      context binders (keptOccurrences input.val selection) = some kept
  selectedCompiled : Concrete.Elaboration.compileOccurrencesWith? input.val
      recurse context binders (selectedOccurrences input.val selection) =
    some selected
  iso : ItemSeqIso (FiniteEquiv.refl (Fin context.length)) rels
    (kept.append selected) items

noncomputable def source_items_partition
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    (recurse : ∀ {rels : RelCtx},
      (region : Fin input.val.regionCount) →
      (context : Concrete.Elaboration.WireContext input.val) →
      Concrete.Elaboration.BinderContext input.val rels →
      Option (Region context.length rels))
    (context : Concrete.Elaboration.WireContext input.val)
    (binders : Concrete.Elaboration.BinderContext input.val rels)
    {items : ItemSeq context.length rels}
    (compiled : Concrete.Elaboration.compileOccurrencesWith? input.val
      recurse context binders
      (Concrete.Elaboration.localOccurrences input.val selection.val.anchor) =
        some items) :
    SourceItemsPartitionResult input selection recurse context binders items := by
  let partitioned := keptOccurrences input.val selection ++
    selectedOccurrences input.val selection
  have eachCompiled : ∀ occurrence, occurrence ∈ partitioned →
      ∃ item, Concrete.Elaboration.compileOccurrenceWith? input.val recurse
        context binders occurrence = some item := by
    intro occurrence member
    exact VisualProof.Refinement.Implementation.IterationPartition.compileOccurrence_success_of_mem
      input.val recurse context binders compiled
      ((occurrences_perm input.val selection).mem_iff.mp member)
  have keptEach : ∀ occurrence,
      occurrence ∈ keptOccurrences input.val selection →
      ∃ item, Concrete.Elaboration.compileOccurrenceWith? input.val recurse
        context binders occurrence = some item :=
    fun occurrence member => eachCompiled occurrence
      (List.mem_append_left _ member)
  have selectedEach : ∀ occurrence,
      occurrence ∈ selectedOccurrences input.val selection →
      ∃ item, Concrete.Elaboration.compileOccurrenceWith? input.val recurse
        context binders occurrence = some item :=
    fun occurrence member => eachCompiled occurrence
      (List.mem_append_right _ member)
  cases keptResult : Concrete.Elaboration.compileOccurrencesWith? input.val
      recurse context binders (keptOccurrences input.val selection) with
  | none =>
      have impossible : False := by
        obtain ⟨kept, keptCompiled⟩ :=
          Concrete.Elaboration.compileOccurrencesWith?_complete recurse context
            binders (keptOccurrences input.val selection) keptEach
        rw [keptResult] at keptCompiled
        contradiction
      exact impossible.elim
  | some kept =>
    cases selectedResult : Concrete.Elaboration.compileOccurrencesWith? input.val
        recurse context binders (selectedOccurrences input.val selection) with
    | none =>
      have impossible : False := by
        obtain ⟨selected, selectedCompiled⟩ :=
          Concrete.Elaboration.compileOccurrencesWith?_complete recurse context
            binders (selectedOccurrences input.val selection) selectedEach
        rw [selectedResult] at selectedCompiled
        contradiction
      exact impossible.elim
    | some selected =>
      have combinedCompiled :
          Concrete.Elaboration.compileOccurrencesWith? input.val recurse context
              binders partitioned = some (kept.append selected) := by
        simpa [partitioned] using
          Concrete.Elaboration.compileOccurrencesWith?_append recurse context
            binders (keptOccurrences input.val selection)
            (selectedOccurrences input.val selection) kept selected keptResult
            selectedResult
      have partitionNodup : partitioned.Nodup :=
        ((occurrences_perm input.val selection).nodup_iff).2
          (Concrete.Elaboration.localOccurrences_nodup input.val
            selection.val.anchor)
      have itemIso :=
        VisualProof.Refinement.Implementation.IterationPartition.compileOccurrences_perm_iso
          input.val recurse context binders (occurrences_perm input.val selection)
          partitionNodup
          (Concrete.Elaboration.localOccurrences_nodup input.val
            selection.val.anchor)
          combinedCompiled compiled
      exact ⟨kept, selected, keptResult, selectedResult, itemIso⟩

noncomputable def source_partition
    (input : Concrete.Checked)
    (selection : CheckedSelection input.val)
    {outerWires : Nat} {rels : RelCtx}
    {body : Region outerWires rels}
    (leaf : Concrete.Splice.Region.ContextPath.CompilerLeaf input.val
      selection.val.anchor (.here body)) :
    IterationPartition.PartitionResult input selection.val.anchor leaf
      (keptOccurrences input.val selection)
      (selectedOccurrences input.val selection) := by
  exact
    VisualProof.Refinement.Implementation.IterationPartition.partition_complete_of_perm
      input selection.val.anchor leaf
      (keptOccurrences input.val selection)
      (selectedOccurrences input.val selection)
      (occurrences_perm input.val selection)

end VisualProof.Refinement.Implementation.DoubleCutIntroPartition
