import VisualProof.Concrete.Operation.Structural.Semantics
import VisualProof.Refinement.Implementation.Soundness

namespace VisualProof.Rule.ModalSoundness

open VisualProof.Concrete
open VisualProof.Refinement.Implementation

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

private theorem allFin_succ_last (n : Nat) :
    allFin (n + 1) =
      (allFin n).map (Fin.castAdd 1) ++ [Fin.last n] := by
  rw [allFin_eq_finRange, allFin_eq_finRange, List.finRange_succ_last]
  apply congrArg (fun xs : List (Fin (n + 1)) => xs ++ [Fin.last n])
  apply List.map_congr_left
  intro index _
  apply Fin.ext
  rfl

private theorem allFin_add (n m : Nat) :
    allFin (n + m) =
      (allFin n).map (Fin.castAdd m) ++
        (allFin m).map (Fin.natAdd n) := by
  induction m with
  | zero =>
      simp only [Nat.add_zero, allFin, List.map_nil, List.append_nil]
      have hfun : (Fin.castAdd 0 : Fin n → Fin (n + 0)) = id := by
        funext index
        apply Fin.ext
        rfl
      rw [hfun, List.map_id]
  | succ m ih =>
      change allFin ((n + m) + 1) = _
      rw [allFin_succ_last (n + m), ih, List.map_append,
        allFin_succ_last m, List.map_append, List.map_map,
        List.append_assoc]
      simp only [List.map_map]
      have hleft :
          (Fin.castAdd 1 ∘ Fin.castAdd m : Fin n → Fin ((n + m) + 1)) =
            Fin.castAdd (m + 1) := by
        funext index
        apply Fin.ext
        rfl
      have hmiddle :
          (Fin.castAdd 1 ∘ Fin.natAdd n : Fin m → Fin ((n + m) + 1)) =
            (Fin.natAdd n ∘ Fin.castAdd 1) := by
        funext index
        apply Fin.ext
        rfl
      have hlast : Fin.last (n + m) = Fin.natAdd n (Fin.last m) := by
        apply Fin.ext
        rfl
      rw [hleft, hmiddle, hlast]
      rfl

def doubleCutOuter (input : Concrete.Diagram) :
    Fin (input.regionCount + 2) :=
  Fin.natAdd input.regionCount ⟨0, by decide⟩

def doubleCutInner (input : Concrete.Diagram) :
    Fin (input.regionCount + 2) :=
  Fin.natAdd input.regionCount ⟨1, by decide⟩

@[simp] theorem doubleCutIntroRaw_regionCount
    (input : Concrete.Diagram) (selection : CheckedSelection input) :
    (doubleCutIntroRaw input selection).regionCount =
      input.regionCount + 2 :=
  rfl

@[simp] theorem doubleCutIntroRaw_nodeCount
    (input : Concrete.Diagram) (selection : CheckedSelection input) :
    (doubleCutIntroRaw input selection).nodeCount = input.nodeCount :=
  rfl

@[simp] theorem doubleCutIntroRaw_wireCount
    (input : Concrete.Diagram) (selection : CheckedSelection input) :
    (doubleCutIntroRaw input selection).wireCount = input.wireCount :=
  rfl

@[simp] theorem doubleCutIntroRaw_root
    (input : Concrete.Diagram) (selection : CheckedSelection input) :
    (doubleCutIntroRaw input selection).root =
      Fin.castAdd 2 input.root :=
  rfl

private theorem doubleCutOuter_ne_lift
    (input : Concrete.Diagram) (region : Fin input.regionCount) :
    doubleCutOuter input ≠ Fin.castAdd 2 region := by
  intro equality
  have values := congrArg Fin.val equality
  simp [doubleCutOuter] at values
  omega

private theorem doubleCutInner_ne_lift
    (input : Concrete.Diagram) (region : Fin input.regionCount) :
    doubleCutInner input ≠ Fin.castAdd 2 region := by
  intro equality
  have values := congrArg Fin.val equality
  simp [doubleCutInner] at values
  omega

private theorem doubleCutOuter_ne_inner (input : Concrete.Diagram) :
    doubleCutOuter input ≠ doubleCutInner input := by
  intro equality
  have values := congrArg Fin.val equality
  simp [doubleCutOuter, doubleCutInner] at values

@[simp] theorem doubleCutIntroRaw_wire
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    (wire : Fin input.wireCount) :
    (doubleCutIntroRaw input selection).wires wire =
      liftCWireRegions 2 (input.wires wire) :=
  rfl

private theorem doubleCutIntroRaw_node
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    (node : Fin input.nodeCount) :
    (doubleCutIntroRaw input selection).nodes node =
      if node ∈ selection.val.directNodes then
        reparentLiftedNode 2 (doubleCutInner input) (input.nodes node)
      else
        liftCNode 2 (input.nodes node) := by
  rfl

private theorem doubleCutIntroRaw_oldRegion
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    (region : Fin input.regionCount) :
    (doubleCutIntroRaw input selection).regions (Fin.castAdd 2 region) =
      if region ∈ selection.val.childRoots then
        reparentLiftedRegion 2 (doubleCutInner input) (input.regions region)
      else
        liftCRegion 2 (input.regions region) := by
  simp only [doubleCutIntroRaw, Fin.addCases_left]
  rfl

@[simp] theorem doubleCutIntroRaw_outer
    (input : Concrete.Diagram) (selection : CheckedSelection input) :
    (doubleCutIntroRaw input selection).regions (doubleCutOuter input) =
      .cut (Fin.castAdd 2 selection.val.anchor) := by
  simp only [doubleCutIntroRaw, doubleCutOuter, Fin.addCases_right]
  have zero :
      (⟨0, doubleCutOuter._proof_1⟩ : Fin 2) = 0 := by
    apply Fin.ext
    rfl
  rw [zero]
  rfl

@[simp] theorem doubleCutIntroRaw_inner
    (input : Concrete.Diagram) (selection : CheckedSelection input) :
    (doubleCutIntroRaw input selection).regions (doubleCutInner input) =
      .cut (doubleCutOuter input) := by
  simp only [doubleCutIntroRaw, doubleCutInner, doubleCutOuter,
    Fin.addCases_right]
  have one :
      (⟨1, doubleCutInner._proof_1⟩ : Fin 2) = 1 := by
    apply Fin.ext
    rfl
  rw [one]
  apply congrArg CRegion.cut
  apply Fin.ext
  rfl

private theorem doubleCutIntroRaw_node_region
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    (node : Fin input.nodeCount) :
    ((doubleCutIntroRaw input selection).nodes node).region =
      if node ∈ selection.val.directNodes then
        doubleCutInner input
      else
        Fin.castAdd 2 (input.nodes node).region := by
  rw [doubleCutIntroRaw_node]
  split <;> cases input.nodes node <;> rfl

private theorem doubleCutIntroRaw_oldRegion_parent
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    (region : Fin input.regionCount) :
    ((doubleCutIntroRaw input selection).regions
        (Fin.castAdd 2 region)).parent? =
      if region ∈ selection.val.childRoots then
        some (doubleCutInner input)
      else
        (input.regions region).parent?.map (Fin.castAdd 2) := by
  rw [doubleCutIntroRaw_oldRegion]
  by_cases selected : region ∈ selection.val.childRoots
  · simp only [if_pos selected]
    have parent := selection.property.childRoots_direct region selected
    cases hregion : input.regions region with
    | sheet =>
        rw [hregion] at parent
        simp only [CRegion.parent?] at parent
        cases parent
    | cut =>
        rfl
    | bubble =>
        rfl
  · simp only [if_neg selected]
    cases input.regions region <;> rfl

@[simp] theorem doubleCutIntroRaw_outer_parent
    (input : Concrete.Diagram) (selection : CheckedSelection input) :
    ((doubleCutIntroRaw input selection).regions
        (doubleCutOuter input)).parent? =
      some (Fin.castAdd 2 selection.val.anchor) := by
  rw [doubleCutIntroRaw_outer]
  rfl

@[simp] theorem doubleCutIntroRaw_inner_parent
    (input : Concrete.Diagram) (selection : CheckedSelection input) :
    ((doubleCutIntroRaw input selection).regions
        (doubleCutInner input)).parent? =
      some (doubleCutOuter input) := by
  rw [doubleCutIntroRaw_inner]
  rfl

@[simp] theorem doubleCutIntroRaw_exactScopeWires
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    (region : Fin input.regionCount) :
    Concrete.Elaboration.exactScopeWires
        (doubleCutIntroRaw input selection) (Fin.castAdd 2 region) =
      Concrete.Elaboration.exactScopeWires input region := by
  unfold Concrete.Elaboration.exactScopeWires
  apply congrArg filterFin
  funext wire
  apply Bool.eq_iff_iff.mpr
  simp only [doubleCutIntroRaw_wire, liftCWireRegions]
  simp only [decide_eq_true_eq, Fin.ext_iff]
  constructor
  · intro equality
    exact congrArg
      (fun value : Fin (input.regionCount + 2) => value.val)
      equality
  · intro equality
    apply Fin.ext
    exact equality

@[simp] theorem doubleCutIntroRaw_outer_exactScopeWires
    (input : Concrete.Diagram) (selection : CheckedSelection input) :
    Concrete.Elaboration.exactScopeWires
        (doubleCutIntroRaw input selection) (doubleCutOuter input) = [] := by
  unfold Concrete.Elaboration.exactScopeWires filterFin
  rw [show allFin (doubleCutIntroRaw input selection).wireCount =
      allFin input.wireCount by rfl]
  apply List.filter_eq_nil_iff.mpr
  intro wire _ selected
  have equality := decide_eq_true_eq.mp selected
  exact doubleCutOuter_ne_lift input (input.wires wire).scope equality.symm

@[simp] theorem doubleCutIntroRaw_inner_exactScopeWires
    (input : Concrete.Diagram) (selection : CheckedSelection input) :
    Concrete.Elaboration.exactScopeWires
        (doubleCutIntroRaw input selection) (doubleCutInner input) = [] := by
  unfold Concrete.Elaboration.exactScopeWires filterFin
  rw [show allFin (doubleCutIntroRaw input selection).wireCount =
      allFin input.wireCount by rfl]
  apply List.filter_eq_nil_iff.mpr
  intro wire _ selected
  have equality := decide_eq_true_eq.mp selected
  exact doubleCutInner_ne_lift input (input.wires wire).scope equality.symm

structure LiftedBinderWitness
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    {sourceRels targetRels : RelCtx}
    (sourceBinders : Concrete.Elaboration.BinderContext input sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext
      (doubleCutIntroRaw input selection) targetRels) : Type where
  relationContexts_eq : sourceRels = targetRels
  binders_eq : ∀ region,
    HEq (sourceBinders region)
      (targetBinders (Fin.castAdd 2 region))

namespace LiftedBinderWitness

def relationMap
    (witness : LiftedBinderWitness input selection
      (sourceRels := sourceRels) (targetRels := targetRels)
      sourceBinders targetBinders) :
    RelationRenaming sourceRels targetRels := by
  cases witness.relationContexts_eq
  exact Concrete.Elaboration.identityRelationRenaming sourceRels

def push
    (witness : LiftedBinderWitness input selection sourceBinders targetBinders)
    (child parent : Fin input.regionCount) (arity : Nat) :
    LiftedBinderWitness input selection
      (sourceBinders.push child arity)
      (targetBinders.push (Fin.castAdd 2 child) arity) := by
  refine ⟨congrArg (List.cons arity) witness.relationContexts_eq, ?_⟩
  intro region
  cases witness.relationContexts_eq
  simp only [Concrete.Elaboration.BinderContext.push]
  by_cases equality : region = child
  · subst region
    simp
  · have liftedNe : Fin.castAdd 2 region ≠ Fin.castAdd 2 child := by
      intro liftedEquality
      apply equality
      apply Fin.ext
      exact congrArg
        (fun value : Fin (input.regionCount + 2) => value.val)
        liftedEquality
    rw [if_neg equality]
    apply heq_of_eq
    split
    · rename_i liftedEquality
      exact False.elim (liftedNe liftedEquality)
    · rw [eq_of_heq (witness.binders_eq region)]

theorem relationMap_push
    (witness : LiftedBinderWitness input selection
      (sourceRels := sourceRels) (targetRels := targetRels)
      sourceBinders targetBinders)
    (child parent : Fin input.regionCount) (arity : Nat) :
    (relationMap (push witness child parent arity) :
        RelationRenaming (arity :: sourceRels) (arity :: targetRels)) =
      (RelationRenaming.lift (relationMap witness) arity :
        RelationRenaming (arity :: sourceRels) (arity :: targetRels)) := by
  cases witness.relationContexts_eq
  simpa [relationMap, Concrete.Elaboration.identityRelationRenaming] using
    (RelationRenaming.lift_id_fun (source := sourceRels) arity).symm

end LiftedBinderWitness

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
    simp [occurrenceSelected, and_comm]
  · apply congrArg
      (List.map Concrete.Elaboration.LocalOccurrence.child)
    apply congrArg
      (fun predicate => List.filter predicate (allFin input.regionCount))
    funext child
    apply Bool.eq_iff_iff.mpr
    simp [occurrenceSelected, and_comm]

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
    simp only [Function.comp_apply, occurrenceSelected, Bool.and_eq_true,
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
    simp only [Function.comp_apply, occurrenceSelected, Bool.and_eq_true,
      decide_eq_true_eq]
    constructor
    · exact And.left
    · intro selected
      exact ⟨selected,
        selection.property.childRoots_direct child selected⟩

theorem doubleCutIntroRaw_inner_localOccurrences
    (input : Concrete.Diagram) (selection : CheckedSelection input) :
    Concrete.Elaboration.localOccurrences
        (doubleCutIntroRaw input selection) (doubleCutInner input) =
      (selectedOccurrences input selection).map (liftOccurrence input) := by
  rw [selectedOccurrences_eq_canonical]
  unfold Concrete.Elaboration.localOccurrences canonicalSelectedOccurrences
    filterFin
  simp only [doubleCutIntroRaw_nodeCount, doubleCutIntroRaw_regionCount,
    List.map_append, List.map_map, Function.comp_apply]
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
    · have regionEq := doubleCutIntroRaw_node_region input selection node
      rw [if_pos selected] at regionEq
      exact ⟨fun _ => selected, fun _ => regionEq⟩
    · have regionEq := doubleCutIntroRaw_node_region input selection node
      rw [if_neg selected] at regionEq
      constructor
      · intro equality
        exact False.elim (doubleCutInner_ne_lift input
          (input.nodes node).region (equality.symm.trans regionEq))
      · intro impossible
        exact False.elim (selected impossible)
  · let newRegions :
        List (Fin (input.regionCount + 2)) :=
        List.filter
          (fun child => decide
            (((doubleCutIntroRaw input selection).regions child).parent? =
              some (doubleCutInner input)))
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
        have indexEq :
            Fin.natAdd input.regionCount (0 : Fin 2) =
              doubleCutOuter input := by
          apply Fin.ext
          rfl
        rw [indexEq, doubleCutIntroRaw_outer_parent] at parent
        exact doubleCutInner_ne_lift input selection.val.anchor
          (Option.some.inj parent).symm
      · subst small
        have indexEq :
            Fin.natAdd input.regionCount (1 : Fin 2) =
              doubleCutInner input := by
          apply Fin.ext
          rfl
        rw [indexEq, doubleCutIntroRaw_inner_parent] at parent
        exact doubleCutOuter_ne_inner input (Option.some.inj parent)
    change _ ++
      List.map
        (Concrete.Elaboration.LocalOccurrence.child
          (nodes := input.nodeCount)) newRegions = _
    simp only [newChildRegions, List.map_nil]
    have oldRegionsEq :
        List.filter
            ((fun child =>
              decide (((doubleCutIntroRaw input selection).regions child).parent? =
                some (doubleCutInner input))) ∘ Fin.castAdd 2)
            (allFin input.regionCount) =
          List.filter (fun child =>
            decide (child ∈ selection.val.childRoots))
            (allFin input.regionCount) := by
      apply congrArg
        (fun predicate => List.filter predicate (allFin input.regionCount))
      funext child
      apply Bool.eq_iff_iff.mpr
      simp only [Function.comp_apply, decide_eq_true_eq]
      have parentEq :=
        doubleCutIntroRaw_oldRegion_parent input selection child
      by_cases selected : child ∈ selection.val.childRoots
      · rw [if_pos selected] at parentEq
        exact ⟨fun _ => selected, fun _ => parentEq⟩
      · rw [if_neg selected] at parentEq
        constructor
        · intro targetParent
          rw [parentEq] at targetParent
          cases oldParent : (input.regions child).parent? with
          | none =>
              simp [oldParent] at targetParent
          | some parent =>
              simp [oldParent] at targetParent
              exact False.elim (doubleCutInner_ne_lift input parent
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

theorem doubleCutIntroRaw_outer_localOccurrences
    (input : Concrete.Diagram) (selection : CheckedSelection input) :
    Concrete.Elaboration.localOccurrences
        (doubleCutIntroRaw input selection) (doubleCutOuter input) =
      [Concrete.Elaboration.LocalOccurrence.child (doubleCutInner input)] := by
  unfold Concrete.Elaboration.localOccurrences filterFin
  simp only [doubleCutIntroRaw_nodeCount, doubleCutIntroRaw_regionCount]
  rw [allFin_add input.regionCount 2, List.filter_append,
    List.map_append]
  let nodeRegions :
      List (Fin (doubleCutIntroRaw input selection).nodeCount) :=
      List.filter
        (fun node => decide
          (((doubleCutIntroRaw input selection).nodes node).region =
            doubleCutOuter input))
        (allFin input.nodeCount)
  have noNodes : nodeRegions = [] := by
    unfold nodeRegions
    apply List.filter_eq_nil_iff.mpr
    intro node _ selected
    have owner := decide_eq_true_eq.mp selected
    have ownerEq := doubleCutIntroRaw_node_region input selection node
    split at ownerEq
    · exact doubleCutOuter_ne_inner input (owner.symm.trans ownerEq)
    ·
      exact doubleCutOuter_ne_lift input (input.nodes node).region
        (owner.symm.trans ownerEq)
  change List.map Concrete.Elaboration.LocalOccurrence.node nodeRegions ++ _ = _
  simp only [noNodes, List.map_nil, List.nil_append]
  let oldRegions : List (Fin input.regionCount) :=
      List.filter
        ((fun child => decide
          (((doubleCutIntroRaw input selection).regions child).parent? =
            some (doubleCutOuter input))) ∘ Fin.castAdd 2)
        (allFin input.regionCount)
  have noOldChildren : oldRegions = [] := by
    unfold oldRegions
    apply List.filter_eq_nil_iff.mpr
    intro child _ selected
    have parent := decide_eq_true_eq.mp selected
    have parentEq :=
      doubleCutIntroRaw_oldRegion_parent input selection child
    by_cases chosen : child ∈ selection.val.childRoots
    · rw [if_pos chosen] at parentEq
      rw [parentEq] at parent
      exact doubleCutOuter_ne_inner input (Option.some.inj parent).symm
    · rw [if_neg chosen] at parentEq
      rw [parentEq] at parent
      cases oldParent : (input.regions child).parent? with
      | none =>
          simp [oldParent] at parent
      | some old =>
          simp [oldParent] at parent
          exact doubleCutOuter_ne_lift input old
            parent.symm
  rw [List.filter_map]
  change List.map Concrete.Elaboration.LocalOccurrence.child
      (List.map (Fin.castAdd 2) oldRegions) ++ _ = _
  simp only [noOldChildren, List.map_nil, List.nil_append]
  change List.map Concrete.Elaboration.LocalOccurrence.child
      (List.filter _ (List.map (Fin.natAdd input.regionCount) (allFin 2))) =
    [_]
  have addedFilter :
      List.filter
          (fun child => decide
            (((doubleCutIntroRaw input selection).regions child).parent? =
              some (doubleCutOuter input)))
          (List.map (Fin.natAdd input.regionCount) (allFin 2)) =
        [doubleCutInner input] := by
    rw [show allFin 2 = [(0 : Fin 2), (1 : Fin 2)] by decide]
    simp only [List.map_cons, List.map_nil, List.filter_cons, List.filter_nil]
    have outerIndex :
        Fin.natAdd input.regionCount (0 : Fin 2) =
          doubleCutOuter input := by
      apply Fin.ext
      rfl
    have innerIndex :
        Fin.natAdd input.regionCount (1 : Fin 2) =
          doubleCutInner input := by
      apply Fin.ext
      rfl
    rw [outerIndex, innerIndex]
    have outerNotParent :
        ¬((doubleCutIntroRaw input selection).regions
            (doubleCutOuter input)).parent? =
          some (doubleCutOuter input) := by
      rw [doubleCutIntroRaw_outer_parent]
      intro equality
      exact doubleCutOuter_ne_lift input selection.val.anchor
        (Option.some.inj equality).symm
    have innerIsParent :
        ((doubleCutIntroRaw input selection).regions
            (doubleCutInner input)).parent? =
          some (doubleCutOuter input) :=
      doubleCutIntroRaw_inner_parent input selection
    rw [decide_eq_false outerNotParent, decide_eq_true innerIsParent]
    rfl
  have mappedAdded := congrArg
    (List.map
      (Concrete.Elaboration.LocalOccurrence.child
        (nodes := input.nodeCount)))
    addedFilter
  simpa only [List.map_cons, List.map_nil] using mappedAdded

theorem doubleCutIntroRaw_anchor_localOccurrences
    (input : Concrete.Diagram) (selection : CheckedSelection input) :
    Concrete.Elaboration.localOccurrences
        (doubleCutIntroRaw input selection)
        (Fin.castAdd 2 selection.val.anchor) =
      (keptOccurrences input selection).map (liftOccurrence input) ++
        [Concrete.Elaboration.LocalOccurrence.child (doubleCutOuter input)] := by
  rw [keptOccurrences_eq_canonical]
  unfold Concrete.Elaboration.localOccurrences canonicalKeptOccurrences filterFin
  simp only [doubleCutIntroRaw_nodeCount, doubleCutIntroRaw_regionCount,
    List.map_append, List.map_map]
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
  rw [liftNode, liftChild]
  rw [List.append_assoc]
  congr 1
  · apply congrArg
      (List.map Concrete.Elaboration.LocalOccurrence.node)
    apply congrArg
      (fun predicate => List.filter predicate (allFin input.nodeCount))
    funext node
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    have ownerEq := doubleCutIntroRaw_node_region input selection node
    by_cases chosen : node ∈ selection.val.directNodes
    · constructor
      · intro owner
        have selectedOwner :
            ((doubleCutIntroRaw input selection).nodes node).region =
              doubleCutInner input := by
          simpa only [if_pos chosen] using ownerEq
        exact False.elim (doubleCutInner_ne_lift input selection.val.anchor
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
    have newRegionsEq : newRegions = [doubleCutOuter input] := by
      unfold newRegions
      rw [show allFin 2 = [(0 : Fin 2), (1 : Fin 2)] by decide]
      simp only [List.map_cons, List.map_nil, List.filter_cons, List.filter_nil]
      have outerIndex :
          Fin.natAdd input.regionCount (0 : Fin 2) =
            doubleCutOuter input := by
        apply Fin.ext
        rfl
      have innerIndex :
          Fin.natAdd input.regionCount (1 : Fin 2) =
            doubleCutInner input := by
        apply Fin.ext
        rfl
      rw [outerIndex, innerIndex]
      have outerParent :
          ((doubleCutIntroRaw input selection).regions
              (doubleCutOuter input)).parent? =
            some (Fin.castAdd 2 selection.val.anchor) :=
        doubleCutIntroRaw_outer_parent input selection
      have innerNotParent :
          ¬((doubleCutIntroRaw input selection).regions
              (doubleCutInner input)).parent? =
            some (Fin.castAdd 2 selection.val.anchor) := by
        rw [doubleCutIntroRaw_inner_parent]
        intro equality
        exact doubleCutOuter_ne_lift input selection.val.anchor
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
      have parentEq :=
        doubleCutIntroRaw_oldRegion_parent input selection child
      by_cases chosen : child ∈ selection.val.childRoots
      · constructor
        · intro parent
          rw [if_pos chosen] at parentEq
          rw [parentEq] at parent
          exact False.elim (doubleCutInner_ne_lift input selection.val.anchor
            (Option.some.inj parent))
        · intro impossible
          exact False.elim (impossible.2 chosen)
      · rw [if_neg chosen] at parentEq
        constructor
        · intro parent
          rw [parentEq] at parent
          cases oldParent : (input.regions child).parent? with
          | none =>
              simp [oldParent] at parent
          | some old =>
              simp [oldParent] at parent
              refine ⟨?_, chosen⟩
              apply congrArg some
              apply Fin.ext
              exact congrArg
                (fun value : Fin (input.regionCount + 2) => value.val)
                parent
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
            (regions := input.regionCount + 2) (doubleCutOuter input)] := by
      change
        List.map
            (Concrete.Elaboration.LocalOccurrence.child
              (regions := input.regionCount + 2) (nodes := input.nodeCount))
            newRegions =
          [Concrete.Elaboration.LocalOccurrence.child
            (regions := input.regionCount + 2) (doubleCutOuter input)]
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
                  (fun occurrences =>
                    occurrences ++
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
      _ = _ := by
        rw [newMappedEq]

theorem anchorOccurrences_perm_partition
    (input : Concrete.Diagram) (selection : CheckedSelection input) :
    List.Perm
      (keptOccurrences input selection ++ selectedOccurrences input selection)
      (Concrete.Elaboration.localOccurrences input selection.val.anchor) := by
  simpa only [keptOccurrences, selectedOccurrences, Bool.not_not] using
    (List.filter_append_perm
      (fun occurrence => !(occurrenceSelected selection occurrence))
      (Concrete.Elaboration.localOccurrences input selection.val.anchor))

private theorem doubleCutIntroRaw_regular_localOccurrences
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    (region : Fin input.regionCount)
    (regular : region ≠ selection.val.anchor) :
    Concrete.Elaboration.localOccurrences
        (doubleCutIntroRaw input selection) (Fin.castAdd 2 region) =
      (Concrete.Elaboration.localOccurrences input region).map
        (liftOccurrence input) := by
  unfold Concrete.Elaboration.localOccurrences filterFin
  simp only [doubleCutIntroRaw_nodeCount, doubleCutIntroRaw_regionCount,
    List.map_append, List.map_map]
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
  rw [liftNode, liftChild]
  congr 1
  · apply congrArg
      (List.map Concrete.Elaboration.LocalOccurrence.node)
    apply congrArg
      (fun predicate => List.filter predicate (allFin input.nodeCount))
    funext node
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    have ownerEq := doubleCutIntroRaw_node_region input selection node
    by_cases chosen : node ∈ selection.val.directNodes
    · have sourceOwner :=
        selection.property.directNodes_at_anchor node chosen
      constructor
      · intro targetOwner
        rw [if_pos chosen] at ownerEq
        exact False.elim
          (doubleCutInner_ne_lift input region
            (ownerEq.symm.trans targetOwner))
      · intro sourceAtRegion
        exact False.elim
          (regular (sourceOwner.symm.trans sourceAtRegion).symm)
    · rw [if_neg chosen] at ownerEq
      constructor
      · intro targetOwner
        apply Fin.ext
        exact congrArg
          (fun value : Fin (input.regionCount + 2) => value.val)
          (ownerEq.symm.trans targetOwner)
      · intro sourceOwner
        exact ownerEq.trans (congrArg (Fin.castAdd 2) sourceOwner)
  · have addedRegionsNil :
        List.filter
            (fun child => decide
              (((doubleCutIntroRaw input selection).regions child).parent? =
                some (Fin.castAdd 2 region)))
            (List.map (Fin.natAdd input.regionCount) (allFin 2)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro child childMem selected
      have parent := decide_eq_true_eq.mp selected
      rw [show allFin 2 = [(0 : Fin 2), (1 : Fin 2)] by decide] at childMem
      simp only [List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at childMem
      rcases childMem with outer | inner
      · have outerEq :
            Fin.natAdd input.regionCount (0 : Fin 2) =
              doubleCutOuter input := by
          apply Fin.ext
          rfl
        rw [outer, outerEq, doubleCutIntroRaw_outer_parent] at parent
        apply regular
        apply Fin.ext
        exact (congrArg
          (fun value : Fin (input.regionCount + 2) => value.val)
          (Option.some.inj parent)).symm
      · have innerEq :
            Fin.natAdd input.regionCount (1 : Fin 2) =
              doubleCutInner input := by
          apply Fin.ext
          rfl
        rw [inner, innerEq, doubleCutIntroRaw_inner_parent] at parent
        exact doubleCutOuter_ne_lift input region
          (Option.some.inj parent)
    have addedOccurrencesNil := congrArg
      (List.map
        (Concrete.Elaboration.LocalOccurrence.child
          (regions := input.regionCount + 2) (nodes := input.nodeCount)))
      addedRegionsNil
    simp only [List.map_nil] at addedOccurrencesNil
    calc
      _ =
          List.map
              (Concrete.Elaboration.LocalOccurrence.child
                (regions := input.regionCount + 2) (nodes := input.nodeCount))
              (List.map (Fin.castAdd 2)
                (List.filter
                  ((fun child => decide
                    (((doubleCutIntroRaw input selection).regions child).parent? =
                      some (Fin.castAdd 2 region))) ∘ Fin.castAdd 2)
                  (allFin input.regionCount))) ++ [] := by
            exact congrArg
              (fun tail =>
                List.map
                    (Concrete.Elaboration.LocalOccurrence.child
                      (regions := input.regionCount + 2)
                      (nodes := input.nodeCount))
                    (List.map (Fin.castAdd 2)
                      (List.filter
                        ((fun child => decide
                          (((doubleCutIntroRaw input selection).regions child).parent? =
                            some (Fin.castAdd 2 region))) ∘ Fin.castAdd 2)
                        (allFin input.regionCount))) ++ tail)
              addedOccurrencesNil
      _ = _ := by
        rw [List.append_nil, List.map_map]
        apply congrArg
          (List.map
            (Concrete.Elaboration.LocalOccurrence.child ∘ Fin.castAdd 2))
        apply congrArg
          (fun predicate => List.filter predicate (allFin input.regionCount))
        funext child
        apply Bool.eq_iff_iff.mpr
        simp only [Function.comp_apply, decide_eq_true_eq]
        have parentEq :=
          doubleCutIntroRaw_oldRegion_parent input selection child
        by_cases chosen : child ∈ selection.val.childRoots
        · have sourceParent :=
            selection.property.childRoots_direct child chosen
          constructor
          · intro targetParent
            rw [if_pos chosen] at parentEq
            exact False.elim
              (doubleCutInner_ne_lift input region
                (Option.some.inj (parentEq.symm.trans targetParent)))
          · intro sourceAtRegion
            exact False.elim
              (regular
                (Option.some.inj
                  (sourceParent.symm.trans sourceAtRegion)).symm)
        · rw [if_neg chosen] at parentEq
          constructor
          · intro targetParent
            cases sourceParent : (input.regions child).parent? with
            | none =>
                rw [parentEq, sourceParent] at targetParent
                cases targetParent
            | some parent =>
                rw [sourceParent] at parentEq
                apply congrArg some
                apply Fin.ext
                exact congrArg
                  (fun value : Fin (input.regionCount + 2) => value.val)
                  (Option.some.inj (parentEq.symm.trans targetParent))
          · intro sourceParent
            rw [sourceParent] at parentEq
            exact parentEq

theorem doubleCutIntroRaw_regular_regionShape
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    (parent child : Fin input.regionCount)
    (regular : parent ≠ selection.val.anchor)
    (childParent : (input.regions child).parent? = some parent) :
    (doubleCutIntroRaw input selection).regions (Fin.castAdd 2 child) =
      match input.regions child with
      | .sheet => .sheet
      | .cut actualParent => .cut (Fin.castAdd 2 actualParent)
      | .bubble actualParent arity =>
          .bubble (Fin.castAdd 2 actualParent) arity := by
  have childNotSelected : child ∉ selection.val.childRoots := by
    intro selected
    have direct := selection.property.childRoots_direct child selected
    exact regular (Option.some.inj (childParent.symm.trans direct))
  rw [doubleCutIntroRaw_oldRegion, if_neg childNotSelected]
  cases input.regions child <;> rfl

theorem doubleCutIntroRaw_regular_nodeShape
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    (region : Fin input.regionCount) (regular : region ≠ selection.val.anchor)
    (node : Fin input.nodeCount)
    (nodeRegion : (input.nodes node).region = region) :
    (doubleCutIntroRaw input selection).nodes node =
      match input.nodes node with
      | .atom owner binder =>
          .atom (Fin.castAdd 2 owner) (Fin.castAdd 2 binder)
      | .identity owner arity =>
          .identity (Fin.castAdd 2 owner) arity := by
  have nodeNotSelected : node ∉ selection.val.directNodes := by
    intro selected
    have atAnchor :=
      selection.property.directNodes_at_anchor node selected
    exact regular (nodeRegion.symm.trans atAnchor)
  rw [doubleCutIntroRaw_node, if_neg nodeNotSelected]
  cases input.nodes node <;> rfl

theorem doubleCutIntroRaw_selected_nodeShape
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    (node : Fin input.nodeCount)
    (selected : node ∈ selection.val.directNodes) :
    (doubleCutIntroRaw input selection).nodes node =
      match input.nodes node with
      | .atom _ binder =>
          .atom (doubleCutInner input) (Fin.castAdd 2 binder)
      | .identity _ arity =>
          .identity (doubleCutInner input) arity := by
  rw [doubleCutIntroRaw_node, if_pos selected]
  cases input.nodes node <;> rfl

theorem doubleCutIntroRaw_unselected_nodeShape
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    (node : Fin input.nodeCount)
    (unselected : node ∉ selection.val.directNodes) :
    (doubleCutIntroRaw input selection).nodes node =
      match input.nodes node with
      | .atom owner binder =>
          .atom (Fin.castAdd 2 owner) (Fin.castAdd 2 binder)
      | .identity owner arity =>
          .identity (Fin.castAdd 2 owner) arity := by
  rw [doubleCutIntroRaw_node, if_neg unselected]
  cases input.nodes node <;> rfl

theorem doubleCutIntroRaw_selected_regionShape
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    (child : Fin input.regionCount)
    (selected : child ∈ selection.val.childRoots) :
    (doubleCutIntroRaw input selection).regions (Fin.castAdd 2 child) =
      match input.regions child with
      | .sheet => .sheet
      | .cut _ => .cut (doubleCutInner input)
      | .bubble _ arity => .bubble (doubleCutInner input) arity := by
  rw [doubleCutIntroRaw_oldRegion, if_pos selected]
  cases input.regions child <;> rfl

theorem doubleCutIntroRaw_unselected_regionShape
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    (child : Fin input.regionCount)
    (unselected : child ∉ selection.val.childRoots) :
    (doubleCutIntroRaw input selection).regions (Fin.castAdd 2 child) =
      match input.regions child with
      | .sheet => .sheet
      | .cut parent => .cut (Fin.castAdd 2 parent)
      | .bubble parent arity =>
          .bubble (Fin.castAdd 2 parent) arity := by
  rw [doubleCutIntroRaw_oldRegion, if_neg unselected]
  cases input.regions child <;> rfl

structure LiftedContextWitness
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext
      (doubleCutIntroRaw input selection)) : Type where
  contexts_eq : sourceContext = targetContext

namespace LiftedContextWitness

def indexRelation
    (witness : LiftedContextWitness input selection
      sourceContext targetContext) :
    Concrete.Elaboration.ContextIndexRelation
      sourceContext.length targetContext.length := by
  exact Concrete.Elaboration.ContextIndexRelation.forwardMap
    (Fin.cast (congrArg List.length witness.contexts_eq))

def extend
    (witness : LiftedContextWitness input selection
      sourceContext targetContext)
    (region : Fin input.regionCount) :
    LiftedContextWitness input selection
      (sourceContext.extend region)
      (targetContext.extend (Fin.castAdd 2 region)) := by
  rcases witness with ⟨rfl⟩
  refine ⟨?_⟩
  simp only [Concrete.Elaboration.WireContext.extend,
    doubleCutIntroRaw_exactScopeWires]
  rfl

end LiftedContextWitness

private theorem doubleCutIntroRaw_endpointOccurs
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    (wire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount) :
    (doubleCutIntroRaw input selection).EndpointOccurs wire endpoint ↔
      input.EndpointOccurs wire endpoint := by
  simp only [Concrete.Diagram.EndpointOccurs, doubleCutIntroRaw_wire,
    liftCWireRegions]
  rfl

private theorem doubleCutIntroRaw_endpointOwner
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    (endpoint : CEndpoint input.nodeCount) :
    Concrete.Elaboration.endpointOwner?
        (doubleCutIntroRaw input selection) endpoint =
      Concrete.Elaboration.endpointOwner? input endpoint := by
  unfold Concrete.Elaboration.endpointOwner?
  apply congrArg List.head?
  unfold filterFin
  apply List.filter_congr
  intro wire _
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact doubleCutIntroRaw_endpointOccurs input selection wire endpoint

private theorem doubleCutIntroRaw_resolvePort
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext
      (doubleCutIntroRaw input selection))
    (witness : LiftedContextWitness input selection
      sourceContext targetContext)
    (node : Fin input.nodeCount) (port : CPort) :
    Concrete.Elaboration.resolvePort?
        (doubleCutIntroRaw input selection) targetContext node port =
      (Concrete.Elaboration.resolvePort? input sourceContext node port).map
        (Fin.cast (congrArg List.length witness.contexts_eq)) := by
  rcases witness with ⟨rfl⟩
  simp only [Concrete.Elaboration.resolvePort?,
    doubleCutIntroRaw_endpointOwner]
  generalize resultEq :
      (do
        let wire ← Concrete.Elaboration.endpointOwner? input ⟨node, port⟩
        sourceContext.lookup? wire) = result
  cases result with
  | none =>
      exact resultEq.trans rfl
  | some index =>
      apply resultEq.trans
      simp only [Option.map_some]
      apply congrArg some
      apply Fin.ext
      rfl

theorem extendWireEnv_transport
    {D : Type} {outer sourceLocalCount targetLocalCount : Nat}
    (countEq : targetLocalCount = sourceLocalCount)
    (sourceLocal : Fin sourceLocalCount → D)
    (targetLocal : Fin targetLocalCount → D)
    (localValues : ∀ index,
      targetLocal index = sourceLocal (Fin.cast countEq index))
    (sourceIndex : Fin (outer + sourceLocalCount))
    (targetIndex : Fin (outer + targetLocalCount))
    (indexValue : sourceIndex.val = targetIndex.val) :
    ∀ (outerEnv : Fin outer → D),
      extendWireEnv outerEnv sourceLocal sourceIndex =
        extendWireEnv outerEnv targetLocal targetIndex := by
  subst targetLocalCount
  have targetLocalEq : targetLocal = sourceLocal := by
    funext index
    simpa using localValues index
  subst targetLocal
  have indexEq : sourceIndex = targetIndex := by
    apply Fin.ext
    exact indexValue
  subst targetIndex
  exact fun _ => rfl

theorem finishRegion_noWires_denote
    (diagram : Concrete.Diagram)
    (context : Concrete.Elaboration.WireContext diagram)
    (region : Fin diagram.regionCount)
    (empty :
      Concrete.Elaboration.exactScopeWires diagram region = [])
    (items : ItemSeq  (context.extend region).length rels)
    (model : Model)
    (env : Fin context.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels) :
    denoteRegion model  env relEnv
        (Concrete.Elaboration.finishRegion diagram context region items) ↔
      denoteItemSeq model  env relEnv
        (items.castWiresEq
          (congrArg List.length (by
            unfold Concrete.Elaboration.WireContext.extend
            rw [empty]
            exact List.append_nil context))) := by
  let contextEq : context.extend region = context := by
    unfold Concrete.Elaboration.WireContext.extend
    rw [empty]
    exact List.append_nil context
  let contextLengthEq :
      (context.extend region).length = context.length :=
    congrArg List.length contextEq
  have countEq :
      (Concrete.Elaboration.exactScopeWires diagram region).length = 0 :=
    congrArg List.length empty
  have environmentEq
      (localEnv :
        Fin (Concrete.Elaboration.exactScopeWires diagram region).length →
          model.Carrier) :
      extendWireEnv env localEnv ∘
          Fin.cast
            (Concrete.Elaboration.WireContext.length_extend context region) =
        env ∘ Fin.cast contextLengthEq := by
    funext index
    let targetLengthEq :
        (context.extend region).length = context.length + 0 :=
      contextLengthEq.trans (Nat.add_zero context.length).symm
    have transported := extendWireEnv_transport
      (countEq := countEq.symm)
      (sourceLocal := localEnv)
      (targetLocal := (Fin.elim0 :
        Fin 0 → model.Carrier))
      (localValues := by intro impossible; exact Fin.elim0 impossible)
      (sourceIndex := Fin.cast
        (Concrete.Elaboration.WireContext.length_extend context region) index)
      (targetIndex := Fin.cast targetLengthEq index)
      (indexValue := rfl)
      env
    simpa [targetLengthEq, contextLengthEq] using transported
  unfold Concrete.Elaboration.finishRegion
  simp only [denoteRegion_mk]
  constructor
  · rintro ⟨localEnv, hitems⟩
    rw [ItemSeq.castWiresEq_eq_renameWires] at hitems ⊢
    rw [denoteItemSeq_renameWires] at hitems ⊢
    simpa [environmentEq localEnv] using hitems
  · intro hitems
    let localEnv :
        Fin (Concrete.Elaboration.exactScopeWires diagram region).length →
          model.Carrier :=
      fun index => Fin.elim0 (Fin.cast countEq index)
    refine ⟨localEnv, ?_⟩
    rw [ItemSeq.castWiresEq_eq_renameWires] at hitems ⊢
    rw [denoteItemSeq_renameWires] at hitems ⊢
    simpa [environmentEq localEnv] using hitems

private theorem doubleCutIntro_compileNode_itemSimulation
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    (model : Model)
    (direction : Concrete.Elaboration.SimulationDirection)
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext
      (doubleCutIntroRaw input selection))
    (contextWitness : LiftedContextWitness input selection
      sourceContext targetContext)
    (sourceBinders : Concrete.Elaboration.BinderContext input sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext
      (doubleCutIntroRaw input selection) targetRels)
    (binderWitness : LiftedBinderWitness input selection
      sourceBinders targetBinders)
    (node : Fin input.nodeCount)
    (regionMap : Fin input.regionCount →
      Fin (doubleCutIntroRaw input selection).regionCount)
    (nodeShape :
      (doubleCutIntroRaw input selection).nodes node =
        match input.nodes node with
        | .atom owner binder =>
            .atom (regionMap owner) (Fin.castAdd 2 binder)
        | .identity owner arity =>
            .identity (regionMap owner) arity)
    (sourceItem : Item  sourceContext.length sourceRels)
    (targetItem : Item  targetContext.length targetRels)
    (sourceCompiled :
      Concrete.Elaboration.compileNode?  input sourceContext
        sourceBinders node = some sourceItem)
    (targetCompiled :
      Concrete.Elaboration.compileNode?
        (doubleCutIntroRaw input selection) targetContext targetBinders node =
          some targetItem) :
    Concrete.Elaboration.ItemSimulation model  direction
      contextWitness.indexRelation
      (sourceItem.renameRelations binderWitness.relationMap) targetItem := by
  rcases contextWitness with ⟨contextsEq⟩
  cases contextsEq
  apply Concrete.Elaboration.compileNode?_itemSimulation_of_related_ports
    (source := input)
    (target := doubleCutIntroRaw input selection)
    model  direction sourceContext sourceContext
    (Concrete.Elaboration.ContextIndexRelation.forwardMap id)
    sourceBinders targetBinders binderWitness.relationMap
    node node regionMap (Fin.castAdd 2)
  · exact nodeShape
  · intro port sourceIndex targetIndex sourceResolved targetResolved
    have resolved := doubleCutIntroRaw_resolvePort input selection
      sourceContext sourceContext ⟨rfl⟩ node port
    rw [sourceResolved, targetResolved] at resolved
    change sourceIndex = targetIndex
    apply Fin.ext
    exact congrArg Fin.val (Option.some.inj resolved).symm
  · intro nodeOwner binder arity sourceRelation sourceAtom sourceLookup
    cases binderWitness.relationContexts_eq
    simpa [LiftedBinderWitness.relationMap] using
      (eq_of_heq (binderWitness.binders_eq binder)).symm.trans sourceLookup
  · exact sourceCompiled
  · exact targetCompiled

theorem doubleCutIntro_compileOccurrence_itemSimulation
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    (sourceWellFormed : input.WellFormed )
    (targetWellFormed :
      (doubleCutIntroRaw input selection).WellFormed )
    (model : Model)
    (direction : Concrete.Elaboration.SimulationDirection)
    (fuelSource fuelTarget : Nat)
    (sourceParent : Fin input.regionCount)
    (targetParent : Fin (doubleCutIntroRaw input selection).regionCount)
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext
      (doubleCutIntroRaw input selection))
    (contextWitness : LiftedContextWitness input selection
      sourceContext targetContext)
    (sourceBinders : Concrete.Elaboration.BinderContext input sourceRels)
    (targetBinders : Concrete.Elaboration.BinderContext
      (doubleCutIntroRaw input selection) targetRels)
    (binderWitness : LiftedBinderWitness input selection
      sourceBinders targetBinders)
    (sourceExact : sourceContext.Exact sourceParent)
    (targetExact : targetContext.Exact targetParent)
    (sourceBindersCover : sourceBinders.Covers sourceParent)
    (targetBindersCover : targetBinders.Covers targetParent)
    (sourceEnumeration :
      Concrete.Elaboration.BinderContext.Enumeration input sourceBinders
        sourceParent)
    (targetEnumeration :
      Concrete.Elaboration.BinderContext.Enumeration
        (doubleCutIntroRaw input selection) targetBinders targetParent)
    (occurrence :
      Concrete.Elaboration.LocalOccurrence input.regionCount input.nodeCount)
    (regionMap : Fin input.regionCount →
      Fin (doubleCutIntroRaw input selection).regionCount)
    (nodeShape : ∀ node,
      occurrence = .node node →
      (doubleCutIntroRaw input selection).nodes node =
        match input.nodes node with
        | .atom owner binder =>
            .atom (regionMap owner) (Fin.castAdd 2 binder)
        | .identity owner arity =>
            .identity (regionMap owner) arity)
    (regionShape : ∀ child,
      occurrence = .child child →
      (input.regions child).parent? = some sourceParent →
      (doubleCutIntroRaw input selection).regions (Fin.castAdd 2 child) =
        match input.regions child with
        | .sheet => .sheet
        | .cut _ => .cut targetParent
        | .bubble _ arity => .bubble targetParent arity)
    (recurseAt : ∀
      {childDirection : Concrete.Elaboration.SimulationDirection}
      {child : Fin input.regionCount}
      {childSourceRels childTargetRels : RelCtx}
      {childSourceBinders :
        Concrete.Elaboration.BinderContext input childSourceRels}
      {childTargetBinders :
        Concrete.Elaboration.BinderContext
          (doubleCutIntroRaw input selection) childTargetRels}
      (childFuelTarget : Nat)
      (childSourceContext : Concrete.Elaboration.WireContext input)
      (childTargetContext : Concrete.Elaboration.WireContext
        (doubleCutIntroRaw input selection))
      (childContext : LiftedContextWitness input selection
        childSourceContext childTargetContext),
      True →
      True →
      (childBinderWitness : LiftedBinderWitness input selection
        childSourceBinders childTargetBinders) →
      childSourceBinders.Covers child →
      childTargetBinders.Covers (Fin.castAdd 2 child) →
      Concrete.Elaboration.BinderContext.Enumeration input
        childSourceBinders child →
      Concrete.Elaboration.BinderContext.Enumeration
        (doubleCutIntroRaw input selection) childTargetBinders
        (Fin.castAdd 2 child) →
      (childSourceContext.extend child).Exact child →
      (childTargetContext.extend (Fin.castAdd 2 child)).Exact
        (Fin.castAdd 2 child) →
      ∀ (sourceBody :
          Region  childSourceContext.length childSourceRels)
        (targetBody :
          Region  childTargetContext.length childTargetRels),
      Concrete.Elaboration.compileRegion?  input fuelSource child
          childSourceContext childSourceBinders = some sourceBody →
      Concrete.Elaboration.compileRegion?
          (doubleCutIntroRaw input selection) childFuelTarget
          (Fin.castAdd 2 child) childTargetContext childTargetBinders =
        some targetBody →
      Concrete.Elaboration.RegionSimulation model  childDirection
        childContext.indexRelation
        (sourceBody.renameRelations childBinderWitness.relationMap)
        targetBody)
    (member :
      occurrence ∈ Concrete.Elaboration.localOccurrences input sourceParent)
    (sourceItem : Item  sourceContext.length sourceRels)
    (targetItem : Item  targetContext.length targetRels)
    (sourceCompiled :
      Concrete.Elaboration.compileOccurrenceWith?  input
        (Concrete.Elaboration.compileRegion?  input fuelSource)
        sourceContext sourceBinders occurrence = some sourceItem)
    (targetCompiled :
      Concrete.Elaboration.compileOccurrenceWith?
        (doubleCutIntroRaw input selection)
        (Concrete.Elaboration.compileRegion?
          (doubleCutIntroRaw input selection) fuelTarget)
        targetContext targetBinders (liftOccurrence input occurrence) =
          some targetItem) :
    Concrete.Elaboration.ItemSimulation model  direction
      contextWitness.indexRelation
      (sourceItem.renameRelations binderWitness.relationMap) targetItem := by
  cases occurrence with
  | node node =>
      exact doubleCutIntro_compileNode_itemSimulation input selection model
        direction sourceContext targetContext contextWitness sourceBinders
        targetBinders binderWitness node regionMap (nodeShape node rfl)
        sourceItem targetItem sourceCompiled targetCompiled
  | child child =>
      have sourceParentEq :=
        (Concrete.Elaboration.mem_localOccurrences_child input sourceParent
          child).mp member
      have targetKind := regionShape child rfl sourceParentEq
      cases sourceKind : input.regions child with
      | sheet =>
          simp [Concrete.Elaboration.compileOccurrenceWith?, sourceKind] at sourceCompiled
      | cut actualParent =>
          have actualParentEq : actualParent = sourceParent := by
            rw [sourceKind] at sourceParentEq
            exact Option.some.inj sourceParentEq
          subst actualParent
          simp only [sourceKind] at targetKind
          cases sourceResult :
              Concrete.Elaboration.compileRegion?  input fuelSource
                child sourceContext sourceBinders with
          | none =>
              simp [Concrete.Elaboration.compileOccurrenceWith?, sourceKind,
                sourceResult] at sourceCompiled
          | some sourceBody =>
              simp [Concrete.Elaboration.compileOccurrenceWith?, sourceKind,
                sourceResult] at sourceCompiled
              subst sourceItem
              cases targetResult :
                  Concrete.Elaboration.compileRegion?
                    (doubleCutIntroRaw input selection) fuelTarget
                    (Fin.castAdd 2 child) targetContext targetBinders with
              | none =>
                  simp [Concrete.Elaboration.compileOccurrenceWith?,
                    liftOccurrence, targetKind, targetResult] at targetCompiled
              | some targetBody =>
                  simp [Concrete.Elaboration.compileOccurrenceWith?,
                    liftOccurrence, targetKind, targetResult] at targetCompiled
                  subst targetItem
                  have targetParentEq :
                      ((doubleCutIntroRaw input selection).regions
                        (Fin.castAdd 2 child)).parent? =
                        some targetParent := by
                    simp [targetKind, CRegion.parent?]
                  have bodies := recurseAt
                    (childDirection := direction.flip)
                    fuelTarget sourceContext targetContext contextWitness
                    True.intro True.intro binderWitness
                    (Concrete.Elaboration.BinderContext.covers_cut_child
                      sourceBindersCover sourceKind)
                    (Concrete.Elaboration.BinderContext.covers_cut_child
                      targetBindersCover targetKind)
                    (sourceEnumeration.cutChild sourceWellFormed sourceKind)
                    (targetEnumeration.cutChild targetWellFormed targetKind)
                    (sourceExact.extend_child sourceWellFormed sourceParentEq)
                    (targetExact.extend_child targetWellFormed targetParentEq)
                    sourceBody targetBody sourceResult targetResult
                  intro sourceEnv targetEnv relEnv environments
                  have bodyEntailment :=
                    bodies sourceEnv targetEnv relEnv environments
                  simp only [Item.renameRelations, cut_denotes_negation]
                  cases direction with
                  | forward =>
                      exact fun sourceNot targetDenotes =>
                        sourceNot (bodyEntailment targetDenotes)
                  | backward =>
                      exact fun targetNot sourceDenotes =>
                        targetNot (bodyEntailment sourceDenotes)
      | bubble actualParent arity =>
          have actualParentEq : actualParent = sourceParent := by
            rw [sourceKind] at sourceParentEq
            exact Option.some.inj sourceParentEq
          subst actualParent
          simp only [sourceKind] at targetKind
          let sourcePushed := sourceBinders.push child arity
          let targetPushed := targetBinders.push (Fin.castAdd 2 child) arity
          cases sourceResult :
              Concrete.Elaboration.compileRegion?  input fuelSource
                child sourceContext sourcePushed with
          | none =>
              simp [Concrete.Elaboration.compileOccurrenceWith?, sourceKind,
                sourcePushed, sourceResult] at sourceCompiled
          | some sourceBody =>
              simp [Concrete.Elaboration.compileOccurrenceWith?, sourceKind,
                sourcePushed, sourceResult] at sourceCompiled
              subst sourceItem
              cases targetResult :
                  Concrete.Elaboration.compileRegion?
                    (doubleCutIntroRaw input selection) fuelTarget
                    (Fin.castAdd 2 child) targetContext targetPushed with
              | none =>
                  simp [Concrete.Elaboration.compileOccurrenceWith?,
                    liftOccurrence, targetKind, targetPushed, targetResult] at targetCompiled
              | some targetBody =>
                  simp [Concrete.Elaboration.compileOccurrenceWith?,
                    liftOccurrence, targetKind, targetPushed, targetResult] at targetCompiled
                  subst targetItem
                  have targetParentEq :
                      ((doubleCutIntroRaw input selection).regions
                        (Fin.castAdd 2 child)).parent? =
                        some targetParent := by
                    simp [targetKind, CRegion.parent?]
                  let pushedWitness :=
                    LiftedBinderWitness.push binderWitness child sourceParent
                      arity
                  have bodies := recurseAt
                    (childDirection := direction)
                    fuelTarget sourceContext targetContext contextWitness
                    True.intro True.intro pushedWitness
                    (Concrete.Elaboration.BinderContext.push_covers_bubble_child
                      sourceBindersCover sourceKind)
                    (Concrete.Elaboration.BinderContext.push_covers_bubble_child
                      targetBindersCover targetKind)
                    (sourceEnumeration.bubbleChild sourceWellFormed sourceKind)
                    (targetEnumeration.bubbleChild targetWellFormed targetKind)
                    (sourceExact.extend_child sourceWellFormed sourceParentEq)
                    (targetExact.extend_child targetWellFormed targetParentEq)
                    sourceBody targetBody sourceResult targetResult
                  have pushedMap :
                      (pushedWitness.relationMap :
                        RelationRenaming (arity :: sourceRels)
                          (arity :: targetRels)) =
                        (RelationRenaming.lift binderWitness.relationMap arity :
                          RelationRenaming (arity :: sourceRels)
                            (arity :: targetRels)) := by
                    simpa only [pushedWitness] using
                      LiftedBinderWitness.relationMap_push binderWitness child
                        sourceParent arity
                  rw [pushedMap] at bodies
                  intro sourceEnv targetEnv relEnv environments
                  simp only [Item.renameRelations, bubble_denotes_exists]
                  cases direction with
                  | forward =>
                      rintro ⟨relationValue, sourceDenotes⟩
                      exact ⟨relationValue,
                        bodies sourceEnv targetEnv (relationValue, relEnv)
                          environments sourceDenotes⟩
                  | backward =>
                      rintro ⟨relationValue, targetDenotes⟩
                      exact ⟨relationValue,
                        bodies sourceEnv targetEnv (relationValue, relEnv)
                          environments targetDenotes⟩

theorem compileOccurrence_success_of_mem
    (diagram : Concrete.Diagram)
    (recurse : ∀ {rels : RelCtx},
      (region : Fin diagram.regionCount) →
      (context : Concrete.Elaboration.WireContext diagram) →
      Concrete.Elaboration.BinderContext diagram rels →
      Option (Region  context.length rels))
    (context : Concrete.Elaboration.WireContext diagram)
    (binders : Concrete.Elaboration.BinderContext diagram rels)
    {occurrences : List
      (Concrete.Elaboration.LocalOccurrence diagram.regionCount
        diagram.nodeCount)}
    {items : ItemSeq  context.length rels}
    (compiled :
      Concrete.Elaboration.compileOccurrencesWith?  diagram recurse
        context binders occurrences = some items)
    {occurrence} (member : occurrence ∈ occurrences) :
    ∃ item,
      Concrete.Elaboration.compileOccurrenceWith?  diagram recurse
        context binders occurrence = some item := by
  induction occurrences generalizing items with
  | nil => simp at member
  | cons head tail induction =>
      simp only [Concrete.Elaboration.compileOccurrencesWith?] at compiled
      cases headResult :
          Concrete.Elaboration.compileOccurrenceWith?  diagram recurse
            context binders head with
      | none => simp [headResult] at compiled
      | some headItem =>
          cases tailResult :
              Concrete.Elaboration.compileOccurrencesWith?  diagram
                recurse context binders tail with
          | none => simp [headResult, tailResult] at compiled
          | some tailItems =>
              simp [headResult, tailResult] at compiled
              subst items
              rcases List.mem_cons.mp member with rfl | member
              · exact ⟨headItem, headResult⟩
              · exact induction tailResult member

theorem compileOccurrences_denote_perm
    (diagram : Concrete.Diagram)
    (recurse : ∀ {rels : RelCtx},
      (region : Fin diagram.regionCount) →
      (context : Concrete.Elaboration.WireContext diagram) →
      Concrete.Elaboration.BinderContext diagram rels →
      Option (Region  context.length rels))
    (context : Concrete.Elaboration.WireContext diagram)
    (binders : Concrete.Elaboration.BinderContext diagram rels)
    {sourceOccurrences targetOccurrences : List
      (Concrete.Elaboration.LocalOccurrence diagram.regionCount
        diagram.nodeCount)}
    (permutation : List.Perm sourceOccurrences targetOccurrences)
    {sourceItems targetItems : ItemSeq  context.length rels}
    (sourceCompiled :
      Concrete.Elaboration.compileOccurrencesWith?  diagram recurse
        context binders sourceOccurrences = some sourceItems)
    (targetCompiled :
      Concrete.Elaboration.compileOccurrencesWith?  diagram recurse
        context binders targetOccurrences = some targetItems)
    (model : Model)
    (env : Fin context.length → model.Carrier)
    (relEnv : RelEnv model.Carrier rels) :
    denoteItemSeq model  env relEnv sourceItems ↔
      denoteItemSeq model  env relEnv targetItems := by
  induction permutation generalizing sourceItems targetItems with
  | nil =>
      simp only [Concrete.Elaboration.compileOccurrencesWith?] at sourceCompiled targetCompiled
      cases sourceCompiled
      cases targetCompiled
      rfl
  | @cons head sourceTailOccurrences targetTailOccurrences permutation induction =>
      simp only [Concrete.Elaboration.compileOccurrencesWith?] at sourceCompiled targetCompiled
      cases headResult :
          Concrete.Elaboration.compileOccurrenceWith?  diagram recurse
            context binders head with
      | none => simp [headResult] at sourceCompiled
      | some headItem =>
          cases sourceTailResult :
              Concrete.Elaboration.compileOccurrencesWith?  diagram
                recurse context binders sourceTailOccurrences with
          | none => simp [headResult, sourceTailResult] at sourceCompiled
          | some sourceTail =>
              cases targetTailResult :
                  Concrete.Elaboration.compileOccurrencesWith?  diagram
                    recurse context binders targetTailOccurrences with
              | none => simp [headResult, targetTailResult] at targetCompiled
              | some targetTail =>
                  simp [headResult, sourceTailResult] at sourceCompiled
                  simp [headResult, targetTailResult] at targetCompiled
                  subst sourceItems
                  subst targetItems
                  simp only [denoteItemSeq_cons]
                  constructor
                  · rintro ⟨headDenotes, tailDenotes⟩
                    exact ⟨headDenotes,
                      (induction sourceTailResult targetTailResult).mp
                        tailDenotes⟩
                  · rintro ⟨headDenotes, tailDenotes⟩
                    exact ⟨headDenotes,
                      (induction sourceTailResult targetTailResult).mpr
                        tailDenotes⟩
  | swap first second tail =>
      simp only [Concrete.Elaboration.compileOccurrencesWith?] at sourceCompiled targetCompiled
      cases firstResult :
          Concrete.Elaboration.compileOccurrenceWith?  diagram recurse
            context binders first with
      | none => simp [firstResult] at sourceCompiled
      | some firstItem =>
          cases secondResult :
              Concrete.Elaboration.compileOccurrenceWith?  diagram
                recurse context binders second with
          | none => simp [firstResult, secondResult] at sourceCompiled
          | some secondItem =>
              cases tailResult :
                  Concrete.Elaboration.compileOccurrencesWith?  diagram
                    recurse context binders tail with
              | none =>
                  simp [firstResult, secondResult, tailResult] at sourceCompiled
              | some tailItems =>
                  simp [firstResult, secondResult, tailResult] at sourceCompiled targetCompiled
                  subst sourceItems
                  subst targetItems
                  simp only [denoteItemSeq_cons]
                  constructor
                  · rintro ⟨firstDenotes, secondDenotes, tailDenotes⟩
                    exact ⟨secondDenotes, firstDenotes, tailDenotes⟩
                  · rintro ⟨secondDenotes, firstDenotes, tailDenotes⟩
                    exact ⟨firstDenotes, secondDenotes, tailDenotes⟩
  | trans firstPermutation secondPermutation firstInduction secondInduction =>
      obtain ⟨middleItems, middleCompiled⟩ :=
        Concrete.Elaboration.compileOccurrencesWith?_complete recurse context
          binders _ (by
            intro occurrence middleMember
            exact compileOccurrence_success_of_mem diagram recurse context
              binders sourceCompiled
              ((firstPermutation.mem_iff).mpr middleMember))
      have firstEquivalence :=
        firstInduction sourceCompiled middleCompiled
      have secondEquivalence :=
        secondInduction middleCompiled targetCompiled
      exact firstEquivalence.trans secondEquivalence

noncomputable def doubleCutIntroSimulation
    (input : Concrete.Checked )
    (selection : CheckedSelection input.val)
    (targetWellFormed :
      (doubleCutIntroRaw input.val selection).WellFormed )
    (model : Model)
    :
    Concrete.Elaboration.ConcreteSemanticSimulation  input.val
      (doubleCutIntroRaw input.val selection) model  where
  source_wellFormed := input.property
  target_wellFormed := targetWellFormed
  regionMap := Fin.castAdd 2
  binderMap := Fin.castAdd 2
  Distinguished := fun region => region = selection.val.anchor
  occurrenceMap := fun _ _ occurrence => liftOccurrence input.val occurrence
  occurrenceMap_node := by
    intro region regular node nodeRegion
    exact ⟨node, rfl⟩
  occurrenceMap_child := by
    intro region regular child
    rfl
  root_eq := doubleCutIntroRaw_root input.val selection
  region_shape := by
    intro parent regular child childParent
    exact doubleCutIntroRaw_regular_regionShape input.val selection parent child
      regular childParent
  localOccurrences_map := by
    intro region regular
    exact doubleCutIntroRaw_regular_localOccurrences input.val selection region
      regular
  BinderWitness := fun {sourceRels targetRels} sourceBinders targetBinders =>
    LiftedBinderWitness input.val selection
      (sourceRels := sourceRels) (targetRels := targetRels)
      sourceBinders targetBinders
  relationMap := fun witness => LiftedBinderWitness.relationMap witness
  binders_empty := {
    relationContexts_eq := rfl
    binders_eq := by
      intro region
      rfl
  }
  binders_push := by
    intro sourceRels targetRels sourceBinders targetBinders witness child parent
      arity childKind regular
    exact LiftedBinderWitness.push witness child parent arity
  relationMap_push := by
    intro sourceRels targetRels sourceBinders targetBinders witness child parent
      arity childKind regular
    exact LiftedBinderWitness.relationMap_push witness child parent arity
  Allowed := fun _ _ => True
  allowed_cut := by simp
  allowed_bubble := by simp
  ContextWitness := fun sourceContext targetContext =>
    LiftedContextWitness input.val selection sourceContext targetContext
  AtRegion := fun _ _ => True
  indexRelation := fun witness => LiftedContextWitness.indexRelation witness
  extendContext := by
    intro sourceContext targetContext witness region regular sourceExact
      targetExact
    exact LiftedContextWitness.extend witness region
  extendFocusedContext := by
    intro sourceContext targetContext witness region atRegion focused sourceExact
      targetExact
    exact LiftedContextWitness.extend witness region
  at_child := by simp
  at_extended := by simp
  at_focused_child := by simp
  localTransport := by
    intro sourceRels targetRels direction fuelSource fuelTarget sourceContext
      targetContext witness sourceBinders targetBinders binderWitness region
      atRegion regular allowed sourceExact targetExact sourceBindersCover
      targetBindersCover sourceEnumeration targetEnumeration sourceItems
      targetItems sourceCompiled targetCompiled itemSemantics
    rcases witness with ⟨contextsEq⟩
    cases contextsEq
    let extendedWitness :=
      LiftedContextWitness.extend
        (input := input.val) (selection := selection)
        (⟨rfl⟩ : LiftedContextWitness input.val selection
          sourceContext sourceContext)
        region
    cases binderWitness.relationContexts_eq
    have identityRelationRenamingEq :
        (Concrete.Elaboration.identityRelationRenaming sourceRels :
          RelationRenaming sourceRels sourceRels) =
            (fun {arity} (relation : RelVar sourceRels arity) => relation) :=
      rfl
    change ∀ relEnv,
      Concrete.Elaboration.DirectionalLocalTransport direction
        (source := input.val)
        (target := doubleCutIntroRaw input.val selection)
        sourceContext sourceContext region (Fin.castAdd 2 region)
        (Concrete.Elaboration.ContextIndexRelation.forwardMap id)
        model  relEnv
        (sourceItems.renameRelations
          (Concrete.Elaboration.identityRelationRenaming sourceRels))
        targetItems
    rw [identityRelationRenamingEq, ItemSeq.renameRelations_id]
    change Concrete.Elaboration.ItemSeqSimulation model  direction
      (LiftedContextWitness.indexRelation extendedWitness)
      (sourceItems.renameRelations
        (Concrete.Elaboration.identityRelationRenaming sourceRels))
      targetItems at itemSemantics
    rw [identityRelationRenamingEq, ItemSeq.renameRelations_id] at itemSemantics
    apply Concrete.Elaboration.directionalLocalTransport_of_agreement
      (source := input.val)
      (target := doubleCutIntroRaw input.val selection)
      direction sourceContext sourceContext region (Fin.castAdd 2 region)
      (Concrete.Elaboration.ContextIndexRelation.forwardMap id)
      (LiftedContextWitness.indexRelation extendedWitness)
      model  sourceItems targetItems
    · intro sourceOuter targetOuter outerAgrees
      have outerEq : sourceOuter = targetOuter := by
        simpa only [
          Concrete.Elaboration.ContextIndexRelation.environmentsAgree_forwardMap,
          Function.comp_id] using outerAgrees
      cases direction with
      | forward =>
          intro sourceLocal
          let localCountEq :
              (Concrete.Elaboration.exactScopeWires
                (doubleCutIntroRaw input.val selection)
                (Fin.castAdd 2 region)).length =
                (Concrete.Elaboration.exactScopeWires input.val region).length :=
            congrArg List.length
              (doubleCutIntroRaw_exactScopeWires input.val selection region)
          let targetLocal :
              Fin (Concrete.Elaboration.exactScopeWires
                (doubleCutIntroRaw input.val selection)
                (Fin.castAdd 2 region)).length → model.Carrier :=
            fun index => sourceLocal (Fin.cast localCountEq index)
          refine ⟨targetLocal, ?_⟩
          unfold LiftedContextWitness.indexRelation
            Concrete.Elaboration.ContextIndexRelation.EnvironmentsAgree
            Concrete.Elaboration.ContextIndexRelation.forwardMap
          intro sourceIndex targetIndex related
          subst targetIndex
          subst targetOuter
          simp only [Concrete.Elaboration.extendedEnvironment, targetLocal,
            Function.comp_apply, doubleCutIntroRaw_exactScopeWires]
          apply extendWireEnv_transport
            (countEq := localCountEq)
            (sourceLocal := sourceLocal) (targetLocal := targetLocal)
          · intro localIndex
            rfl
          · rfl
      | backward =>
          intro targetLocal
          let localCountEq :
              (Concrete.Elaboration.exactScopeWires
                (doubleCutIntroRaw input.val selection)
                (Fin.castAdd 2 region)).length =
                (Concrete.Elaboration.exactScopeWires input.val region).length :=
            congrArg List.length
              (doubleCutIntroRaw_exactScopeWires input.val selection region)
          let sourceLocal :
              Fin (Concrete.Elaboration.exactScopeWires input.val region).length →
                model.Carrier :=
            fun index => targetLocal (Fin.cast localCountEq.symm index)
          refine ⟨sourceLocal, ?_⟩
          unfold LiftedContextWitness.indexRelation
            Concrete.Elaboration.ContextIndexRelation.EnvironmentsAgree
            Concrete.Elaboration.ContextIndexRelation.forwardMap
          intro sourceIndex targetIndex related
          subst targetIndex
          subst targetOuter
          simp only [Concrete.Elaboration.extendedEnvironment, sourceLocal,
            Function.comp_apply, doubleCutIntroRaw_exactScopeWires]
          apply extendWireEnv_transport
            (countEq := localCountEq)
            (sourceLocal := sourceLocal) (targetLocal := targetLocal)
          · intro localIndex
            apply congrArg targetLocal
            apply Fin.ext
            rfl
          · rfl
    · exact itemSemantics
  nodeSemantic := by
    intro sourceRels targetRels direction region sourceContext targetContext
      witness atRegion sourceNodup targetNodup sourceBinders targetBinders
      allowed binderWitness sourceNode targetNode regular mapped nodeRegion
      sourceItem targetItem sourceCompiled targetCompiled
    rcases witness with ⟨contextsEq⟩
    cases contextsEq
    have targetNodeEq : targetNode = sourceNode :=
      Concrete.Elaboration.LocalOccurrence.node.inj mapped.symm
    subst targetNode
    apply Concrete.Elaboration.compileNode?_itemSimulation_of_related_ports
      (source := input.val)
      (target := doubleCutIntroRaw input.val selection)
      model  direction sourceContext sourceContext
      (Concrete.Elaboration.ContextIndexRelation.forwardMap id)
      sourceBinders targetBinders
      (LiftedBinderWitness.relationMap binderWitness)
      sourceNode sourceNode
      (regionMap := Fin.castAdd 2)
      (binderMap := Fin.castAdd 2)
    · exact doubleCutIntroRaw_regular_nodeShape input.val selection region
        regular sourceNode nodeRegion
    · intro port sourceIndex targetIndex sourceResolved targetResolved
      have resolved := doubleCutIntroRaw_resolvePort input.val selection
        sourceContext sourceContext ⟨rfl⟩ sourceNode port
      rw [sourceResolved, targetResolved] at resolved
      change sourceIndex = targetIndex
      apply Fin.ext
      exact congrArg Fin.val (Option.some.inj resolved).symm
    · intro nodeOwner binder arity sourceRelation sourceAtom sourceLookup
      cases binderWitness.relationContexts_eq
      simpa [LiftedBinderWitness.relationMap] using
        (eq_of_heq (binderWitness.binders_eq binder)).symm.trans sourceLookup
    · exact sourceCompiled
    · exact targetCompiled
  focusedRegionKernel := by
    intro sourceRels targetRels direction fuelSource fuelTarget region
      sourceContext targetContext witness sourceBinders targetBinders atRegion
      focused allowed binderWitness sourceExact targetExact sourceBindersCover
      targetBindersCover sourceEnumeration targetEnumeration recurse recurseAt
      sourceItems targetItems sourceCompiled targetCompiled
    subst region
    cases binderWitness.relationContexts_eq
    rw [doubleCutIntroRaw_anchor_localOccurrences] at targetCompiled
    obtain ⟨keptTargetItems, outerTargetItems, keptTargetCompiled,
        outerTargetCompiled, targetItemsEq⟩ :=
      Concrete.Elaboration.compileOccurrencesWith?_append_split
        (d := doubleCutIntroRaw input.val selection)

        (fun {rels} =>
          Concrete.Elaboration.compileRegion?
            (doubleCutIntroRaw input.val selection) fuelTarget)
        (targetContext.extend (Fin.castAdd 2 selection.val.anchor))
        targetBinders
        ((keptOccurrences input.val selection).map
          (liftOccurrence input.val))
        [Concrete.Elaboration.LocalOccurrence.child
          (doubleCutOuter input.val)]
        targetItems targetCompiled
    rw [targetItemsEq]
    simp only [Concrete.Elaboration.compileOccurrencesWith?] at outerTargetCompiled
    simp only [Concrete.Elaboration.compileOccurrenceWith?,
      doubleCutIntroRaw_outer] at outerTargetCompiled
    cases outerRegionResult :
        Concrete.Elaboration.compileRegion?
          (doubleCutIntroRaw input.val selection) fuelTarget
          (doubleCutOuter input.val)
          (targetContext.extend (Fin.castAdd 2 selection.val.anchor))
          targetBinders with
    | none => simp [outerRegionResult] at outerTargetCompiled
    | some outerBody =>
        simp [outerRegionResult] at outerTargetCompiled
        subst outerTargetItems
        cases fuelTarget with
        | zero =>
            simp [Concrete.Elaboration.compileRegion?] at outerRegionResult
        | succ outerFuel =>
            simp only [Concrete.Elaboration.compileRegion?] at outerRegionResult
            rw [doubleCutIntroRaw_outer_localOccurrences] at outerRegionResult
            obtain ⟨outerItems, outerItemsResult, outerBodyEq⟩ :=
              Option.bind_eq_some_iff.mp outerRegionResult
            have outerBodyEq' :
                Concrete.Elaboration.finishRegion
                    (doubleCutIntroRaw input.val selection)
                    (targetContext.extend
                      (Fin.castAdd 2 selection.val.anchor))
                    (doubleCutOuter input.val) outerItems =
                  outerBody :=
              Option.some.inj outerBodyEq
            subst outerBody
            simp only [Concrete.Elaboration.compileOccurrencesWith?,
              Concrete.Elaboration.compileOccurrenceWith?,
              doubleCutIntroRaw_inner] at outerItemsResult
            cases innerRegionResult :
                Concrete.Elaboration.compileRegion?
                  (doubleCutIntroRaw input.val selection) outerFuel
                  (doubleCutInner input.val)
                  ((targetContext.extend
                    (Fin.castAdd 2 selection.val.anchor)).extend
                      (doubleCutOuter input.val))
                  targetBinders with
            | none => simp [innerRegionResult] at outerItemsResult
            | some innerBody =>
                simp [innerRegionResult] at outerItemsResult
                subst outerItems
                cases outerFuel with
                | zero =>
                    simp [Concrete.Elaboration.compileRegion?] at innerRegionResult
                | succ innerFuel =>
                    simp only [Concrete.Elaboration.compileRegion?] at innerRegionResult
                    rw [doubleCutIntroRaw_inner_localOccurrences] at innerRegionResult
                    obtain ⟨selectedTargetItems, selectedTargetCompiled,
                        innerBodyEq⟩ :=
                      Option.bind_eq_some_iff.mp innerRegionResult
                    have innerBodyEq' :
                        Concrete.Elaboration.finishRegion
                            (doubleCutIntroRaw input.val selection)
                            ((targetContext.extend
                              (Fin.castAdd 2 selection.val.anchor)).extend
                                (doubleCutOuter input.val))
                            (doubleCutInner input.val)
                            selectedTargetItems =
                          innerBody :=
                      Option.some.inj innerBodyEq
                    subst innerBody
                    let sourceRecurse :
                        ∀ {rels : RelCtx},
                          (child : Fin input.val.regionCount) →
                          (childContext :
                            Concrete.Elaboration.WireContext input.val) →
                          Concrete.Elaboration.BinderContext input.val rels →
                          Option
                            (Region  childContext.length rels) :=
                      fun {rels} =>
                        Concrete.Elaboration.compileRegion?  input.val
                          fuelSource
                    obtain ⟨partitionSourceItems, partitionSourceCompiled⟩ :=
                      Concrete.Elaboration.compileOccurrencesWith?_complete
                        sourceRecurse
                        (sourceContext.extend selection.val.anchor)
                        sourceBinders
                        (keptOccurrences input.val selection ++
                          selectedOccurrences input.val selection)
                        (by
                          intro occurrence member
                          exact compileOccurrence_success_of_mem input.val
                            sourceRecurse
                            (sourceContext.extend selection.val.anchor)
                            sourceBinders sourceCompiled
                            ((anchorOccurrences_perm_partition input.val
                              selection).mem_iff.mp member))
                    obtain ⟨keptSourceItems, selectedSourceItems,
                        keptSourceCompiled, selectedSourceCompiled,
                        partitionSourceItemsEq⟩ :=
                      Concrete.Elaboration.compileOccurrencesWith?_append_split
                        sourceRecurse
                        (sourceContext.extend selection.val.anchor)
                        sourceBinders
                        (keptOccurrences input.val selection)
                        (selectedOccurrences input.val selection)
                        partitionSourceItems partitionSourceCompiled
                    have keptPointwise :
                        ∀ occurrence,
                          occurrence ∈ keptOccurrences input.val selection →
                          ∀ (sourceItem :
                              Item
                                (sourceContext.extend
                                  selection.val.anchor).length sourceRels)
                            (targetItem :
                              Item
                                (targetContext.extend
                                  (Fin.castAdd 2
                                    selection.val.anchor)).length sourceRels),
                          Concrete.Elaboration.compileOccurrenceWith?
                               input.val sourceRecurse
                              (sourceContext.extend selection.val.anchor)
                              sourceBinders occurrence =
                            some sourceItem →
                          Concrete.Elaboration.compileOccurrenceWith?

                              (doubleCutIntroRaw input.val selection)
                              (Concrete.Elaboration.compileRegion?
                                (doubleCutIntroRaw input.val selection)
                                (innerFuel + 1 + 1))
                              (targetContext.extend
                                (Fin.castAdd 2 selection.val.anchor))
                              targetBinders
                              (liftOccurrence input.val occurrence) =
                            some targetItem →
                          Concrete.Elaboration.ItemSimulation model
                            direction
                            (witness.extend
                              selection.val.anchor).indexRelation
                            (sourceItem.renameRelations
                              binderWitness.relationMap)
                            targetItem := by
                      intro occurrence keptMember sourceItem targetItem
                        sourceOccurrenceCompiled targetOccurrenceCompiled
                      have filteredMember := keptMember
                      rw [keptOccurrences] at filteredMember
                      have sourceMember :=
                        (List.mem_filter.mp filteredMember).1
                      apply doubleCutIntro_compileOccurrence_itemSimulation
                        input.val selection input.property targetWellFormed
                        model  direction fuelSource
                        (innerFuel + 1 + 1)
                        selection.val.anchor
                        (Fin.castAdd 2 selection.val.anchor)
                        (sourceContext.extend selection.val.anchor)
                        (targetContext.extend
                          (Fin.castAdd 2 selection.val.anchor))
                        (witness.extend selection.val.anchor)
                        sourceBinders targetBinders binderWitness
                        sourceExact targetExact sourceBindersCover
                        targetBindersCover sourceEnumeration targetEnumeration
                        occurrence (Fin.castAdd 2)
                      · intro node occurrenceEq
                        cases occurrenceEq
                        have unselected :=
                          (List.mem_filter.mp filteredMember).2
                        simpa [occurrenceSelected] using
                          (doubleCutIntroRaw_unselected_nodeShape input.val
                            selection node (by
                              simpa [occurrenceSelected] using unselected))
                      · intro child occurrenceEq childParent
                        cases occurrenceEq
                        have unselected :=
                          (List.mem_filter.mp filteredMember).2
                        have shape :=
                          doubleCutIntroRaw_unselected_regionShape input.val
                            selection child (by
                              simpa [occurrenceSelected] using unselected)
                        cases childKind : input.val.regions child with
                        | sheet =>
                            rw [childKind] at childParent
                            simp [CRegion.parent?] at childParent
                        | cut parent =>
                            have parentEq : parent =
                                selection.val.anchor := by
                              rw [childKind] at childParent
                              exact Option.some.inj childParent
                            subst parent
                            simpa [childKind] using shape
                        | bubble parent arity =>
                            have parentEq : parent =
                                selection.val.anchor := by
                              rw [childKind] at childParent
                              exact Option.some.inj childParent
                            subst parent
                            simpa [childKind] using shape
                      · exact recurseAt
                      · exact sourceMember
                      · simpa [sourceRecurse] using sourceOccurrenceCompiled
                      · exact targetOccurrenceCompiled
                    have targetOuterExact :=
                      targetExact.extend_child targetWellFormed
                        (doubleCutIntroRaw_outer_parent input.val selection)
                    have targetInnerExact :=
                      targetOuterExact.extend_child targetWellFormed
                        (doubleCutIntroRaw_inner_parent input.val selection)
                    have targetOuterBindersCover :=
                      Concrete.Elaboration.BinderContext.covers_cut_child
                        targetBindersCover
                        (doubleCutIntroRaw_outer input.val selection)
                    have targetInnerBindersCover :=
                      Concrete.Elaboration.BinderContext.covers_cut_child
                        targetOuterBindersCover
                        (doubleCutIntroRaw_inner input.val selection)
                    have targetOuterEnumeration :=
                      targetEnumeration.cutChild targetWellFormed
                        (doubleCutIntroRaw_outer input.val selection)
                    have targetInnerEnumeration :=
                      targetOuterEnumeration.cutChild targetWellFormed
                        (doubleCutIntroRaw_inner input.val selection)
                    have targetOuterContextEq :
                        (targetContext.extend
                          (Fin.castAdd 2 selection.val.anchor)).extend
                            (doubleCutOuter input.val) =
                          targetContext.extend
                            (Fin.castAdd 2 selection.val.anchor) := by
                      unfold Concrete.Elaboration.WireContext.extend
                      rw [doubleCutIntroRaw_outer_exactScopeWires]
                      exact List.append_nil _
                    have selectedTargetContextEq :
                        (((targetContext.extend
                          (Fin.castAdd 2 selection.val.anchor)).extend
                            (doubleCutOuter input.val)).extend
                              (doubleCutInner input.val)) =
                          targetContext.extend
                            (Fin.castAdd 2 selection.val.anchor) := by
                      apply Eq.trans _ targetOuterContextEq
                      unfold Concrete.Elaboration.WireContext.extend
                      rw [doubleCutIntroRaw_inner_exactScopeWires]
                      exact List.append_nil _
                    have selectedContextWitness :
                        LiftedContextWitness input.val selection
                          (sourceContext.extend selection.val.anchor)
                          (((targetContext.extend
                            (Fin.castAdd 2 selection.val.anchor)).extend
                              (doubleCutOuter input.val)).extend
                                (doubleCutInner input.val)) := by
                      exact ⟨(witness.extend
                        selection.val.anchor).contexts_eq.trans
                          selectedTargetContextEq.symm⟩
                    have selectedPointwise :
                        ∀ occurrence,
                          occurrence ∈ selectedOccurrences input.val selection →
                          ∀ (sourceItem :
                              Item
                                (sourceContext.extend
                                  selection.val.anchor).length sourceRels)
                            (targetItem :
                              Item
                                (((targetContext.extend
                                  (Fin.castAdd 2
                                    selection.val.anchor)).extend
                                      (doubleCutOuter input.val)).extend
                                        (doubleCutInner input.val)).length
                                sourceRels),
                          Concrete.Elaboration.compileOccurrenceWith?
                               input.val sourceRecurse
                              (sourceContext.extend selection.val.anchor)
                              sourceBinders occurrence =
                            some sourceItem →
                          Concrete.Elaboration.compileOccurrenceWith?

                              (doubleCutIntroRaw input.val selection)
                              (Concrete.Elaboration.compileRegion?
                                (doubleCutIntroRaw input.val selection)
                                innerFuel)
                              (((targetContext.extend
                                (Fin.castAdd 2
                                  selection.val.anchor)).extend
                                    (doubleCutOuter input.val)).extend
                                      (doubleCutInner input.val))
                              targetBinders
                              (liftOccurrence input.val occurrence) =
                            some targetItem →
                          Concrete.Elaboration.ItemSimulation model
                            direction selectedContextWitness.indexRelation
                            (sourceItem.renameRelations
                              binderWitness.relationMap)
                            targetItem := by
                      intro occurrence selectedMember sourceItem targetItem
                        sourceOccurrenceCompiled targetOccurrenceCompiled
                      have filteredMember := selectedMember
                      rw [selectedOccurrences] at filteredMember
                      have sourceMember :=
                        (List.mem_filter.mp filteredMember).1
                      apply doubleCutIntro_compileOccurrence_itemSimulation
                        input.val selection input.property targetWellFormed
                        model  direction fuelSource innerFuel
                        selection.val.anchor (doubleCutInner input.val)
                        (sourceContext.extend selection.val.anchor)
                        (((targetContext.extend
                          (Fin.castAdd 2 selection.val.anchor)).extend
                            (doubleCutOuter input.val)).extend
                              (doubleCutInner input.val))
                        selectedContextWitness sourceBinders targetBinders
                        binderWitness sourceExact targetInnerExact
                        sourceBindersCover targetInnerBindersCover
                        sourceEnumeration targetInnerEnumeration occurrence
                        (fun _ => doubleCutInner input.val)
                      · intro node occurrenceEq
                        cases occurrenceEq
                        have selected :=
                          (List.mem_filter.mp filteredMember).2
                        exact doubleCutIntroRaw_selected_nodeShape input.val
                          selection node (by
                            simpa [occurrenceSelected] using selected)
                      · intro child occurrenceEq childParent
                        cases occurrenceEq
                        have selected :=
                          (List.mem_filter.mp filteredMember).2
                        exact doubleCutIntroRaw_selected_regionShape input.val
                          selection child (by
                            simpa [occurrenceSelected] using selected)
                      · exact recurseAt
                      · exact sourceMember
                      · simpa [sourceRecurse] using sourceOccurrenceCompiled
                      · exact targetOccurrenceCompiled
                    have keptSimulation :=
                      Concrete.Elaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
                        model  direction sourceRecurse
                        (Concrete.Elaboration.compileRegion?
                          (doubleCutIntroRaw input.val selection)
                          (innerFuel + 1 + 1))
                        (sourceContext.extend selection.val.anchor)
                        (targetContext.extend
                          (Fin.castAdd 2 selection.val.anchor))
                        sourceBinders targetBinders
                        (witness.extend selection.val.anchor).indexRelation
                        binderWitness.relationMap
                        (liftOccurrence input.val)
                        (keptOccurrences input.val selection)
                        keptPointwise keptSourceItems keptTargetItems
                        keptSourceCompiled keptTargetCompiled
                    have selectedSimulation :=
                      Concrete.Elaboration.ConcreteSemanticSimulation.compileOccurrences_denote_of_pointwise
                        model  direction sourceRecurse
                        (Concrete.Elaboration.compileRegion?
                          (doubleCutIntroRaw input.val selection) innerFuel)
                        (sourceContext.extend selection.val.anchor)
                        (((targetContext.extend
                          (Fin.castAdd 2 selection.val.anchor)).extend
                            (doubleCutOuter input.val)).extend
                              (doubleCutInner input.val))
                        sourceBinders targetBinders
                        selectedContextWitness.indexRelation
                        binderWitness.relationMap
                        (liftOccurrence input.val)
                        (selectedOccurrences input.val selection)
                        selectedPointwise selectedSourceItems
                        selectedTargetItems selectedSourceCompiled
                        selectedTargetCompiled
                    have nestedDenotes
                        (targetEnv : Fin
                          (targetContext.extend
                            (Fin.castAdd 2
                              selection.val.anchor)).length →
                            model.Carrier)
                        (relEnv : RelEnv model.Carrier sourceRels) :
                        denoteItem model  targetEnv relEnv
                            (.cut
                              (Concrete.Elaboration.finishRegion
                                (doubleCutIntroRaw input.val selection)
                                (targetContext.extend
                                  (Fin.castAdd 2 selection.val.anchor))
                                (doubleCutOuter input.val)
                                (.cons
                                  (.cut
                                    (Concrete.Elaboration.finishRegion
                                      (doubleCutIntroRaw input.val selection)
                                      ((targetContext.extend
                                        (Fin.castAdd 2
                                          selection.val.anchor)).extend
                                            (doubleCutOuter input.val))
                                      (doubleCutInner input.val)
                                      selectedTargetItems))
                                  .nil))) ↔
                          denoteItemSeq model
                            (fun index =>
                              targetEnv (Fin.cast
                                (congrArg List.length
                                  selectedTargetContextEq) index))
                            relEnv selectedTargetItems := by
                      rw [cut_denotes_negation]
                      rw [finishRegion_noWires_denote
                        (doubleCutIntroRaw input.val selection)
                        (targetContext.extend
                          (Fin.castAdd 2 selection.val.anchor))
                        (doubleCutOuter input.val)
                        (doubleCutIntroRaw_outer_exactScopeWires
                          input.val selection)]
                      rw [ItemSeq.castWiresEq_eq_renameWires,
                        denoteItemSeq_renameWires]
                      simp only [denoteItemSeq_cons, denoteItemSeq_nil,
                        and_true, cut_denotes_negation]
                      rw [Classical.not_not]
                      rw [finishRegion_noWires_denote
                        (doubleCutIntroRaw input.val selection)
                        ((targetContext.extend
                          (Fin.castAdd 2 selection.val.anchor)).extend
                            (doubleCutOuter input.val))
                        (doubleCutInner input.val)
                        (doubleCutIntroRaw_inner_exactScopeWires
                          input.val selection)]
                      rw [ItemSeq.castWiresEq_eq_renameWires,
                        denoteItemSeq_renameWires]
                      apply iff_of_eq
                      apply congrArg (fun environment =>
                        denoteItemSeq model  environment relEnv
                          selectedTargetItems)
                      funext index
                      apply congrArg targetEnv
                      apply Fin.ext
                      rfl
                    have relationMapEq :
                        (binderWitness.relationMap :
                          RelationRenaming sourceRels sourceRels) =
                            (fun {arity}
                              (relation : RelVar sourceRels arity) =>
                                relation) := by
                      rfl
                    rw [relationMapEq, ItemSeq.renameRelations_id] at keptSimulation selectedSimulation
                    have focusedItemsSimulation :
                        Concrete.Elaboration.ItemSeqSimulation model
                          direction
                          (witness.extend
                            selection.val.anchor).indexRelation
                          sourceItems
                          (keptTargetItems.append
                            (.cons
                              (.cut
                                (Concrete.Elaboration.finishRegion
                                  (doubleCutIntroRaw input.val selection)
                                  (targetContext.extend
                                    (Fin.castAdd 2
                                      selection.val.anchor))
                                  (doubleCutOuter input.val)
                                  (.cons
                                    (.cut
                                      (Concrete.Elaboration.finishRegion
                                        (doubleCutIntroRaw input.val selection)
                                        ((targetContext.extend
                                          (Fin.castAdd 2
                                            selection.val.anchor)).extend
                                              (doubleCutOuter input.val))
                                        (doubleCutInner input.val)
                                        selectedTargetItems))
                                    .nil)))
                              .nil)) := by
                      intro sourceEnv targetEnv relEnv environments
                      have sourcePartition :=
                        compileOccurrences_denote_perm input.val sourceRecurse
                          (sourceContext.extend selection.val.anchor)
                          sourceBinders
                          (anchorOccurrences_perm_partition input.val
                            selection).symm
                          sourceCompiled partitionSourceCompiled
                          model  sourceEnv relEnv
                      rw [partitionSourceItemsEq,
                        denoteItemSeq_append] at sourcePartition
                      have keptEntailment :=
                        keptSimulation sourceEnv targetEnv relEnv environments
                      let selectedTargetEnv :
                          Fin
                            (((targetContext.extend
                              (Fin.castAdd 2
                                selection.val.anchor)).extend
                                  (doubleCutOuter input.val)).extend
                                    (doubleCutInner input.val)).length →
                              model.Carrier :=
                        fun index =>
                          targetEnv (Fin.cast
                            (congrArg List.length
                              selectedTargetContextEq) index)
                      have selectedEnvironments :
                          selectedContextWitness.indexRelation.EnvironmentsAgree
                            sourceEnv selectedTargetEnv := by
                        unfold LiftedContextWitness.indexRelation
                          Concrete.Elaboration.ContextIndexRelation.EnvironmentsAgree
                          Concrete.Elaboration.ContextIndexRelation.forwardMap
                        intro sourceIndex targetIndex related
                        subst targetIndex
                        have base := environments sourceIndex
                          (Fin.cast
                            (congrArg List.length
                              (witness.extend
                                selection.val.anchor).contexts_eq)
                            sourceIndex)
                          rfl
                        exact base.trans (by
                          apply congrArg targetEnv
                          apply Fin.ext
                          rfl)
                      have selectedEntailment :=
                        selectedSimulation sourceEnv selectedTargetEnv relEnv
                          selectedEnvironments
                      rw [denoteItemSeq_append, denoteItemSeq_cons,
                        denoteItemSeq_nil, and_true]
                      cases direction with
                      | forward =>
                          intro sourceDenotes
                          have partitionDenotes :=
                            sourcePartition.mp sourceDenotes
                          exact ⟨keptEntailment partitionDenotes.1,
                            (nestedDenotes targetEnv relEnv).mpr
                              (selectedEntailment partitionDenotes.2)⟩
                      | backward =>
                          rintro ⟨keptDenotes, nestedDenotesTarget⟩
                          apply sourcePartition.mpr
                          exact ⟨keptEntailment keptDenotes,
                            selectedEntailment
                              ((nestedDenotes targetEnv relEnv).mp
                                nestedDenotesTarget)⟩
                    rw [relationMapEq, Region.renameRelations_id]
                    rcases witness with ⟨contextsEq⟩
                    cases contextsEq
                    let extendedWitness :=
                      LiftedContextWitness.extend
                        (input := input.val) (selection := selection)
                        (⟨rfl⟩ : LiftedContextWitness input.val selection
                          sourceContext sourceContext)
                        selection.val.anchor
                    apply Concrete.Elaboration.finishRegion_denote
                      (source := input.val)
                      (target := doubleCutIntroRaw input.val selection)
                      direction sourceContext sourceContext
                      selection.val.anchor
                      (Fin.castAdd 2 selection.val.anchor)
                      (Concrete.Elaboration.ContextIndexRelation.forwardMap id)
                      model
                    intro relEnv
                    apply Concrete.Elaboration.directionalLocalTransport_of_agreement
                      (source := input.val)
                      (target := doubleCutIntroRaw input.val selection)
                      direction sourceContext sourceContext
                      selection.val.anchor
                      (Fin.castAdd 2 selection.val.anchor)
                      (Concrete.Elaboration.ContextIndexRelation.forwardMap id)
                      extendedWitness.indexRelation
                      model
                    · intro sourceOuter targetOuter outerAgrees
                      have outerEq : sourceOuter = targetOuter := by
                        simpa only [
                          Concrete.Elaboration.ContextIndexRelation.environmentsAgree_forwardMap,
                          Function.comp_id] using outerAgrees
                      cases direction with
                      | forward =>
                          intro sourceLocal
                          let localCountEq :
                              (Concrete.Elaboration.exactScopeWires
                                (doubleCutIntroRaw input.val selection)
                                (Fin.castAdd 2
                                  selection.val.anchor)).length =
                                (Concrete.Elaboration.exactScopeWires input.val
                                  selection.val.anchor).length :=
                            congrArg List.length
                              (doubleCutIntroRaw_exactScopeWires input.val
                                selection selection.val.anchor)
                          let targetLocal :
                              Fin
                                (Concrete.Elaboration.exactScopeWires
                                  (doubleCutIntroRaw input.val selection)
                                  (Fin.castAdd 2
                                    selection.val.anchor)).length →
                                model.Carrier :=
                            fun index =>
                              sourceLocal (Fin.cast localCountEq index)
                          refine ⟨targetLocal, ?_⟩
                          unfold LiftedContextWitness.indexRelation
                            Concrete.Elaboration.ContextIndexRelation.EnvironmentsAgree
                            Concrete.Elaboration.ContextIndexRelation.forwardMap
                          intro sourceIndex targetIndex related
                          subst targetIndex
                          subst targetOuter
                          simp only [
                            Concrete.Elaboration.extendedEnvironment,
                            targetLocal, Function.comp_apply,
                            doubleCutIntroRaw_exactScopeWires]
                          apply extendWireEnv_transport
                            (countEq := localCountEq)
                            (sourceLocal := sourceLocal)
                            (targetLocal := targetLocal)
                          · intro localIndex
                            rfl
                          · rfl
                      | backward =>
                          intro targetLocal
                          let localCountEq :
                              (Concrete.Elaboration.exactScopeWires
                                (doubleCutIntroRaw input.val selection)
                                (Fin.castAdd 2
                                  selection.val.anchor)).length =
                                (Concrete.Elaboration.exactScopeWires input.val
                                  selection.val.anchor).length :=
                            congrArg List.length
                              (doubleCutIntroRaw_exactScopeWires input.val
                                selection selection.val.anchor)
                          let sourceLocal :
                              Fin
                                (Concrete.Elaboration.exactScopeWires input.val
                                  selection.val.anchor).length →
                                model.Carrier :=
                            fun index =>
                              targetLocal (Fin.cast localCountEq.symm index)
                          refine ⟨sourceLocal, ?_⟩
                          unfold LiftedContextWitness.indexRelation
                            Concrete.Elaboration.ContextIndexRelation.EnvironmentsAgree
                            Concrete.Elaboration.ContextIndexRelation.forwardMap
                          intro sourceIndex targetIndex related
                          subst targetIndex
                          subst targetOuter
                          simp only [
                            Concrete.Elaboration.extendedEnvironment,
                            sourceLocal, Function.comp_apply,
                            doubleCutIntroRaw_exactScopeWires]
                          apply extendWireEnv_transport
                            (countEq := localCountEq)
                            (sourceLocal := sourceLocal)
                            (targetLocal := targetLocal)
                          · intro localIndex
                            apply congrArg targetLocal
                            apply Fin.ext
                            rfl
                          · rfl
                    · exact focusedItemsSimulation

end VisualProof.Rule.ModalSoundness
