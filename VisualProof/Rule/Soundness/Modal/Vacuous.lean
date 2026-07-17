import VisualProof.Rule.Soundness.Modal

namespace VisualProof.Rule.VacuousSoundness

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram

def bubbleRegion (input : ConcreteDiagram) :
    Fin (input.regionCount + 1) :=
  Fin.last input.regionCount

@[simp] theorem vacuousIntroRaw_regionCount
    (input : ConcreteDiagram) (selection : CheckedSelection input)
    (arity : Nat) :
    (vacuousIntroRaw input selection arity).regionCount =
      input.regionCount + 1 := rfl

@[simp] theorem vacuousIntroRaw_nodeCount
    (input : ConcreteDiagram) (selection : CheckedSelection input)
    (arity : Nat) :
    (vacuousIntroRaw input selection arity).nodeCount = input.nodeCount := rfl

@[simp] theorem vacuousIntroRaw_wireCount
    (input : ConcreteDiagram) (selection : CheckedSelection input)
    (arity : Nat) :
    (vacuousIntroRaw input selection arity).wireCount = input.wireCount := rfl

@[simp] theorem vacuousIntroRaw_root
    (input : ConcreteDiagram) (selection : CheckedSelection input)
    (arity : Nat) :
    (vacuousIntroRaw input selection arity).root = input.root.castSucc := rfl

@[simp] theorem vacuousIntroRaw_wire
    (input : ConcreteDiagram) (selection : CheckedSelection input)
    (arity : Nat) (wire : Fin input.wireCount) :
    (vacuousIntroRaw input selection arity).wires wire =
      liftCWireRegions 1 (input.wires wire) := rfl

theorem bubbleRegion_ne_lift
    (input : ConcreteDiagram) (region : Fin input.regionCount) :
    bubbleRegion input ≠ region.castSucc := by
  intro equality
  have values := congrArg Fin.val equality
  simp [bubbleRegion] at values
  omega

theorem vacuousIntroRaw_node
    (input : ConcreteDiagram) (selection : CheckedSelection input)
    (arity : Nat) (node : Fin input.nodeCount) :
    (vacuousIntroRaw input selection arity).nodes node =
      if node ∈ selection.val.directNodes then
        reparentLiftedNode 1 (bubbleRegion input) (input.nodes node)
      else liftCNode 1 (input.nodes node) := rfl

theorem vacuousIntroRaw_oldRegion
    (input : ConcreteDiagram) (selection : CheckedSelection input)
    (arity : Nat) (region : Fin input.regionCount) :
    (vacuousIntroRaw input selection arity).regions region.castSucc =
      if region ∈ selection.val.childRoots then
        reparentLiftedRegion 1 (bubbleRegion input) (input.regions region)
      else liftCRegion 1 (input.regions region) := by
  simp only [vacuousIntroRaw, Fin.lastCases_castSucc]
  rfl

@[simp] theorem vacuousIntroRaw_bubble
    (input : ConcreteDiagram) (selection : CheckedSelection input)
    (arity : Nat) :
    (vacuousIntroRaw input selection arity).regions (bubbleRegion input) =
      .bubble selection.val.anchor.castSucc arity := by
  simp [vacuousIntroRaw, bubbleRegion]

theorem vacuousIntroRaw_node_region
    (input : ConcreteDiagram) (selection : CheckedSelection input)
    (arity : Nat) (node : Fin input.nodeCount) :
    ((vacuousIntroRaw input selection arity).nodes node).region =
      if node ∈ selection.val.directNodes then bubbleRegion input
      else (input.nodes node).region.castSucc := by
  rw [vacuousIntroRaw_node]
  split <;> cases input.nodes node <;> rfl

theorem vacuousIntroRaw_oldRegion_parent
    (input : ConcreteDiagram) (selection : CheckedSelection input)
    (arity : Nat) (region : Fin input.regionCount) :
    ((vacuousIntroRaw input selection arity).regions
      region.castSucc).parent? =
      if region ∈ selection.val.childRoots then some (bubbleRegion input)
      else (input.regions region).parent?.map Fin.castSucc := by
  rw [vacuousIntroRaw_oldRegion]
  by_cases selected : region ∈ selection.val.childRoots
  · simp only [if_pos selected]
    have direct := selection.property.childRoots_direct region selected
    cases shape : input.regions region with
    | sheet =>
        rw [shape] at direct
        simp only [CRegion.parent?] at direct
        cases direct
    | cut => rfl
    | bubble => rfl
  · simp only [if_neg selected]
    cases input.regions region <;> rfl

@[simp] theorem vacuousIntroRaw_bubble_parent
    (input : ConcreteDiagram) (selection : CheckedSelection input)
    (arity : Nat) :
    ((vacuousIntroRaw input selection arity).regions
      (bubbleRegion input)).parent? = some selection.val.anchor.castSucc := by
  rw [vacuousIntroRaw_bubble]
  rfl

@[simp] theorem vacuousIntroRaw_exactScopeWires
    (input : ConcreteDiagram) (selection : CheckedSelection input)
    (arity : Nat) (region : Fin input.regionCount) :
    ConcreteElaboration.exactScopeWires
      (vacuousIntroRaw input selection arity) region.castSucc =
        ConcreteElaboration.exactScopeWires input region := by
  unfold ConcreteElaboration.exactScopeWires
  apply congrArg filterFin
  funext wire
  apply Bool.eq_iff_iff.mpr
  simp only [vacuousIntroRaw_wire, liftCWireRegions, decide_eq_true_eq,
    Fin.ext_iff]
  constructor <;> intro equality
  · exact congrArg
      (fun value : Fin (input.regionCount + 1) => value.val) equality
  · apply Fin.ext
    exact equality

@[simp] theorem vacuousIntroRaw_bubble_exactScopeWires
    (input : ConcreteDiagram) (selection : CheckedSelection input)
    (arity : Nat) :
    ConcreteElaboration.exactScopeWires
      (vacuousIntroRaw input selection arity) (bubbleRegion input) = [] := by
  unfold ConcreteElaboration.exactScopeWires filterFin
  rw [show allFin (vacuousIntroRaw input selection arity).wireCount =
      allFin input.wireCount by rfl]
  apply List.filter_eq_nil_iff.mpr
  intro wire _ selected
  have equality := decide_eq_true_eq.mp selected
  exact bubbleRegion_ne_lift input (input.wires wire).scope equality.symm

def liftOccurrence (input : ConcreteDiagram) :
    ConcreteElaboration.LocalOccurrence input.regionCount input.nodeCount →
      ConcreteElaboration.LocalOccurrence (input.regionCount + 1)
        input.nodeCount
  | .node node => .node node
  | .child child => .child child.castSucc

structure LiftedContextWitness
    (input : ConcreteDiagram) (selection : CheckedSelection input)
    (arity : Nat)
    (sourceContext : ConcreteElaboration.WireContext input)
    (targetContext : ConcreteElaboration.WireContext
      (vacuousIntroRaw input selection arity)) : Type where
  contexts_eq : sourceContext = targetContext

namespace LiftedContextWitness

def indexRelation
    (witness : LiftedContextWitness input selection arity
      sourceContext targetContext) :
    ConcreteElaboration.ContextIndexRelation sourceContext.length
      targetContext.length :=
  ConcreteElaboration.ContextIndexRelation.forwardMap
    (Fin.cast (congrArg List.length witness.contexts_eq))

def extend
    (witness : LiftedContextWitness input selection arity
      sourceContext targetContext)
    (region : Fin input.regionCount) :
    LiftedContextWitness input selection arity
      (sourceContext.extend region) (targetContext.extend region.castSucc) := by
  rcases witness with ⟨rfl⟩
  refine ⟨?_⟩
  simp only [ConcreteElaboration.WireContext.extend,
    vacuousIntroRaw_exactScopeWires]
  rfl

end LiftedContextWitness

structure LiftedBinderWitness
    (input : ConcreteDiagram) (selection : CheckedSelection input)
    (arity : Nat) {sourceRels targetRels : RelCtx}
    (sourceBinders : ConcreteElaboration.BinderContext input sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext
      (vacuousIntroRaw input selection arity) targetRels) : Type where
  relationContexts_eq : sourceRels = targetRels
  binders_eq : ∀ region,
    HEq (sourceBinders region) (targetBinders region.castSucc)

namespace LiftedBinderWitness

def relationMap
    (witness : LiftedBinderWitness input selection arity
      (sourceRels := sourceRels) (targetRels := targetRels)
      sourceBinders targetBinders) : RelationRenaming sourceRels targetRels := by
  cases witness.relationContexts_eq
  exact ConcreteElaboration.identityRelationRenaming sourceRels

def push
    (witness : LiftedBinderWitness input selection arity
      sourceBinders targetBinders)
    (child : Fin input.regionCount) (binderArity : Nat) :
    LiftedBinderWitness input selection arity
      (sourceBinders.push child binderArity)
      (targetBinders.push child.castSucc binderArity) := by
  refine ⟨congrArg (List.cons binderArity) witness.relationContexts_eq, ?_⟩
  intro region
  cases witness.relationContexts_eq
  simp only [ConcreteElaboration.BinderContext.push]
  by_cases equality : region = child
  · subst region
    simp
  · have liftedNe : region.castSucc ≠ child.castSucc := by
      intro liftedEquality
      apply equality
      apply Fin.ext
      exact congrArg
        (fun value : Fin (input.regionCount + 1) => value.val)
        liftedEquality
    rw [if_neg equality]
    apply heq_of_eq
    split
    · rename_i liftedEquality
      exact False.elim (liftedNe liftedEquality)
    · rw [eq_of_heq (witness.binders_eq region)]

theorem relationMap_push
    (witness : LiftedBinderWitness input selection arity
      (sourceRels := sourceRels) (targetRels := targetRels)
      sourceBinders targetBinders)
    (child : Fin input.regionCount) (binderArity : Nat) :
    (relationMap (push witness child binderArity) :
      RelationRenaming (binderArity :: sourceRels)
        (binderArity :: targetRels)) =
      (RelationRenaming.lift (relationMap witness) binderArity :
        RelationRenaming (binderArity :: sourceRels)
          (binderArity :: targetRels)) := by
  cases witness.relationContexts_eq
  simpa [relationMap, ConcreteElaboration.identityRelationRenaming] using
    (RelationRenaming.lift_id_fun (source := sourceRels) binderArity).symm

end LiftedBinderWitness

private theorem allFin_succ_last (n : Nat) :
    allFin (n + 1) = (allFin n).map Fin.castSucc ++ [Fin.last n] := by
  rw [allFin_eq_finRange, allFin_eq_finRange, List.finRange_succ_last]

private def canonicalSelectedOccurrences
    (input : ConcreteDiagram) (selection : CheckedSelection input) :=
  (filterFin fun node =>
      decide (node ∈ selection.val.directNodes)).map
        ConcreteElaboration.LocalOccurrence.node ++
    (filterFin fun child =>
      decide (child ∈ selection.val.childRoots)).map
        ConcreteElaboration.LocalOccurrence.child

private def canonicalKeptOccurrences
    (input : ConcreteDiagram) (selection : CheckedSelection input) :=
  (filterFin fun node => decide
      ((input.nodes node).region = selection.val.anchor ∧
        node ∉ selection.val.directNodes)).map
      ConcreteElaboration.LocalOccurrence.node ++
    (filterFin fun child => decide
      ((input.regions child).parent? = some selection.val.anchor ∧
        child ∉ selection.val.childRoots)).map
      ConcreteElaboration.LocalOccurrence.child

private theorem selectedOccurrences_eq_canonical
    (input : ConcreteDiagram) (selection : CheckedSelection input) :
    ModalSoundness.selectedOccurrences input selection =
      canonicalSelectedOccurrences input selection := by
  unfold ModalSoundness.selectedOccurrences canonicalSelectedOccurrences
    ConcreteElaboration.localOccurrences ModalSoundness.occurrenceSelected
    filterFin
  simp only [List.filter_append, List.filter_map, List.filter_filter]
  congr 1
  · apply congrArg (List.map ConcreteElaboration.LocalOccurrence.node)
    apply congrArg
      (fun predicate => List.filter predicate (allFin input.nodeCount))
    funext node
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply, ModalSoundness.occurrenceSelected,
      Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · exact And.left
    · intro selected
      exact ⟨selected,
        selection.property.directNodes_at_anchor node selected⟩
  · apply congrArg (List.map ConcreteElaboration.LocalOccurrence.child)
    apply congrArg
      (fun predicate => List.filter predicate (allFin input.regionCount))
    funext child
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply, ModalSoundness.occurrenceSelected,
      Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · exact And.left
    · intro selected
      exact ⟨selected, selection.property.childRoots_direct child selected⟩

private theorem keptOccurrences_eq_canonical
    (input : ConcreteDiagram) (selection : CheckedSelection input) :
    ModalSoundness.keptOccurrences input selection =
      canonicalKeptOccurrences input selection := by
  unfold ModalSoundness.keptOccurrences canonicalKeptOccurrences
    ConcreteElaboration.localOccurrences ModalSoundness.occurrenceSelected
    filterFin
  simp only [List.filter_append, List.filter_map, List.filter_filter]
  congr 1
  · apply congrArg (List.map ConcreteElaboration.LocalOccurrence.node)
    apply congrArg
      (fun predicate => List.filter predicate (allFin input.nodeCount))
    funext node
    apply Bool.eq_iff_iff.mpr
    simp [ModalSoundness.occurrenceSelected, and_comm]
  · apply congrArg (List.map ConcreteElaboration.LocalOccurrence.child)
    apply congrArg
      (fun predicate => List.filter predicate (allFin input.regionCount))
    funext child
    apply Bool.eq_iff_iff.mpr
    simp [ModalSoundness.occurrenceSelected, and_comm]

theorem bubble_localOccurrences
    (input : ConcreteDiagram) (selection : CheckedSelection input)
    (arity : Nat) :
    ConcreteElaboration.localOccurrences
        (vacuousIntroRaw input selection arity) (bubbleRegion input) =
      (ModalSoundness.selectedOccurrences input selection).map
        (liftOccurrence input) := by
  rw [selectedOccurrences_eq_canonical]
  unfold ConcreteElaboration.localOccurrences canonicalSelectedOccurrences
    filterFin
  simp only [vacuousIntroRaw_nodeCount, vacuousIntroRaw_regionCount,
    List.map_append, List.map_map, allFin_succ_last, List.filter_append,
    List.filter_map]
  have liftNode :
      (liftOccurrence input ∘ ConcreteElaboration.LocalOccurrence.node) =
        ConcreteElaboration.LocalOccurrence.node := by
    funext node
    rfl
  have liftChild :
      (liftOccurrence input ∘ ConcreteElaboration.LocalOccurrence.child) =
        (ConcreteElaboration.LocalOccurrence.child ∘ Fin.castSucc) := by
    funext child
    rfl
  rw [liftNode, liftChild]
  congr 1
  · apply congrArg (List.map ConcreteElaboration.LocalOccurrence.node)
    apply congrArg
      (fun predicate => List.filter predicate (allFin input.nodeCount))
    funext node
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    by_cases selected : node ∈ selection.val.directNodes
    · have owner := vacuousIntroRaw_node_region input selection arity node
      rw [if_pos selected] at owner
      exact ⟨fun _ => selected, fun _ => owner⟩
    · have owner := vacuousIntroRaw_node_region input selection arity node
      rw [if_neg selected] at owner
      constructor
      · intro targetOwner
        exact False.elim (bubbleRegion_ne_lift input
          (input.nodes node).region (targetOwner.symm.trans owner))
      · exact fun impossible => False.elim (selected impossible)
  · have oldChildren :
        List.filter
            ((fun child => decide
              (((vacuousIntroRaw input selection arity).regions child).parent? =
                some (bubbleRegion input))) ∘ Fin.castSucc)
            (allFin input.regionCount) =
          List.filter (fun child =>
            decide (child ∈ selection.val.childRoots))
            (allFin input.regionCount) := by
      apply congrArg
        (fun predicate => List.filter predicate (allFin input.regionCount))
      funext child
      apply Bool.eq_iff_iff.mpr
      simp only [Function.comp_apply, decide_eq_true_eq]
      have parent := vacuousIntroRaw_oldRegion_parent input selection arity child
      by_cases selected : child ∈ selection.val.childRoots
      · rw [if_pos selected] at parent
        exact ⟨fun _ => selected, fun _ => parent⟩
      · rw [if_neg selected] at parent
        constructor
        · intro targetParent
          rw [parent] at targetParent
          cases oldParent : (input.regions child).parent? with
          | none => simp [oldParent] at targetParent
          | some old =>
              simp [oldParent] at targetParent
              exact False.elim
                (bubbleRegion_ne_lift input old targetParent.symm)
        · exact fun impossible => False.elim (selected impossible)
    have noSelf :
        ¬((vacuousIntroRaw input selection arity).regions
          (bubbleRegion input)).parent? = some (bubbleRegion input) := by
      rw [vacuousIntroRaw_bubble_parent]
      intro equality
      exact bubbleRegion_ne_lift input selection.val.anchor
        (Option.some.inj equality).symm
    have addedEmpty :
        List.filter
            (fun child => decide
              (((vacuousIntroRaw input selection arity).regions child).parent? =
                some (bubbleRegion input)))
            [Fin.last input.regionCount] = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro child member selected
      have childEq : child = bubbleRegion input := by
        have lastEq : child = Fin.last input.regionCount :=
          List.mem_singleton.mp member
        simpa [bubbleRegion] using lastEq
      subst child
      exact noSelf (decide_eq_true_eq.mp selected)
    have mappedAddedEmpty :
        List.map
            (ConcreteElaboration.LocalOccurrence.child
              (regions := input.regionCount + 1)
              (nodes := input.nodeCount))
            (List.filter
              (fun child => decide
                (((vacuousIntroRaw input selection arity).regions child).parent? =
                  some (bubbleRegion input)))
              [Fin.last input.regionCount]) = [] := by
      exact congrArg
        (List.map
          (ConcreteElaboration.LocalOccurrence.child
            (regions := input.regionCount + 1)
            (nodes := input.nodeCount)))
        addedEmpty
    calc
      _ = List.map
          (ConcreteElaboration.LocalOccurrence.child ∘ Fin.castSucc)
          (List.filter
            ((fun child => decide
              (((vacuousIntroRaw input selection arity).regions child).parent? =
                some (bubbleRegion input))) ∘ Fin.castSucc)
            (allFin input.regionCount)) := by
        have appended := congrArg
          (fun tail =>
            List.map
                (ConcreteElaboration.LocalOccurrence.child ∘ Fin.castSucc)
                (List.filter
                  ((fun child => decide
                    (((vacuousIntroRaw input selection arity).regions
                      child).parent? = some (bubbleRegion input))) ∘
                    Fin.castSucc)
                  (allFin input.regionCount)) ++
              List.map
                (ConcreteElaboration.LocalOccurrence.child
                  (regions := input.regionCount + 1)
                  (nodes := input.nodeCount)) tail)
          addedEmpty
        exact appended.trans (by simp)
      _ = _ := congrArg
        (List.map
          (ConcreteElaboration.LocalOccurrence.child ∘ Fin.castSucc))
        oldChildren

theorem anchor_localOccurrences
    (input : ConcreteDiagram) (selection : CheckedSelection input)
    (arity : Nat) :
    ConcreteElaboration.localOccurrences
        (vacuousIntroRaw input selection arity) selection.val.anchor.castSucc =
      (ModalSoundness.keptOccurrences input selection).map
          (liftOccurrence input) ++
        [ConcreteElaboration.LocalOccurrence.child (bubbleRegion input)] := by
  rw [keptOccurrences_eq_canonical]
  unfold ConcreteElaboration.localOccurrences canonicalKeptOccurrences
    filterFin
  simp only [vacuousIntroRaw_nodeCount, vacuousIntroRaw_regionCount,
    List.map_append, List.map_map, allFin_succ_last, List.filter_append,
    List.filter_map]
  have liftNode :
      (liftOccurrence input ∘ ConcreteElaboration.LocalOccurrence.node) =
        ConcreteElaboration.LocalOccurrence.node := by
    funext node
    rfl
  have liftChild :
      (liftOccurrence input ∘ ConcreteElaboration.LocalOccurrence.child) =
        (ConcreteElaboration.LocalOccurrence.child ∘ Fin.castSucc) := by
    funext child
    rfl
  rw [liftNode, liftChild, List.append_assoc]
  congr 1
  · apply congrArg (List.map ConcreteElaboration.LocalOccurrence.node)
    apply congrArg
      (fun predicate => List.filter predicate (allFin input.nodeCount))
    funext node
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    have owner := vacuousIntroRaw_node_region input selection arity node
    by_cases selected : node ∈ selection.val.directNodes
    · rw [if_pos selected] at owner
      constructor
      · intro targetOwner
        exact False.elim (bubbleRegion_ne_lift input selection.val.anchor
          (owner.symm.trans targetOwner))
      · intro impossible
        exact False.elim (impossible.2 selected)
    · rw [if_neg selected] at owner
      constructor
      · intro targetOwner
        refine ⟨?_, selected⟩
        apply Fin.ext
        exact congrArg
          (fun value : Fin (input.regionCount + 1) => value.val)
          (owner.symm.trans targetOwner)
      · rintro ⟨sourceOwner, _⟩
        exact owner.trans (congrArg Fin.castSucc sourceOwner)
  · have oldChildren :
        List.filter
            ((fun child => decide
              (((vacuousIntroRaw input selection arity).regions child).parent? =
                some selection.val.anchor.castSucc)) ∘ Fin.castSucc)
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
      have parent := vacuousIntroRaw_oldRegion_parent input selection arity child
      by_cases selected : child ∈ selection.val.childRoots
      · rw [if_pos selected] at parent
        constructor
        · intro targetParent
          exact False.elim (bubbleRegion_ne_lift input selection.val.anchor
            (Option.some.inj (parent.symm.trans targetParent)))
        · intro impossible
          exact False.elim (impossible.2 selected)
      · rw [if_neg selected] at parent
        constructor
        · intro targetParent
          rw [parent] at targetParent
          cases sourceParent : (input.regions child).parent? with
          | none => simp [sourceParent] at targetParent
          | some actualParent =>
              simp [sourceParent] at targetParent
              refine ⟨?_, selected⟩
              apply congrArg some
              apply Fin.ext
              exact congrArg
                (fun value : Fin (input.regionCount + 1) => value.val)
                targetParent
        · rintro ⟨sourceParent, _⟩
          rw [parent, sourceParent]
          rfl
    have bubbleIsChild :
        ((vacuousIntroRaw input selection arity).regions
          (bubbleRegion input)).parent? =
            some selection.val.anchor.castSucc :=
      vacuousIntroRaw_bubble_parent input selection arity
    have addedFilter :
        List.filter
            (fun child => decide
              (((vacuousIntroRaw input selection arity).regions child).parent? =
                some selection.val.anchor.castSucc))
            [Fin.last input.regionCount] = [bubbleRegion input] := by
      change List.filter
          (fun child => decide
            (((vacuousIntroRaw input selection arity).regions child).parent? =
              some selection.val.anchor.castSucc))
          [bubbleRegion input] = [bubbleRegion input]
      simp [CRegion.parent?]
    have oldMapped := congrArg
      (List.map
        (ConcreteElaboration.LocalOccurrence.child
          (nodes := input.nodeCount) ∘ Fin.castSucc))
      oldChildren
    have newMapped := congrArg
      (List.map
        (ConcreteElaboration.LocalOccurrence.child
          (regions := input.regionCount + 1) (nodes := input.nodeCount)))
      addedFilter
    calc
      _ = List.map
            (ConcreteElaboration.LocalOccurrence.child ∘ Fin.castSucc)
            (List.filter (fun child => decide
              ((input.regions child).parent? = some selection.val.anchor ∧
                child ∉ selection.val.childRoots))
              (allFin input.regionCount)) ++
          List.map
            (ConcreteElaboration.LocalOccurrence.child
              (regions := input.regionCount + 1) (nodes := input.nodeCount))
            (List.filter
              (fun child => decide
                (((vacuousIntroRaw input selection arity).regions child).parent? =
                  some selection.val.anchor.castSucc))
              [Fin.last input.regionCount]) := by
        exact congrArg
          (fun old => old ++
            List.map
              (ConcreteElaboration.LocalOccurrence.child
                (regions := input.regionCount + 1) (nodes := input.nodeCount))
              (List.filter
                (fun child => decide
                  (((vacuousIntroRaw input selection arity).regions child).parent? =
                    some selection.val.anchor.castSucc))
                [Fin.last input.regionCount]))
          oldMapped
      _ = _ := by
        have appended := congrArg
          (fun tail =>
            List.map
                (ConcreteElaboration.LocalOccurrence.child ∘ Fin.castSucc)
                (List.filter (fun child => decide
                  ((input.regions child).parent? = some selection.val.anchor ∧
                    child ∉ selection.val.childRoots))
                  (allFin input.regionCount)) ++ tail)
          newMapped
        exact appended.trans (by simp)

theorem anchorOccurrences_perm_partition
    (input : ConcreteDiagram) (selection : CheckedSelection input) :
    List.Perm
      (ModalSoundness.keptOccurrences input selection ++
        ModalSoundness.selectedOccurrences input selection)
      (ConcreteElaboration.localOccurrences input selection.val.anchor) := by
  simpa only [ModalSoundness.keptOccurrences,
    ModalSoundness.selectedOccurrences, Bool.not_not] using
    (List.filter_append_perm
      (fun occurrence =>
        !(ModalSoundness.occurrenceSelected selection occurrence))
      (ConcreteElaboration.localOccurrences input selection.val.anchor))

theorem regular_localOccurrences
    (input : ConcreteDiagram) (selection : CheckedSelection input)
    (arity : Nat) (region : Fin input.regionCount)
    (regular : region ≠ selection.val.anchor) :
    ConcreteElaboration.localOccurrences
        (vacuousIntroRaw input selection arity) region.castSucc =
      (ConcreteElaboration.localOccurrences input region).map
        (liftOccurrence input) := by
  unfold ConcreteElaboration.localOccurrences filterFin
  simp only [vacuousIntroRaw_nodeCount, vacuousIntroRaw_regionCount,
    List.map_append, List.map_map, allFin_succ_last, List.filter_append,
    List.filter_map]
  have liftNode :
      (liftOccurrence input ∘ ConcreteElaboration.LocalOccurrence.node) =
        ConcreteElaboration.LocalOccurrence.node := by
    funext node
    rfl
  have liftChild :
      (liftOccurrence input ∘ ConcreteElaboration.LocalOccurrence.child) =
        (ConcreteElaboration.LocalOccurrence.child ∘ Fin.castSucc) := by
    funext child
    rfl
  rw [liftNode, liftChild]
  congr 1
  · apply congrArg (List.map ConcreteElaboration.LocalOccurrence.node)
    apply congrArg
      (fun predicate => List.filter predicate (allFin input.nodeCount))
    funext node
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    have owner := vacuousIntroRaw_node_region input selection arity node
    by_cases selected : node ∈ selection.val.directNodes
    · have sourceOwner :=
        selection.property.directNodes_at_anchor node selected
      rw [if_pos selected] at owner
      constructor
      · intro targetOwner
        exact False.elim (bubbleRegion_ne_lift input region
          (owner.symm.trans targetOwner))
      · intro sourceAtRegion
        exact False.elim (regular (sourceOwner.symm.trans sourceAtRegion).symm)
    · rw [if_neg selected] at owner
      constructor
      · intro targetOwner
        apply Fin.ext
        exact congrArg
          (fun value : Fin (input.regionCount + 1) => value.val)
          (owner.symm.trans targetOwner)
      · intro sourceOwner
        exact owner.trans (congrArg Fin.castSucc sourceOwner)
  · have noAddedChild :
        List.filter
            (fun child => decide
              (((vacuousIntroRaw input selection arity).regions child).parent? =
                some region.castSucc))
            [Fin.last input.regionCount] = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro child member selected
      have childEq : child = bubbleRegion input := by
        simpa [bubbleRegion] using List.mem_singleton.mp member
      subst child
      have parent := vacuousIntroRaw_bubble_parent input selection arity
      exact regular (by
        apply Fin.ext
        exact congrArg
          (fun value : Fin (input.regionCount + 1) => value.val)
          (Option.some.inj
            (parent.symm.trans (decide_eq_true_eq.mp selected))).symm)
    have oldChildren :
        List.filter
            ((fun child => decide
              (((vacuousIntroRaw input selection arity).regions child).parent? =
                some region.castSucc)) ∘ Fin.castSucc)
            (allFin input.regionCount) =
          List.filter (fun child => decide
            ((input.regions child).parent? = some region))
            (allFin input.regionCount) := by
      apply congrArg
        (fun predicate => List.filter predicate (allFin input.regionCount))
      funext child
      apply Bool.eq_iff_iff.mpr
      simp only [Function.comp_apply, decide_eq_true_eq]
      have parent := vacuousIntroRaw_oldRegion_parent input selection arity child
      by_cases selected : child ∈ selection.val.childRoots
      · have sourceParent := selection.property.childRoots_direct child selected
        rw [if_pos selected] at parent
        constructor
        · intro targetParent
          exact False.elim (bubbleRegion_ne_lift input region
            (Option.some.inj (parent.symm.trans targetParent)))
        · intro atRegion
          exact False.elim (regular
            (Option.some.inj (sourceParent.symm.trans atRegion)).symm)
      · rw [if_neg selected] at parent
        constructor
        · intro targetParent
          cases sourceParent : (input.regions child).parent? with
          | none =>
              simp [sourceParent] at parent
              cases parent.symm.trans targetParent
          | some actualParent =>
              rw [sourceParent] at parent
              apply congrArg some
              apply Fin.ext
              exact congrArg
                (fun value : Fin (input.regionCount + 1) => value.val)
                (Option.some.inj (parent.symm.trans targetParent))
        · intro sourceParent
          rw [sourceParent] at parent
          exact parent
    have removedTail := congrArg
      (fun tail =>
        List.map
            (ConcreteElaboration.LocalOccurrence.child ∘ Fin.castSucc)
            (List.filter
              ((fun child => decide
                (((vacuousIntroRaw input selection arity).regions child).parent? =
                  some region.castSucc)) ∘ Fin.castSucc)
              (allFin input.regionCount)) ++
          List.map
            (ConcreteElaboration.LocalOccurrence.child
              (regions := input.regionCount + 1) (nodes := input.nodeCount)) tail)
      noAddedChild
    calc
      _ = List.map
          (ConcreteElaboration.LocalOccurrence.child ∘ Fin.castSucc)
          (List.filter
            ((fun child => decide
              (((vacuousIntroRaw input selection arity).regions child).parent? =
                some region.castSucc)) ∘ Fin.castSucc)
            (allFin input.regionCount)) :=
        removedTail.trans (by simp)
      _ = _ := congrArg
        (List.map
          (ConcreteElaboration.LocalOccurrence.child ∘ Fin.castSucc))
        oldChildren

theorem regular_regionShape
    (input : ConcreteDiagram) (selection : CheckedSelection input)
    (arity : Nat) (parent child : Fin input.regionCount)
    (regular : parent ≠ selection.val.anchor)
    (childParent : (input.regions child).parent? = some parent) :
    (vacuousIntroRaw input selection arity).regions child.castSucc =
      match input.regions child with
      | .sheet => .sheet
      | .cut actualParent => .cut actualParent.castSucc
      | .bubble actualParent childArity =>
          .bubble actualParent.castSucc childArity := by
  have childNotSelected : child ∉ selection.val.childRoots := by
    intro selected
    have direct := selection.property.childRoots_direct child selected
    exact regular (Option.some.inj (childParent.symm.trans direct))
  rw [vacuousIntroRaw_oldRegion, if_neg childNotSelected]
  cases input.regions child <;> rfl

theorem regular_nodeShape
    (input : ConcreteDiagram) (selection : CheckedSelection input)
    (arity : Nat) (region : Fin input.regionCount)
    (regular : region ≠ selection.val.anchor)
    (node : Fin input.nodeCount)
    (nodeRegion : (input.nodes node).region = region) :
    (vacuousIntroRaw input selection arity).nodes node =
      match input.nodes node with
      | .term owner freePorts term =>
          .term owner.castSucc freePorts term
      | .atom owner binder => .atom owner.castSucc binder.castSucc
      | .named owner definition nodeArity =>
          .named owner.castSucc definition nodeArity := by
  have nodeNotSelected : node ∉ selection.val.directNodes := by
    intro selected
    have atAnchor := selection.property.directNodes_at_anchor node selected
    exact regular (nodeRegion.symm.trans atAnchor)
  rw [vacuousIntroRaw_node, if_neg nodeNotSelected]
  cases input.nodes node <;> rfl

theorem selected_nodeShape
    (input : ConcreteDiagram) (selection : CheckedSelection input)
    (arity : Nat) (node : Fin input.nodeCount)
    (selected : node ∈ selection.val.directNodes) :
    (vacuousIntroRaw input selection arity).nodes node =
      match input.nodes node with
      | .term _ freePorts term =>
          .term (bubbleRegion input) freePorts term
      | .atom _ binder =>
          .atom (bubbleRegion input) binder.castSucc
      | .named _ definition nodeArity =>
          .named (bubbleRegion input) definition nodeArity := by
  rw [vacuousIntroRaw_node, if_pos selected]
  cases input.nodes node <;> rfl

theorem unselected_nodeShape
    (input : ConcreteDiagram) (selection : CheckedSelection input)
    (arity : Nat) (node : Fin input.nodeCount)
    (unselected : node ∉ selection.val.directNodes) :
    (vacuousIntroRaw input selection arity).nodes node =
      match input.nodes node with
      | .term owner freePorts term =>
          .term owner.castSucc freePorts term
      | .atom owner binder => .atom owner.castSucc binder.castSucc
      | .named owner definition nodeArity =>
          .named owner.castSucc definition nodeArity := by
  rw [vacuousIntroRaw_node, if_neg unselected]
  cases input.nodes node <;> rfl

theorem selected_regionShape
    (input : ConcreteDiagram) (selection : CheckedSelection input)
    (arity : Nat) (child : Fin input.regionCount)
    (selected : child ∈ selection.val.childRoots) :
    (vacuousIntroRaw input selection arity).regions child.castSucc =
      match input.regions child with
      | .sheet => .sheet
      | .cut _ => .cut (bubbleRegion input)
      | .bubble _ childArity => .bubble (bubbleRegion input) childArity := by
  rw [vacuousIntroRaw_oldRegion, if_pos selected]
  cases input.regions child <;> rfl

theorem unselected_regionShape
    (input : ConcreteDiagram) (selection : CheckedSelection input)
    (arity : Nat) (child : Fin input.regionCount)
    (unselected : child ∉ selection.val.childRoots) :
    (vacuousIntroRaw input selection arity).regions child.castSucc =
      match input.regions child with
      | .sheet => .sheet
      | .cut parent => .cut parent.castSucc
      | .bubble parent childArity => .bubble parent.castSucc childArity := by
  rw [vacuousIntroRaw_oldRegion, if_neg unselected]
  cases input.regions child <;> rfl

theorem endpointOccurs
    (input : ConcreteDiagram) (selection : CheckedSelection input)
    (arity : Nat) (wire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount) :
    (vacuousIntroRaw input selection arity).EndpointOccurs wire endpoint ↔
      input.EndpointOccurs wire endpoint := by
  simp only [ConcreteDiagram.EndpointOccurs, vacuousIntroRaw_wire,
    liftCWireRegions]
  rfl

theorem endpointOwner
    (input : ConcreteDiagram) (selection : CheckedSelection input)
    (arity : Nat) (endpoint : CEndpoint input.nodeCount) :
    ConcreteElaboration.endpointOwner?
        (vacuousIntroRaw input selection arity) endpoint =
      ConcreteElaboration.endpointOwner? input endpoint := by
  unfold ConcreteElaboration.endpointOwner?
  apply congrArg List.head?
  unfold filterFin
  apply List.filter_congr
  intro wire _
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact endpointOccurs input selection arity wire endpoint

theorem resolvePort
    (input : ConcreteDiagram) (selection : CheckedSelection input)
    (arity : Nat)
    (sourceContext : ConcreteElaboration.WireContext input)
    (targetContext : ConcreteElaboration.WireContext
      (vacuousIntroRaw input selection arity))
    (witness : LiftedContextWitness input selection arity
      sourceContext targetContext)
    (node : Fin input.nodeCount) (port : CPort) :
    ConcreteElaboration.resolvePort?
        (vacuousIntroRaw input selection arity) targetContext node port =
      (ConcreteElaboration.resolvePort? input sourceContext node port).map
        (Fin.cast (congrArg List.length witness.contexts_eq)) := by
  rcases witness with ⟨rfl⟩
  simp only [ConcreteElaboration.resolvePort?, endpointOwner]
  generalize resultEq :
      (do
        let wire ← ConcreteElaboration.endpointOwner? input ⟨node, port⟩
        sourceContext.lookup? wire) = result
  cases result with
  | none => exact resultEq.trans rfl
  | some index =>
      apply resultEq.trans
      simp only [Option.map_some]
      apply congrArg some
      apply Fin.ext
      rfl

end VisualProof.Rule.VacuousSoundness
