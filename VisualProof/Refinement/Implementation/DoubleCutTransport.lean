import VisualProof.Concrete.Step
import VisualProof.Concrete.Subgraph.Splice.Trace
import VisualProof.Diagram.ContextPathIsomorphism

namespace VisualProof.Refinement.Implementation.DoubleCutTransport

open VisualProof
open VisualProof.Concrete
open VisualProof.Data.Finite
open VisualProof.Diagram
open VisualProof.Theory

def identityRelationRenaming (rels : RelCtx) : RelationRenaming rels rels :=
  fun relation => relation

private theorem allFin_succ_last (n : Nat) :
    allFin (n + 1) = (allFin n).map (Fin.castAdd 1) ++ [Fin.last n] := by
  rw [allFin_eq_finRange, allFin_eq_finRange, List.finRange_succ_last]
  apply congrArg (fun indices : List (Fin (n + 1)) => indices ++ [Fin.last n])
  apply List.map_congr_left
  intro index _
  ext
  rfl

theorem allFin_add (n m : Nat) :
    allFin (n + m) =
      (allFin n).map (Fin.castAdd m) ++ (allFin m).map (Fin.natAdd n) := by
  induction m with
  | zero =>
      simp only [Nat.add_zero, allFin, List.map_nil, List.append_nil]
      have equality : (Fin.castAdd 0 : Fin n → Fin (n + 0)) = id := by
        funext index
        ext
        rfl
      rw [equality, List.map_id]
  | succ m induction =>
      change allFin ((n + m) + 1) = _
      rw [allFin_succ_last (n + m), induction, List.map_append,
        allFin_succ_last m, List.map_append, List.map_map, List.append_assoc]
      simp only [List.map_map]
      have left :
          (Fin.castAdd 1 ∘ Fin.castAdd m : Fin n → Fin ((n + m) + 1)) =
            Fin.castAdd (m + 1) := by funext index; ext; rfl
      have middle :
          (Fin.castAdd 1 ∘ Fin.natAdd n : Fin m → Fin ((n + m) + 1)) =
            Fin.natAdd n ∘ Fin.castAdd 1 := by funext index; ext; rfl
      have last : Fin.last (n + m) = Fin.natAdd n (Fin.last m) := by ext; rfl
      rw [left, middle, last]
      rfl

def outer (input : Concrete.Diagram) : Fin (input.regionCount + 2) :=
  Fin.natAdd input.regionCount ⟨0, by decide⟩

def inner (input : Concrete.Diagram) : Fin (input.regionCount + 2) :=
  Fin.natAdd input.regionCount ⟨1, by decide⟩

@[simp] theorem regionCount (input : Concrete.Diagram)
    (selection : CheckedSelection input) :
    (doubleCutIntroRaw input selection).regionCount = input.regionCount + 2 := rfl

@[simp] theorem nodeCount (input : Concrete.Diagram)
    (selection : CheckedSelection input) :
    (doubleCutIntroRaw input selection).nodeCount = input.nodeCount := rfl

@[simp] theorem wireCount (input : Concrete.Diagram)
    (selection : CheckedSelection input) :
    (doubleCutIntroRaw input selection).wireCount = input.wireCount := rfl

@[simp] theorem root (input : Concrete.Diagram)
    (selection : CheckedSelection input) :
    (doubleCutIntroRaw input selection).root = Fin.castAdd 2 input.root := rfl

def targetOpen (source : Concrete.OpenDiagram)
    (selection : CheckedSelection source.diagram) : Concrete.OpenDiagram := {
  diagram := doubleCutIntroRaw source.diagram selection
  boundary := source.boundary
}

@[simp] theorem targetOpen_exposedWires (source : Concrete.OpenDiagram)
    (selection : CheckedSelection source.diagram) :
    (targetOpen source selection).exposedWires = source.exposedWires := rfl

theorem targetOpen_wellFormed
    (source : Concrete.CheckedOpen)
    (selection : CheckedSelection source.val.diagram)
    (rawWellFormed : (doubleCutIntroRaw source.val.diagram selection).WellFormed) :
    (targetOpen source.val selection).WellFormed := by
  refine {
    diagram_well_formed := rawWellFormed
    boundary_is_root_scoped := ?_
  }
  intro wire member
  change (liftCWireRegions 2 (source.val.diagram.wires wire)).scope =
    Fin.castAdd 2 source.val.diagram.root
  exact congrArg (Fin.castAdd 2)
    (source.property.boundary_is_root_scoped wire member)

theorem outer_ne_lift (input : Concrete.Diagram)
    (region : Fin input.regionCount) : outer input ≠ Fin.castAdd 2 region := by
  intro equality
  have values := congrArg Fin.val equality
  simp [outer] at values
  omega

theorem inner_ne_lift (input : Concrete.Diagram)
    (region : Fin input.regionCount) : inner input ≠ Fin.castAdd 2 region := by
  intro equality
  have values := congrArg Fin.val equality
  simp [inner] at values
  omega

theorem outer_ne_inner (input : Concrete.Diagram) : outer input ≠ inner input := by
  intro equality
  have values := congrArg Fin.val equality
  simp [outer, inner] at values

@[simp] theorem wire (input : Concrete.Diagram)
    (selection : CheckedSelection input) (index : Fin input.wireCount) :
    (doubleCutIntroRaw input selection).wires index =
      liftCWireRegions 2 (input.wires index) := rfl

theorem node (input : Concrete.Diagram)
    (selection : CheckedSelection input) (index : Fin input.nodeCount) :
    (doubleCutIntroRaw input selection).nodes index =
      if index ∈ selection.val.directNodes then
        reparentLiftedNode 2 (inner input) (input.nodes index)
      else liftCNode 2 (input.nodes index) := by
  rfl

theorem oldRegion (input : Concrete.Diagram)
    (selection : CheckedSelection input) (region : Fin input.regionCount) :
    (doubleCutIntroRaw input selection).regions (Fin.castAdd 2 region) =
      if region ∈ selection.val.childRoots then
        reparentLiftedRegion 2 (inner input) (input.regions region)
      else liftCRegion 2 (input.regions region) := by
  simp only [doubleCutIntroRaw, Fin.addCases_left]
  rfl

@[simp] theorem outer_region (input : Concrete.Diagram)
    (selection : CheckedSelection input) :
    (doubleCutIntroRaw input selection).regions (outer input) =
      .cut (Fin.castAdd 2 selection.val.anchor) := by
  simp only [doubleCutIntroRaw, outer, Fin.addCases_right]
  have zero : (⟨0, outer._proof_1⟩ : Fin 2) = 0 := by ext; rfl
  rw [zero]
  rfl

@[simp] theorem inner_region (input : Concrete.Diagram)
    (selection : CheckedSelection input) :
    (doubleCutIntroRaw input selection).regions (inner input) = .cut (outer input) := by
  simp only [doubleCutIntroRaw, inner, outer, Fin.addCases_right]
  have one : (⟨1, inner._proof_1⟩ : Fin 2) = 1 := by ext; rfl
  rw [one]
  congr 1

theorem node_region (input : Concrete.Diagram)
    (selection : CheckedSelection input) (index : Fin input.nodeCount) :
    ((doubleCutIntroRaw input selection).nodes index).region =
      if index ∈ selection.val.directNodes then inner input
      else Fin.castAdd 2 (input.nodes index).region := by
  rw [node]
  split <;> cases input.nodes index <;> rfl

theorem oldRegion_parent (input : Concrete.Diagram)
    (selection : CheckedSelection input) (region : Fin input.regionCount) :
    ((doubleCutIntroRaw input selection).regions
        (Fin.castAdd 2 region)).parent? =
      if region ∈ selection.val.childRoots then some (inner input)
      else (input.regions region).parent?.map (Fin.castAdd 2) := by
  rw [oldRegion]
  by_cases selected : region ∈ selection.val.childRoots
  · simp only [if_pos selected]
    have direct := selection.property.childRoots_direct region selected
    cases shape : input.regions region with
    | sheet => rw [shape] at direct; cases direct
    | cut => rfl
    | bubble => rfl
  · simp only [if_neg selected]
    cases input.regions region <;> rfl

@[simp] theorem outer_parent (input : Concrete.Diagram)
    (selection : CheckedSelection input) :
    ((doubleCutIntroRaw input selection).regions (outer input)).parent? =
      some (Fin.castAdd 2 selection.val.anchor) := by
  rw [outer_region]
  rfl

@[simp] theorem inner_parent (input : Concrete.Diagram)
    (selection : CheckedSelection input) :
    ((doubleCutIntroRaw input selection).regions (inner input)).parent? =
      some (outer input) := by
  rw [inner_region]
  rfl

@[simp] theorem exactScopeWires (input : Concrete.Diagram)
    (selection : CheckedSelection input) (region : Fin input.regionCount) :
    Concrete.Elaboration.exactScopeWires (doubleCutIntroRaw input selection)
        (Fin.castAdd 2 region) =
      Concrete.Elaboration.exactScopeWires input region := by
  unfold Concrete.Elaboration.exactScopeWires
  apply congrArg filterFin
  funext index
  apply Bool.eq_iff_iff.mpr
  simp only [wire, liftCWireRegions, decide_eq_true_eq, Fin.ext_iff]
  constructor
  · intro equality
    exact congrArg (fun value : Fin (input.regionCount + 2) => value.val) equality
  · intro equality
    exact Fin.ext equality

@[simp] theorem targetOpen_hiddenWires (source : Concrete.OpenDiagram)
    (selection : CheckedSelection source.diagram) :
    (targetOpen source selection).hiddenWires = source.hiddenWires := by
  unfold Concrete.OpenDiagram.hiddenWires targetOpen
  rw [root, exactScopeWires]
  rfl

@[simp] theorem targetOpen_rootWires (source : Concrete.OpenDiagram)
    (selection : CheckedSelection source.diagram) :
    (targetOpen source selection).rootWires = source.rootWires := by
  unfold Concrete.OpenDiagram.rootWires
  rw [targetOpen_exposedWires, targetOpen_hiddenWires]
  rfl

@[simp] theorem outer_exactScopeWires (input : Concrete.Diagram)
    (selection : CheckedSelection input) :
    Concrete.Elaboration.exactScopeWires (doubleCutIntroRaw input selection)
      (outer input) = [] := by
  unfold Concrete.Elaboration.exactScopeWires filterFin
  rw [show allFin (doubleCutIntroRaw input selection).wireCount =
      allFin input.wireCount by rfl]
  apply List.filter_eq_nil_iff.mpr
  intro index _ chosen
  exact outer_ne_lift input (input.wires index).scope
    (decide_eq_true_eq.mp chosen).symm

@[simp] theorem inner_exactScopeWires (input : Concrete.Diagram)
    (selection : CheckedSelection input) :
    Concrete.Elaboration.exactScopeWires (doubleCutIntroRaw input selection)
      (inner input) = [] := by
  unfold Concrete.Elaboration.exactScopeWires filterFin
  rw [show allFin (doubleCutIntroRaw input selection).wireCount =
      allFin input.wireCount by rfl]
  apply List.filter_eq_nil_iff.mpr
  intro index _ chosen
  exact inner_ne_lift input (input.wires index).scope
    (decide_eq_true_eq.mp chosen).symm

structure Context
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    (source : Concrete.Elaboration.WireContext input)
    (target : Concrete.Elaboration.WireContext
      (doubleCutIntroRaw input selection)) : Type where
  equality : source = target

def Context.extend (witness : Context input selection source target)
    (region : Fin input.regionCount) :
    Context input selection (source.extend region)
      (target.extend (Fin.castAdd 2 region)) := by
  rcases witness with ⟨rfl⟩
  refine ⟨?_⟩
  simp only [Concrete.Elaboration.WireContext.extend, exactScopeWires]
  rfl

structure Binders
    (input : Concrete.Diagram) (selection : CheckedSelection input)
    {sourceRels targetRels : RelCtx}
    (source : Concrete.Elaboration.BinderContext input sourceRels)
    (target : Concrete.Elaboration.BinderContext
      (doubleCutIntroRaw input selection) targetRels) : Type where
  rels : sourceRels = targetRels
  equality : ∀ region,
    HEq (source region) (target (Fin.castAdd 2 region))

def Binders.relationMap {sourceRels targetRels : RelCtx}
    {source : Concrete.Elaboration.BinderContext input sourceRels}
    {target : Concrete.Elaboration.BinderContext
      (doubleCutIntroRaw input selection) targetRels}
    (witness : Binders input selection source target) :
    RelationRenaming sourceRels targetRels := by
  cases witness.rels
  exact identityRelationRenaming sourceRels

def Binders.push {sourceRels targetRels : RelCtx}
    {source : Concrete.Elaboration.BinderContext input sourceRels}
    {target : Concrete.Elaboration.BinderContext
      (doubleCutIntroRaw input selection) targetRels}
    (witness : Binders input selection source target)
    (child : Fin input.regionCount) (arity : Nat) :
    Binders input selection (source.push child arity)
      (target.push (Fin.castAdd 2 child) arity) := by
  refine ⟨congrArg (List.cons arity) witness.rels, ?_⟩
  intro region
  cases witness.rels
  simp only [Concrete.Elaboration.BinderContext.push]
  by_cases equality : region = child
  · subst region
    simp
  · have liftedNe : Fin.castAdd 2 region ≠ Fin.castAdd 2 child := by
      intro lifted
      apply equality
      apply Fin.ext
      exact congrArg
        (fun index : Fin (input.regionCount + 2) => index.val) lifted
    rw [if_neg equality]
    apply heq_of_eq
    split
    · rename_i lifted
      exact False.elim (liftedNe lifted)
    · rw [eq_of_heq (witness.equality region)]

theorem Binders.relationMap_push
    {sourceRels targetRels : RelCtx}
    {source : Concrete.Elaboration.BinderContext input sourceRels}
    {target : Concrete.Elaboration.BinderContext
      (doubleCutIntroRaw input selection) targetRels}
    (witness : Binders input selection source target)
    (child : Fin input.regionCount) (arity : Nat) :
    (relationMap (push witness child arity) :
      RelationRenaming (arity :: sourceRels) (arity :: targetRels)) =
      (RelationRenaming.lift (relationMap witness) arity :
        RelationRenaming (arity :: sourceRels) (arity :: targetRels)) := by
  cases witness.rels
  simpa [relationMap, identityRelationRenaming] using
    (RelationRenaming.lift_id_fun (source := sourceRels) arity).symm

theorem endpointOccurs (input : Concrete.Diagram)
    (selection : CheckedSelection input) (index : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount) :
    (doubleCutIntroRaw input selection).EndpointOccurs index endpoint ↔
      input.EndpointOccurs index endpoint := by
  simp only [Concrete.Diagram.EndpointOccurs, wire, liftCWireRegions]
  rfl

theorem endpointOwner (input : Concrete.Diagram)
    (selection : CheckedSelection input) (endpoint : CEndpoint input.nodeCount) :
    Concrete.Elaboration.endpointOwner? (doubleCutIntroRaw input selection)
        endpoint = Concrete.Elaboration.endpointOwner? input endpoint := by
  unfold Concrete.Elaboration.endpointOwner?
  apply congrArg List.head?
  unfold filterFin
  apply List.filter_congr
  intro index _
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using endpointOccurs input selection index endpoint

theorem resolvePort (input : Concrete.Diagram)
    (selection : CheckedSelection input)
    (source : Concrete.Elaboration.WireContext input)
    (target : Concrete.Elaboration.WireContext
      (doubleCutIntroRaw input selection))
    (witness : Context input selection source target)
    (node : Fin input.nodeCount) (port : CPort) :
    Concrete.Elaboration.resolvePort? (doubleCutIntroRaw input selection)
        target node port =
      (Concrete.Elaboration.resolvePort? input source node port).map
        (Fin.cast (congrArg List.length witness.equality)) := by
  rcases witness with ⟨rfl⟩
  simp only [Concrete.Elaboration.resolvePort?, endpointOwner]
  generalize equality : (do
    let index ← Concrete.Elaboration.endpointOwner? input ⟨node, port⟩
    source.lookup? index) = result
  cases result with
  | none => exact equality.trans rfl
  | some index =>
      apply equality.trans
      simp only [Option.map_some]
      congr 2

theorem selected_node (input : Concrete.Diagram)
    (selection : CheckedSelection input) (index : Fin input.nodeCount)
    (selected : index ∈ selection.val.directNodes) :
    (doubleCutIntroRaw input selection).nodes index =
      match input.nodes index with
      | .atom _ binder => .atom (inner input) (Fin.castAdd 2 binder)
      | .identity _ arity => .identity (inner input) arity := by
  rw [node, if_pos selected]
  cases input.nodes index <;> rfl

theorem unselected_node (input : Concrete.Diagram)
    (selection : CheckedSelection input) (index : Fin input.nodeCount)
    (unselected : index ∉ selection.val.directNodes) :
    (doubleCutIntroRaw input selection).nodes index =
      match input.nodes index with
      | .atom owner binder => .atom (Fin.castAdd 2 owner) (Fin.castAdd 2 binder)
      | .identity owner arity => .identity (Fin.castAdd 2 owner) arity := by
  rw [node, if_neg unselected]
  cases input.nodes index <;> rfl

theorem selected_region (input : Concrete.Diagram)
    (selection : CheckedSelection input) (region : Fin input.regionCount)
    (selected : region ∈ selection.val.childRoots) :
    (doubleCutIntroRaw input selection).regions (Fin.castAdd 2 region) =
      match input.regions region with
      | .sheet => .sheet
      | .cut _ => .cut (inner input)
      | .bubble _ arity => .bubble (inner input) arity := by
  rw [oldRegion, if_pos selected]
  cases input.regions region <;> rfl

theorem unselected_region (input : Concrete.Diagram)
    (selection : CheckedSelection input) (region : Fin input.regionCount)
    (unselected : region ∉ selection.val.childRoots) :
    (doubleCutIntroRaw input selection).regions (Fin.castAdd 2 region) =
      match input.regions region with
      | .sheet => .sheet
      | .cut parent => .cut (Fin.castAdd 2 parent)
      | .bubble parent arity => .bubble (Fin.castAdd 2 parent) arity := by
  rw [oldRegion, if_neg unselected]
  cases input.regions region <;> rfl

theorem regular_node (input : Concrete.Diagram)
    (selection : CheckedSelection input) (region : Fin input.regionCount)
    (regular : region ≠ selection.val.anchor) (index : Fin input.nodeCount)
    (owner : (input.nodes index).region = region) :
    (doubleCutIntroRaw input selection).nodes index =
      match input.nodes index with
      | .atom nodeOwner binder =>
          .atom (Fin.castAdd 2 nodeOwner) (Fin.castAdd 2 binder)
      | .identity nodeOwner arity =>
          .identity (Fin.castAdd 2 nodeOwner) arity := by
  apply unselected_node input selection index
  intro selected
  exact regular (owner.symm.trans
    (selection.property.directNodes_at_anchor index selected))

theorem regular_region (input : Concrete.Diagram)
    (selection : CheckedSelection input) (parent child : Fin input.regionCount)
    (regular : parent ≠ selection.val.anchor)
    (childParent : (input.regions child).parent? = some parent) :
    (doubleCutIntroRaw input selection).regions (Fin.castAdd 2 child) =
      match input.regions child with
      | .sheet => .sheet
      | .cut actualParent => .cut (Fin.castAdd 2 actualParent)
      | .bubble actualParent arity =>
          .bubble (Fin.castAdd 2 actualParent) arity := by
  apply unselected_region input selection child
  intro selected
  exact regular (Option.some.inj
    (childParent.symm.trans
      (selection.property.childRoots_direct child selected)))

theorem regular_localOccurrences (input : Concrete.Diagram)
    (selection : CheckedSelection input) (region : Fin input.regionCount)
    (regular : region ≠ selection.val.anchor) :
    Concrete.Elaboration.localOccurrences (doubleCutIntroRaw input selection)
        (Fin.castAdd 2 region) =
      (Concrete.Elaboration.localOccurrences input region).map
        (fun occurrence => match occurrence with
          | .node node => .node node
          | .child child => .child (Fin.castAdd 2 child)) := by
  unfold Concrete.Elaboration.localOccurrences filterFin
  simp only [nodeCount, regionCount, List.map_append, List.map_map]
  rw [allFin_add input.regionCount 2, List.filter_append,
    List.filter_map, List.map_append]
  have liftNode :
      ((fun occurrence : Concrete.Elaboration.LocalOccurrence
          input.regionCount input.nodeCount => match occurrence with
        | .node node => .node node
        | .child child => .child (Fin.castAdd 2 child)) ∘
          Concrete.Elaboration.LocalOccurrence.node) =
        Concrete.Elaboration.LocalOccurrence.node := by funext node; rfl
  have liftChild :
      ((fun occurrence : Concrete.Elaboration.LocalOccurrence
          input.regionCount input.nodeCount => match occurrence with
        | .node node => .node node
        | .child child => .child (Fin.castAdd 2 child)) ∘
          Concrete.Elaboration.LocalOccurrence.child) =
        Concrete.Elaboration.LocalOccurrence.child ∘ Fin.castAdd 2 := by
    funext child
    rfl
  rw [liftNode, liftChild]
  congr 1
  · apply congrArg (List.map Concrete.Elaboration.LocalOccurrence.node)
    apply congrArg (fun predicate => List.filter predicate (allFin input.nodeCount))
    funext index
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    have targetOwner := node_region input selection index
    by_cases selected : index ∈ selection.val.directNodes
    · have sourceOwner := selection.property.directNodes_at_anchor index selected
      constructor
      · intro atRegion
        rw [if_pos selected] at targetOwner
        exact False.elim (inner_ne_lift input region
          (targetOwner.symm.trans atRegion))
      · intro atRegion
        exact False.elim (regular (sourceOwner.symm.trans atRegion).symm)
    · rw [if_neg selected] at targetOwner
      constructor
      · intro atRegion
        apply Fin.ext
        exact congrArg (fun value : Fin (input.regionCount + 2) => value.val)
          (targetOwner.symm.trans atRegion)
      · intro atRegion
        exact targetOwner.trans (congrArg (Fin.castAdd 2) atRegion)
  · have addedNil :
        List.filter
            (fun child => decide
              (((doubleCutIntroRaw input selection).regions child).parent? =
                some (Fin.castAdd 2 region)))
            (List.map (Fin.natAdd input.regionCount) (allFin 2)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro child member chosen
      have parent := decide_eq_true_eq.mp chosen
      rw [show allFin 2 = [(0 : Fin 2), (1 : Fin 2)] by decide] at member
      simp only [List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at member
      rcases member with isOuter | isInner
      · have equality : Fin.natAdd input.regionCount (0 : Fin 2) = outer input := by
          ext
          rfl
        rw [isOuter, equality, outer_parent] at parent
        apply regular
        apply Fin.ext
        exact (congrArg
          (fun value : Fin (input.regionCount + 2) => value.val)
          (Option.some.inj parent)).symm
      · have equality : Fin.natAdd input.regionCount (1 : Fin 2) = inner input := by
          ext
          rfl
        rw [isInner, equality, inner_parent] at parent
        exact outer_ne_lift input region (Option.some.inj parent)
    have addedOccurrencesNil := congrArg
      (List.map (Concrete.Elaboration.LocalOccurrence.child
        (regions := input.regionCount + 2) (nodes := input.nodeCount))) addedNil
    calc
      _ = List.map
            (Concrete.Elaboration.LocalOccurrence.child
              (regions := input.regionCount + 2) (nodes := input.nodeCount))
            (List.map (Fin.castAdd 2)
              (List.filter
                ((fun child => decide
                  (((doubleCutIntroRaw input selection).regions child).parent? =
                    some (Fin.castAdd 2 region))) ∘ Fin.castAdd 2)
                (allFin input.regionCount))) ++ [] := by
          exact congrArg (fun tail => List.map
            (Concrete.Elaboration.LocalOccurrence.child
              (regions := input.regionCount + 2) (nodes := input.nodeCount))
            (List.map (Fin.castAdd 2)
              (List.filter
                ((fun child => decide
                  (((doubleCutIntroRaw input selection).regions child).parent? =
                    some (Fin.castAdd 2 region))) ∘ Fin.castAdd 2)
                (allFin input.regionCount))) ++ tail) addedOccurrencesNil
      _ = _ := by
        rw [List.append_nil, List.map_map]
        apply congrArg
          (List.map (Concrete.Elaboration.LocalOccurrence.child ∘ Fin.castAdd 2))
        apply congrArg (fun predicate => List.filter predicate (allFin input.regionCount))
        funext child
        apply Bool.eq_iff_iff.mpr
        simp only [Function.comp_apply, decide_eq_true_eq]
        have parentEq := oldRegion_parent input selection child
        by_cases selected : child ∈ selection.val.childRoots
        · have sourceParent := selection.property.childRoots_direct child selected
          constructor
          · intro targetParent
            rw [if_pos selected] at parentEq
            exact False.elim (inner_ne_lift input region
              (Option.some.inj (parentEq.symm.trans targetParent)))
          · intro atRegion
            exact False.elim (regular
              (Option.some.inj (sourceParent.symm.trans atRegion)).symm)
        · rw [if_neg selected] at parentEq
          constructor
          · intro targetParent
            cases sourceParent : (input.regions child).parent? with
            | none =>
                rw [parentEq, sourceParent] at targetParent
                cases targetParent
            | some actual =>
                rw [sourceParent] at parentEq
                apply congrArg some
                apply Fin.ext
                exact congrArg
                  (fun value : Fin (input.regionCount + 2) => value.val)
                  (Option.some.inj (parentEq.symm.trans targetParent))
          · intro sourceParent
            rw [sourceParent] at parentEq
            exact parentEq

end VisualProof.Refinement.Implementation.DoubleCutTransport
