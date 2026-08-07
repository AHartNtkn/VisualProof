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

end VisualProof.Refinement.Implementation.DoubleCutTransport
