import VisualProof.Concrete.Step

namespace VisualProof.Refinement.Implementation.WireJoin

open VisualProof.Concrete
open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

structure ContextIndexRelation (source target : Nat) where
  Rel : Fin source → Fin target → Prop

def identityRelationRenaming (rels : RelCtx) : RelationRenaming rels rels :=
  fun relation => relation

abbrev Target (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount) :=
  joinWireRaw input outer inner

def wireMap (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount) (distinct : outer ≠ inner) :
    Fin input.wireCount → Fin (Target input outer inner).wireCount :=
  fun wire =>
    if hwire : wire = inner then
      (joinWireDomain input inner).index outer (by
        simpa [joinWireDomain] using distinct)
    else
      (joinWireDomain input inner).index wire (by
        simpa [joinWireDomain] using hwire)

@[simp] theorem wireMap_inner
    (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount) (distinct : outer ≠ inner) :
    wireMap input outer inner distinct inner =
      (joinWireDomain input inner).index outer
        (by simpa [joinWireDomain] using distinct) := by
  simp [wireMap]

@[simp] theorem wireMap_of_ne
    (input : Concrete.Diagram)
    (outer inner wire : Fin input.wireCount) (distinct : outer ≠ inner)
    (hne : wire ≠ inner) :
    wireMap input outer inner distinct wire =
      (joinWireDomain input inner).index wire
        (by simpa [joinWireDomain] using hne) := by
  simp [wireMap, hne]

theorem origin_wireMap
    (input : Concrete.Diagram)
    (outer inner wire : Fin input.wireCount) (distinct : outer ≠ inner) :
    (joinWireDomain input inner).origin
        (wireMap input outer inner distinct wire) =
      if wire = inner then outer else wire := by
  by_cases hwire : wire = inner
  · subst wire
    rw [if_pos rfl, wireMap_inner]
    exact (joinWireDomain input inner).origin_index outer (by
      simpa [joinWireDomain] using distinct)
  · rw [if_neg hwire,
      wireMap_of_ne input outer inner wire distinct hwire]
    exact (joinWireDomain input inner).origin_index wire (by
      simpa [joinWireDomain] using hwire)

theorem wireMap_surjective
    (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount) (distinct : outer ≠ inner) :
    Function.Surjective (wireMap input outer inner distinct) := by
  intro target
  let source := (joinWireDomain input inner).origin target
  have sourceNe : source ≠ inner := by
    have survives := (joinWireDomain input inner).origin_survives target
    simpa [source, joinWireDomain] using survives
  refine ⟨source, ?_⟩
  rw [wireMap_of_ne input outer inner source distinct sourceNe]
  exact (joinWireDomain input inner).index_origin target

theorem wireMap_eq_iff
    (input : Concrete.Diagram)
    (outer inner left right : Fin input.wireCount)
    (distinct : outer ≠ inner) :
    wireMap input outer inner distinct left =
        wireMap input outer inner distinct right ↔
      left = right ∨
        (left = outer ∧ right = inner) ∨
        (left = inner ∧ right = outer) := by
  constructor
  · intro equality
    have originEquality := congrArg
      (joinWireDomain input inner).origin equality
    rw [origin_wireMap, origin_wireMap] at originEquality
    by_cases hleft : left = inner <;>
      by_cases hright : right = inner
    · exact Or.inl (hleft.trans hright.symm)
    · exact Or.inr (Or.inr ⟨hleft, by
        simpa [hleft, hright] using originEquality.symm⟩)
    · exact Or.inr (Or.inl ⟨by
        simpa [hleft, hright] using originEquality, hright⟩)
    · exact Or.inl (by simpa [hleft, hright] using originEquality)
  · intro cases
    rcases cases with same | outerInner | innerOuter
    · subst right
      rfl
    · rcases outerInner with ⟨leftEq, rightEq⟩
      subst left
      subst right
      rw [wireMap_of_ne input outer inner outer distinct distinct,
          wireMap_inner]
    · rcases innerOuter with ⟨leftEq, rightEq⟩
      subst left
      subst right
      rw [wireMap_inner,
          wireMap_of_ne input outer inner outer distinct distinct]

@[simp] theorem target_regionCount
    (input : Concrete.Diagram) (outer inner : Fin input.wireCount) :
    (Target input outer inner).regionCount = input.regionCount :=
  rfl

@[simp] theorem target_nodeCount
    (input : Concrete.Diagram) (outer inner : Fin input.wireCount) :
    (Target input outer inner).nodeCount = input.nodeCount :=
  rfl

@[simp] theorem target_root
    (input : Concrete.Diagram) (outer inner : Fin input.wireCount) :
    (Target input outer inner).root = input.root :=
  rfl

@[simp] theorem target_regions
    (input : Concrete.Diagram) (outer inner : Fin input.wireCount)
    (region : Fin input.regionCount) :
    (Target input outer inner).regions region = input.regions region :=
  rfl

@[simp] theorem target_nodes
    (input : Concrete.Diagram) (outer inner : Fin input.wireCount)
    (node : Fin input.nodeCount) :
    (Target input outer inner).nodes node = input.nodes node :=
  rfl

theorem target_wire_scope
    (input : Concrete.Diagram)
    (outer inner wire : Fin input.wireCount) (distinct : outer ≠ inner) :
    ((Target input outer inner).wires
      (wireMap input outer inner distinct wire)).scope =
        if wire = inner then
          (input.wires outer).scope
        else
          (input.wires wire).scope := by
  change
    (if (joinWireDomain input inner).origin
          (wireMap input outer inner distinct wire) = outer then
        { scope := (input.wires outer).scope
          endpoints := (input.wires outer).endpoints ++
            (input.wires inner).endpoints }
      else
        input.wires ((joinWireDomain input inner).origin
          (wireMap input outer inner distinct wire))).scope = _
  rw [origin_wireMap]
  by_cases hwire : wire = inner
  · simp [hwire]
  · by_cases houter : wire = outer
    · simp [houter]
    · simp [hwire, houter]

theorem target_wire_scope_origin
    (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount)
    (targetWire : Fin (Target input outer inner).wireCount) :
    ((Target input outer inner).wires targetWire).scope =
      if (joinWireDomain input inner).origin targetWire = outer then
        (input.wires outer).scope
      else
        (input.wires
          ((joinWireDomain input inner).origin targetWire)).scope := by
  change
    (if (joinWireDomain input inner).origin targetWire = outer then
        { scope := (input.wires outer).scope
          endpoints := (input.wires outer).endpoints ++
            (input.wires inner).endpoints }
      else
        input.wires
          ((joinWireDomain input inner).origin targetWire)).scope = _
  by_cases houter :
      (joinWireDomain input inner).origin targetWire = outer
  · rw [if_pos houter, if_pos houter]
  · rw [if_neg houter, if_neg houter]

theorem target_climb
    (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount)
    (steps : Nat) (region : Fin input.regionCount) :
    (Target input outer inner).climb steps region =
      input.climb steps region := by
  induction steps generalizing region with
  | zero => rfl
  | succ steps induction =>
      cases parent : (input.regions region).parent? with
      | none =>
          simp [Concrete.Diagram.climb, target_regions, parent]
      | some directParent =>
          simpa [Concrete.Diagram.climb, target_regions, parent] using
            induction directParent

theorem target_encloses_iff
    (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount)
    (ancestor descendant : Fin input.regionCount) :
    (Target input outer inner).Encloses ancestor descendant ↔
      input.Encloses ancestor descendant := by
  unfold Concrete.Diagram.Encloses
  constructor <;> rintro ⟨steps, encloses⟩ <;>
    exact ⟨steps, by simpa [target_climb] using encloses⟩

theorem endpointOccurs_map
    (input : Concrete.Diagram)
    (outer inner wire : Fin input.wireCount) (distinct : outer ≠ inner)
    (endpoint : CEndpoint input.nodeCount)
    (occurs : input.EndpointOccurs wire endpoint) :
    (Target input outer inner).EndpointOccurs
      (wireMap input outer inner distinct wire) endpoint := by
  unfold Concrete.Diagram.EndpointOccurs at occurs ⊢
  change endpoint ∈
    (if (joinWireDomain input inner).origin
          (wireMap input outer inner distinct wire) = outer then
        { scope := (input.wires outer).scope
          endpoints := (input.wires outer).endpoints ++
            (input.wires inner).endpoints }
      else
        input.wires ((joinWireDomain input inner).origin
          (wireMap input outer inner distinct wire))).endpoints
  rw [origin_wireMap]
  by_cases hwire : wire = inner
  · subst wire
    simp [occurs]
  · by_cases houter : wire = outer
    · subst wire
      simp [hwire, occurs]
    · simpa [hwire, houter] using occurs

theorem visible_map
    (input : Concrete.Diagram)
    (wellFormed : input.WellFormed )
    (outer inner wire : Fin input.wireCount) (distinct : outer ≠ inner)
    (ordered :
      input.Encloses (input.wires outer).scope (input.wires inner).scope)
    (region : Fin input.regionCount)
    (visible : input.Encloses (input.wires wire).scope region) :
    (Target input outer inner).Encloses
      ((Target input outer inner).wires
        (wireMap input outer inner distinct wire)).scope region := by
  rw [target_wire_scope]
  by_cases hwire : wire = inner
  · subst wire
    rw [if_pos rfl]
    rw [target_encloses_iff]
    exact Concrete.Elaboration.checked_encloses_trans wellFormed ordered visible
  · rw [if_neg hwire, target_encloses_iff]
    exact visible

theorem visible_preimage
    (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount) (distinct : outer ≠ inner)
    (region : Fin input.regionCount)
    (targetWire : Fin (Target input outer inner).wireCount)
    (visible :
      (Target input outer inner).Encloses
        ((Target input outer inner).wires targetWire).scope region) :
    ∃ sourceWire,
      input.Encloses (input.wires sourceWire).scope region ∧
        wireMap input outer inner distinct sourceWire = targetWire := by
  let sourceWire := (joinWireDomain input inner).origin targetWire
  have sourceNe : sourceWire ≠ inner := by
    have survives := (joinWireDomain input inner).origin_survives targetWire
    simpa [sourceWire, joinWireDomain] using survives
  refine ⟨sourceWire, ?_, ?_⟩
  · rw [target_wire_scope_origin, target_encloses_iff] at visible
    change input.Encloses
      (if sourceWire = outer then
        (input.wires outer).scope
      else
        (input.wires sourceWire).scope) region at visible
    by_cases houter : sourceWire = outer
    · simpa [houter] using visible
    · simpa [houter] using visible
  · rw [wireMap_of_ne input outer inner sourceWire distinct sourceNe]
    exact (joinWireDomain input inner).index_origin targetWire

def contextRelation
    (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount) (distinct : outer ≠ inner)
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext :
      Concrete.Elaboration.WireContext (Target input outer inner)) :
    ContextIndexRelation
      sourceContext.length targetContext.length where
  Rel sourceIndex targetIndex :=
    wireMap input outer inner distinct (sourceContext.get sourceIndex) =
      targetContext.get targetIndex

structure ContextWitness
    (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount) (distinct : outer ≠ inner)
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext :
      Concrete.Elaboration.WireContext (Target input outer inner)) where
  indexMap : Fin sourceContext.length → Fin targetContext.length
  get : ∀ sourceIndex,
    targetContext.get (indexMap sourceIndex) =
      wireMap input outer inner distinct (sourceContext.get sourceIndex)
  surjective : Function.Surjective indexMap

noncomputable def ContextWitness.ofExact
    (input : Concrete.Diagram)
    (wellFormed : input.WellFormed )
    (outer inner : Fin input.wireCount) (distinct : outer ≠ inner)
    (ordered :
      input.Encloses (input.wires outer).scope (input.wires inner).scope)
    (region : Fin input.regionCount)
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext :
      Concrete.Elaboration.WireContext (Target input outer inner))
    (sourceExact : sourceContext.Exact region)
    (targetExact : targetContext.Exact region) :
    ContextWitness input outer inner distinct sourceContext targetContext := by
  let indexMap : Fin sourceContext.length → Fin targetContext.length :=
    fun sourceIndex => Classical.choose (by
      have sourceMember := List.get_mem sourceContext sourceIndex
      have sourceVisible := (sourceExact.mem_iff _).1 sourceMember
      have targetVisible := visible_map input wellFormed outer inner
        (sourceContext.get sourceIndex) distinct ordered region sourceVisible
      exact Concrete.Elaboration.WireContext.lookup?_complete
        ((targetExact.mem_iff _).2 targetVisible))
  have get : ∀ sourceIndex,
      targetContext.get (indexMap sourceIndex) =
        wireMap input outer inner distinct
          (sourceContext.get sourceIndex) := by
    intro sourceIndex
    have sourceMember := List.get_mem sourceContext sourceIndex
    have sourceVisible := (sourceExact.mem_iff _).1 sourceMember
    have targetVisible := visible_map input wellFormed outer inner
      (sourceContext.get sourceIndex) distinct ordered region sourceVisible
    have targetMember := (targetExact.mem_iff _).2 targetVisible
    exact Concrete.Elaboration.WireContext.lookup?_sound
      (Classical.choose_spec
        (Concrete.Elaboration.WireContext.lookup?_complete targetMember))
  refine ⟨indexMap, get, ?_⟩
  intro targetIndex
  have targetMember := List.get_mem targetContext targetIndex
  have targetVisible := (targetExact.mem_iff _).1 targetMember
  obtain ⟨sourceWire, sourceVisible, mapped⟩ :=
    visible_preimage input outer inner distinct region
      (targetContext.get targetIndex) targetVisible
  have sourceMember := (sourceExact.mem_iff _).2 sourceVisible
  obtain ⟨sourceIndex, lookup⟩ :=
    Concrete.Elaboration.WireContext.lookup?_complete sourceMember
  refine ⟨sourceIndex, ?_⟩
  apply Fin.ext
  apply (List.getElem_inj targetExact.nodup).mp
  have sourceGet :=
    Concrete.Elaboration.WireContext.lookup?_sound lookup
  have mappedGet :
      wireMap input outer inner distinct (sourceContext.get sourceIndex) =
        targetContext.get targetIndex :=
    (congrArg (wireMap input outer inner distinct) sourceGet).trans mapped
  simpa only [List.get_eq_getElem] using
    (get sourceIndex).trans mappedGet

noncomputable def localMap
    (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount) (distinct : outer ≠ inner)
    (region : Fin input.regionCount)
    (hne : region ≠ (input.wires inner).scope) :
    Fin (Concrete.Elaboration.exactScopeWires input region).length →
      Fin (Concrete.Elaboration.exactScopeWires
        (Target input outer inner) region).length :=
  fun sourceIndex =>
    let sourceWire :=
      (Concrete.Elaboration.exactScopeWires input region).get sourceIndex
    let targetWire := wireMap input outer inner distinct sourceWire
    have sourceScope : (input.wires sourceWire).scope = region :=
      (Concrete.Elaboration.mem_exactScopeWires input region sourceWire).1
        (List.get_mem _ sourceIndex)
    have sourceNe : sourceWire ≠ inner := by
      intro equality
      exact hne (by simpa [equality] using sourceScope.symm)
    have targetScope :
        ((Target input outer inner).wires targetWire).scope = region := by
      rw [target_wire_scope input outer inner sourceWire distinct,
        if_neg sourceNe]
      exact sourceScope
    Classical.choose
      (Concrete.Elaboration.WireContext.lookup?_complete
        ((Concrete.Elaboration.mem_exactScopeWires
          (Target input outer inner) region targetWire).2 targetScope))

theorem localMap_get
    (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount) (distinct : outer ≠ inner)
    (region : Fin input.regionCount)
    (hne : region ≠ (input.wires inner).scope)
    (sourceIndex :
      Fin (Concrete.Elaboration.exactScopeWires input region).length) :
    (Concrete.Elaboration.exactScopeWires
      (Target input outer inner) region).get
        (localMap input outer inner distinct region hne sourceIndex) =
      wireMap input outer inner distinct
        ((Concrete.Elaboration.exactScopeWires input region).get
          sourceIndex) := by
  exact Concrete.Elaboration.WireContext.lookup?_sound
    (Classical.choose_spec
      (Concrete.Elaboration.WireContext.lookup?_complete
        ((Concrete.Elaboration.mem_exactScopeWires
          (Target input outer inner) region
          (wireMap input outer inner distinct
            ((Concrete.Elaboration.exactScopeWires input region).get
              sourceIndex))).2 (by
            have sourceScope :=
              (Concrete.Elaboration.mem_exactScopeWires input region
                ((Concrete.Elaboration.exactScopeWires input region).get
                  sourceIndex)).1 (List.get_mem _ sourceIndex)
            have sourceNe :
                (Concrete.Elaboration.exactScopeWires input region).get
                    sourceIndex ≠ inner := by
              intro equality
              rw [equality] at sourceScope
              exact hne sourceScope.symm
            rw [target_wire_scope, if_neg sourceNe]
            exact sourceScope))))

theorem localMap_injective
    (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount) (distinct : outer ≠ inner)
    (region : Fin input.regionCount)
    (hne : region ≠ (input.wires inner).scope) :
    Function.Injective (localMap input outer inner distinct region hne) := by
  intro left right equality
  have targetGetEquality := congrArg
    (List.get (Concrete.Elaboration.exactScopeWires
      (Target input outer inner) region)) equality
  rw [localMap_get, localMap_get] at targetGetEquality
  have mapped :=
    (wireMap_eq_iff input outer inner
      ((Concrete.Elaboration.exactScopeWires input region).get left)
      ((Concrete.Elaboration.exactScopeWires input region).get right)
      distinct).1 targetGetEquality
  have sourceGetEquality :
      (Concrete.Elaboration.exactScopeWires input region).get left =
        (Concrete.Elaboration.exactScopeWires input region).get right := by
    rcases mapped with same | outerInner | innerOuter
    · exact same
    · rcases outerInner with ⟨_, rightInner⟩
      have rightScope :=
        (Concrete.Elaboration.mem_exactScopeWires input region
          ((Concrete.Elaboration.exactScopeWires input region).get right)).1
          (List.get_mem _ right)
      rw [rightInner] at rightScope
      exact False.elim (hne rightScope.symm)
    · rcases innerOuter with ⟨leftInner, _⟩
      have leftScope :=
        (Concrete.Elaboration.mem_exactScopeWires input region
          ((Concrete.Elaboration.exactScopeWires input region).get left)).1
          (List.get_mem _ left)
      rw [leftInner] at leftScope
      exact False.elim (hne leftScope.symm)
  apply Fin.ext
  exact (List.getElem_inj
    (Concrete.Elaboration.exactScopeWires_nodup input region)).mp
      (by simpa only [List.get_eq_getElem] using sourceGetEquality)

theorem localMap_surjective
    (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount) (distinct : outer ≠ inner)
    (region : Fin input.regionCount)
    (hne : region ≠ (input.wires inner).scope) :
    Function.Surjective
      (localMap input outer inner distinct region hne) := by
  intro targetIndex
  let targetWire :=
    (Concrete.Elaboration.exactScopeWires
      (Target input outer inner) region).get targetIndex
  have targetScope :
      ((Target input outer inner).wires targetWire).scope = region :=
    (Concrete.Elaboration.mem_exactScopeWires
      (Target input outer inner) region targetWire).1
      (List.get_mem _ targetIndex)
  let sourceWire := (joinWireDomain input inner).origin targetWire
  have sourceNe : sourceWire ≠ inner := by
    have survives := (joinWireDomain input inner).origin_survives targetWire
    simpa [sourceWire, joinWireDomain] using survives
  have mapped :
      wireMap input outer inner distinct sourceWire = targetWire := by
    rw [wireMap_of_ne input outer inner sourceWire distinct sourceNe]
    exact (joinWireDomain input inner).index_origin targetWire
  have sourceScope : (input.wires sourceWire).scope = region := by
    rw [target_wire_scope_origin] at targetScope
    change
      (if sourceWire = outer then
        (input.wires outer).scope
      else
        (input.wires sourceWire).scope) = region at targetScope
    by_cases houter : sourceWire = outer
    · simpa [houter] using targetScope
    · simpa [houter] using targetScope
  have sourceMember :=
    (Concrete.Elaboration.mem_exactScopeWires input region sourceWire).2
      sourceScope
  obtain ⟨sourceIndex, lookup⟩ :=
    Concrete.Elaboration.WireContext.lookup?_complete sourceMember
  refine ⟨sourceIndex, ?_⟩
  have sourceGet :=
    Concrete.Elaboration.WireContext.lookup?_sound lookup
  have targetGet :
      (Concrete.Elaboration.exactScopeWires
        (Target input outer inner) region).get
          (localMap input outer inner distinct region hne sourceIndex) =
        targetWire := by
    calc
      _ = wireMap input outer inner distinct
          ((Concrete.Elaboration.exactScopeWires input region).get
            sourceIndex) :=
        localMap_get input outer inner distinct region hne sourceIndex
      _ = wireMap input outer inner distinct sourceWire :=
        congrArg (wireMap input outer inner distinct) sourceGet
      _ = targetWire := mapped
  apply Fin.ext
  exact (List.getElem_inj
    (Concrete.Elaboration.exactScopeWires_nodup
      (Target input outer inner) region)).mp (by
        simpa only [List.get_eq_getElem] using targetGet)

noncomputable def ContextWitness.extend
    (_witness : ContextWitness input outer inner distinct
      sourceContext targetContext)
    (wellFormed : input.WellFormed )
    (ordered :
      input.Encloses (input.wires outer).scope (input.wires inner).scope)
    (region : Fin input.regionCount)
    (sourceExact : (sourceContext.extend region).Exact region)
    (targetExact : (targetContext.extend region).Exact region) :
    ContextWitness input outer inner distinct
      (sourceContext.extend region) (targetContext.extend region) :=
  ContextWitness.ofExact input wellFormed outer inner distinct ordered region
    (sourceContext.extend region) (targetContext.extend region)
    sourceExact targetExact

theorem ContextWitness.extend_index_inherited
    (witness : ContextWitness input outer inner distinct
      sourceContext targetContext)
    (wellFormed : input.WellFormed )
    (ordered :
      input.Encloses (input.wires outer).scope (input.wires inner).scope)
    (region : Fin input.regionCount)
    (sourceExact : (sourceContext.extend region).Exact region)
    (targetExact : (targetContext.extend region).Exact region)
    (sourceIndex : Fin sourceContext.length) :
    (witness.extend wellFormed ordered region sourceExact targetExact).indexMap
        (Fin.cast
          (Concrete.Elaboration.WireContext.length_extend sourceContext
            region).symm
          (Fin.castAdd
            (Concrete.Elaboration.exactScopeWires input region).length
            sourceIndex)) =
      Fin.cast
        (Concrete.Elaboration.WireContext.length_extend targetContext
          region).symm
        (Fin.castAdd
          (Concrete.Elaboration.exactScopeWires
            (Target input outer inner) region).length
          (witness.indexMap sourceIndex)) := by
  let sourceExtendedIndex : Fin (sourceContext.extend region).length :=
    Fin.cast
      (Concrete.Elaboration.WireContext.length_extend sourceContext region).symm
      (Fin.castAdd
        (Concrete.Elaboration.exactScopeWires input region).length sourceIndex)
  let targetExtendedIndex : Fin (targetContext.extend region).length :=
    Fin.cast
      (Concrete.Elaboration.WireContext.length_extend targetContext region).symm
      (Fin.castAdd
        (Concrete.Elaboration.exactScopeWires
          (Target input outer inner) region).length
        (witness.indexMap sourceIndex))
  change
    (witness.extend wellFormed ordered region sourceExact targetExact).indexMap
      sourceExtendedIndex = targetExtendedIndex
  apply Fin.ext
  have sourceGet :
      (sourceContext.extend region).get sourceExtendedIndex =
        sourceContext.get sourceIndex := by
    simp [sourceExtendedIndex, Concrete.Elaboration.WireContext.extend]
  have targetGet :
      (targetContext.extend region).get targetExtendedIndex =
        targetContext.get (witness.indexMap sourceIndex) := by
    simp [targetExtendedIndex, Concrete.Elaboration.WireContext.extend]
  have mappedGet :=
    (witness.extend wellFormed ordered region sourceExact targetExact).get
      sourceExtendedIndex
  rw [sourceGet] at mappedGet
  have hget :
      (targetContext.extend region).get
          ((witness.extend wellFormed ordered region sourceExact
            targetExact).indexMap sourceExtendedIndex) =
        (targetContext.extend region).get targetExtendedIndex :=
    (mappedGet.trans (witness.get sourceIndex).symm).trans targetGet.symm
  exact (List.getElem_inj targetExact.nodup).mp (by
    simpa only [List.get_eq_getElem] using hget)

theorem ContextWitness.extend_index_local_of_ne
    (witness : ContextWitness input outer inner distinct
      sourceContext targetContext)
    (wellFormed : input.WellFormed )
    (ordered :
      input.Encloses (input.wires outer).scope (input.wires inner).scope)
    (region : Fin input.regionCount)
    (hne : region ≠ (input.wires inner).scope)
    (sourceExact : (sourceContext.extend region).Exact region)
    (targetExact : (targetContext.extend region).Exact region)
    (sourceLocal :
      Fin (Concrete.Elaboration.exactScopeWires input region).length) :
    (witness.extend wellFormed ordered region sourceExact targetExact).indexMap
        (Fin.cast
          (Concrete.Elaboration.WireContext.length_extend sourceContext
            region).symm
          (Fin.natAdd sourceContext.length sourceLocal)) =
      Fin.cast
        (Concrete.Elaboration.WireContext.length_extend targetContext
          region).symm
        (Fin.natAdd targetContext.length
          (localMap input outer inner distinct region hne sourceLocal)) := by
  let sourceExtendedIndex : Fin (sourceContext.extend region).length :=
    Fin.cast
      (Concrete.Elaboration.WireContext.length_extend sourceContext region).symm
      (Fin.natAdd sourceContext.length sourceLocal)
  let targetExtendedIndex : Fin (targetContext.extend region).length :=
    Fin.cast
      (Concrete.Elaboration.WireContext.length_extend targetContext region).symm
      (Fin.natAdd targetContext.length
        (localMap input outer inner distinct region hne sourceLocal))
  change
    (witness.extend wellFormed ordered region sourceExact targetExact).indexMap
      sourceExtendedIndex = targetExtendedIndex
  apply Fin.ext
  have sourceGet :
      (sourceContext.extend region).get sourceExtendedIndex =
        (Concrete.Elaboration.exactScopeWires input region).get sourceLocal := by
    simp [sourceExtendedIndex, Concrete.Elaboration.WireContext.extend]
  have targetGet :
      (targetContext.extend region).get targetExtendedIndex =
        (Concrete.Elaboration.exactScopeWires
          (Target input outer inner) region).get
            (localMap input outer inner distinct region hne sourceLocal) := by
    simp [targetExtendedIndex, Concrete.Elaboration.WireContext.extend]
  have mappedGet :=
    (witness.extend wellFormed ordered region sourceExact targetExact).get
      sourceExtendedIndex
  rw [sourceGet] at mappedGet
  have hget :
      (targetContext.extend region).get
          ((witness.extend wellFormed ordered region sourceExact
            targetExact).indexMap sourceExtendedIndex) =
        (targetContext.extend region).get targetExtendedIndex :=
    (mappedGet.trans
      (localMap_get input outer inner distinct region hne sourceLocal).symm)
        |>.trans targetGet.symm
  exact (List.getElem_inj targetExact.nodup).mp (by
    simpa only [List.get_eq_getElem] using hget)

noncomputable def localInverse
    (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount) (distinct : outer ≠ inner)
    (region : Fin input.regionCount)
    (hne : region ≠ (input.wires inner).scope)
    (targetIndex : Fin (Concrete.Elaboration.exactScopeWires
      (Target input outer inner) region).length) :
    Fin (Concrete.Elaboration.exactScopeWires input region).length :=
  Classical.choose
    (localMap_surjective input outer inner distinct region hne targetIndex)

@[simp] theorem target_localOccurrences
    (input : Concrete.Diagram) (outer inner : Fin input.wireCount)
    (region : Fin input.regionCount) :
    Concrete.Elaboration.localOccurrences (Target input outer inner) region =
      Concrete.Elaboration.localOccurrences input region := by
  unfold Concrete.Elaboration.localOccurrences
  simp only [target_nodeCount, target_regionCount, target_nodes,
    target_regions]
  rfl

def targetOpenRaw
    (source : Concrete.OpenDiagram)
    (outer inner : Fin source.diagram.wireCount)
    (distinct : outer ≠ inner) :
    Concrete.OpenDiagram where
  diagram := Target source.diagram outer inner
  boundary := source.boundary.map
    (wireMap source.diagram outer inner distinct)

theorem targetOpenRaw_wellFormed
    (source : Concrete.CheckedOpen )
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.val.diagram.Encloses
      (source.val.diagram.wires outer).scope
      (source.val.diagram.wires inner).scope)
    (targetWellFormed :
      (Target source.val.diagram outer inner).WellFormed ) :
    (targetOpenRaw source.val outer inner distinct).WellFormed  where
  diagram_well_formed := targetWellFormed
  boundary_is_root_scoped := by
    intro targetWire targetMember
    change targetWire ∈ source.val.boundary.map
      (wireMap source.val.diagram outer inner distinct) at targetMember
    obtain ⟨sourceWire, sourceMember, rfl⟩ :=
      List.mem_map.mp targetMember
    have sourceRoot :=
      source.property.boundary_is_root_scoped sourceWire sourceMember
    change
      ((Target source.val.diagram outer inner).wires
        (wireMap source.val.diagram outer inner distinct sourceWire)).scope =
        (Target source.val.diagram outer inner).root
    rw [target_wire_scope]
    by_cases hwire : sourceWire = inner
    · subst sourceWire
      rw [if_pos rfl]
      have outerEnclosesRoot :
          source.val.diagram.Encloses
            (source.val.diagram.wires outer).scope
            source.val.diagram.root := by
        rw [← sourceRoot]
        exact ordered
      exact Concrete.Elaboration.encloses_sheet_eq
        source.property.diagram_well_formed.root_is_sheet
        outerEnclosesRoot
    · simpa [hwire] using sourceRoot

def targetOpen
    (source : Concrete.CheckedOpen )
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.val.diagram.Encloses
      (source.val.diagram.wires outer).scope
      (source.val.diagram.wires inner).scope)
    (targetWellFormed :
      (Target source.val.diagram outer inner).WellFormed ) :
    Concrete.CheckedOpen  :=
  ⟨targetOpenRaw source.val outer inner distinct,
    targetOpenRaw_wellFormed source outer inner distinct ordered
      targetWellFormed⟩

theorem targetOpenRaw_exposed_mem_iff
    (source : Concrete.OpenDiagram)
    (outer inner : Fin source.diagram.wireCount)
    (distinct : outer ≠ inner)
    (targetWire : Fin (Target source.diagram outer inner).wireCount) :
    targetWire ∈
        (targetOpenRaw source outer inner distinct).exposedWires ↔
      ∃ sourceWire ∈ source.exposedWires,
        wireMap source.diagram outer inner distinct sourceWire = targetWire := by
  unfold Concrete.OpenDiagram.exposedWires targetOpenRaw
  simp only [List.mem_eraseDups, List.mem_map]

noncomputable def exposedMap
    (source : Concrete.OpenDiagram)
    (outer inner : Fin source.diagram.wireCount)
    (distinct : outer ≠ inner) :
    Fin source.exposedWires.length →
      Fin (targetOpenRaw source outer inner distinct).exposedWires.length :=
  fun sourceIndex =>
    Classical.choose
      (Concrete.Elaboration.WireContext.lookup?_complete
        ((targetOpenRaw_exposed_mem_iff source outer inner distinct _).2
          ⟨source.exposedWires.get sourceIndex,
            List.get_mem _ sourceIndex, rfl⟩))

theorem exposedMap_get
    (source : Concrete.OpenDiagram)
    (outer inner : Fin source.diagram.wireCount)
    (distinct : outer ≠ inner)
    (sourceIndex : Fin source.exposedWires.length) :
    (targetOpenRaw source outer inner distinct).exposedWires.get
        (exposedMap source outer inner distinct sourceIndex) =
      wireMap source.diagram outer inner distinct
        (source.exposedWires.get sourceIndex) := by
  exact Concrete.Elaboration.WireContext.lookup?_sound
    (Classical.choose_spec
      (Concrete.Elaboration.WireContext.lookup?_complete
        ((targetOpenRaw_exposed_mem_iff source outer inner distinct _).2
          ⟨source.exposedWires.get sourceIndex,
            List.get_mem _ sourceIndex, rfl⟩)))

theorem exposedMap_surjective
    (source : Concrete.OpenDiagram)
    (outer inner : Fin source.diagram.wireCount)
    (distinct : outer ≠ inner) :
    Function.Surjective (exposedMap source outer inner distinct) := by
  intro targetIndex
  obtain ⟨sourceWire, sourceMember, mapped⟩ :=
    (targetOpenRaw_exposed_mem_iff source outer inner distinct
      ((targetOpenRaw source outer inner distinct).exposedWires.get
        targetIndex)).1 (List.get_mem _ targetIndex)
  obtain ⟨sourceIndex, lookup⟩ :=
    Concrete.Elaboration.WireContext.lookup?_complete sourceMember
  refine ⟨sourceIndex, ?_⟩
  apply Fin.ext
  exact (List.getElem_inj
    (targetOpenRaw source outer inner distinct).exposedWires_nodup).mp (by
  have sourceGet :=
    Concrete.Elaboration.WireContext.lookup?_sound lookup
  have chosenGet := exposedMap_get source outer inner distinct sourceIndex
  simpa only [List.get_eq_getElem] using
    chosenGet.trans
      ((congrArg (wireMap source.diagram outer inner distinct)
        sourceGet).trans mapped))

theorem exposedMap_injective_of_root_ne
    (source : Concrete.CheckedOpen )
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (rootNe : source.val.diagram.root ≠
      (source.val.diagram.wires inner).scope) :
    Function.Injective (exposedMap source.val outer inner distinct) := by
  intro left right equality
  have getEquality := congrArg
    (List.get
      (targetOpenRaw source.val outer inner distinct).exposedWires) equality
  rw [exposedMap_get, exposedMap_get] at getEquality
  have mapped := (wireMap_eq_iff source.val.diagram outer inner
    (source.val.exposedWires.get left)
    (source.val.exposedWires.get right) distinct).1 getEquality
  have sourceGetEquality :
      source.val.exposedWires.get left =
        source.val.exposedWires.get right := by
    rcases mapped with same | outerInner | innerOuter
    · exact same
    · rcases outerInner with ⟨_, rightInner⟩
      have rightRoot := source.property.exposed_root_scoped
        (List.get_mem source.val.exposedWires right)
      rw [rightInner] at rightRoot
      exact False.elim (rootNe rightRoot.symm)
    · rcases innerOuter with ⟨leftInner, _⟩
      have leftRoot := source.property.exposed_root_scoped
        (List.get_mem source.val.exposedWires left)
      rw [leftInner] at leftRoot
      exact False.elim (rootNe leftRoot.symm)
  apply Fin.ext
  exact (List.getElem_inj source.val.exposedWires_nodup).mp (by
    simpa only [List.get_eq_getElem] using sourceGetEquality)

def leftIndex (left right : List α) :
    Fin left.length → Fin (left ++ right).length :=
  fun index => Fin.cast
    (by simp : left.length + right.length = (left ++ right).length)
    (Fin.castAdd right.length index)

@[simp] theorem get_leftIndex (left right : List α)
    (index : Fin left.length) :
    (left ++ right).get (leftIndex left right index) = left.get index := by
  simp [leftIndex]

noncomputable def rootWitness
    (source : Concrete.CheckedOpen )
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.val.diagram.Encloses
      (source.val.diagram.wires outer).scope
      (source.val.diagram.wires inner).scope)
    (targetWellFormed :
      (Target source.val.diagram outer inner).WellFormed ) :
    ContextWitness source.val.diagram outer inner distinct
      (source.val.exposedWires ++ source.val.hiddenWires)
      ((targetOpenRaw source.val outer inner distinct).exposedWires ++
        (targetOpenRaw source.val outer inner distinct).hiddenWires) :=
  ContextWitness.ofExact source.val.diagram
    source.property.diagram_well_formed outer inner distinct ordered
    source.val.diagram.root
    (source.val.exposedWires ++ source.val.hiddenWires)
    ((targetOpenRaw source.val outer inner distinct).exposedWires ++
      (targetOpenRaw source.val outer inner distinct).hiddenWires)
    (by
      simpa only [Concrete.OpenDiagram.rootWires] using
        Concrete.Elaboration.openRootWires_exact source.property)
    (by
      let target := targetOpen source outer inner distinct ordered
        targetWellFormed
      simpa only [Concrete.OpenDiagram.rootWires] using
        Concrete.Elaboration.openRootWires_exact target.property)

theorem rootWitness_index_exposed
    (source : Concrete.CheckedOpen )
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.val.diagram.Encloses
      (source.val.diagram.wires outer).scope
      (source.val.diagram.wires inner).scope)
    (targetWellFormed :
      (Target source.val.diagram outer inner).WellFormed )
    (sourceIndex : Fin source.val.exposedWires.length) :
    (rootWitness source outer inner distinct ordered targetWellFormed).indexMap
        (leftIndex source.val.exposedWires source.val.hiddenWires
          sourceIndex) =
      leftIndex
        (targetOpenRaw source.val outer inner distinct).exposedWires
        (targetOpenRaw source.val outer inner distinct).hiddenWires
        (exposedMap source.val outer inner distinct sourceIndex) := by
  let witness := rootWitness source outer inner distinct ordered
    targetWellFormed
  change witness.indexMap
      (leftIndex source.val.exposedWires source.val.hiddenWires sourceIndex) =
    leftIndex
      (targetOpenRaw source.val outer inner distinct).exposedWires
      (targetOpenRaw source.val outer inner distinct).hiddenWires
      (exposedMap source.val outer inner distinct sourceIndex)
  apply Fin.ext
  have mappedGet := witness.get
    (leftIndex source.val.exposedWires source.val.hiddenWires sourceIndex)
  have hget :
      ((targetOpenRaw source.val outer inner distinct).exposedWires ++
          (targetOpenRaw source.val outer inner distinct).hiddenWires).get
          (witness.indexMap
            (leftIndex source.val.exposedWires source.val.hiddenWires
              sourceIndex)) =
        ((targetOpenRaw source.val outer inner distinct).exposedWires ++
          (targetOpenRaw source.val outer inner distinct).hiddenWires).get
          (leftIndex
            (targetOpenRaw source.val outer inner distinct).exposedWires
            (targetOpenRaw source.val outer inner distinct).hiddenWires
            (exposedMap source.val outer inner distinct sourceIndex)) := by
    rw [get_leftIndex] at mappedGet
    simpa only [get_leftIndex] using
      mappedGet.trans
        (exposedMap_get source.val outer inner distinct sourceIndex).symm
  have targetNodup :
      ((targetOpenRaw source.val outer inner distinct).exposedWires ++
        (targetOpenRaw source.val outer inner distinct).hiddenWires).Nodup := by
    simpa only [Concrete.OpenDiagram.rootWires] using
      (targetOpenRaw source.val outer inner distinct).rootWires_nodup
  exact (List.getElem_inj targetNodup).mp (by
    simpa only [List.get_eq_getElem] using hget)
def rightIndex (left right : List α) :
    Fin right.length → Fin (left ++ right).length :=
  fun index => Fin.cast
    (by simp : left.length + right.length = (left ++ right).length)
    (Fin.natAdd left.length index)

@[simp] theorem get_rightIndex (left right : List α)
    (index : Fin right.length) :
    (left ++ right).get (rightIndex left right index) = right.get index := by
  simp [rightIndex]
theorem boundaryLengthEq
    (source : Concrete.OpenDiagram)
    (outer inner : Fin source.diagram.wireCount)
    (distinct : outer ≠ inner) :
    (targetOpenRaw source outer inner distinct).boundary.length =
      source.boundary.length := by
  simp [targetOpenRaw]

theorem boundaryClass_map
    (source : Concrete.OpenDiagram)
    (outer inner : Fin source.diagram.wireCount)
    (distinct : outer ≠ inner)
    (targetPosition :
      Fin (targetOpenRaw source outer inner distinct).boundary.length) :
    (targetOpenRaw source outer inner distinct).boundaryClass targetPosition =
      exposedMap source outer inner distinct
        (source.boundaryClass
          (Fin.cast (boundaryLengthEq source outer inner distinct)
            targetPosition)) := by
  let sourcePosition :=
    Fin.cast (boundaryLengthEq source outer inner distinct) targetPosition
  apply
    ((targetOpenRaw source outer inner distinct).boundaryClass_complete
      targetPosition
      (exposedMap source outer inner distinct
        (source.boundaryClass sourcePosition)) ?_).symm
  rw [exposedMap_get, source.boundaryClass_sound]
  simp [sourcePosition, targetOpenRaw, List.get_eq_getElem]
private theorem wireMap_index?
    (input : Concrete.Diagram)
    (outer inner sourceWire : Fin input.wireCount)
    (distinct : outer ≠ inner) :
    (if sourceWire = inner then
        (joinWireDomain input inner).index? outer
      else
        (joinWireDomain input inner).index? sourceWire) =
      some (wireMap input outer inner distinct sourceWire) := by
  by_cases sourceEq : sourceWire = inner
  · rw [if_pos sourceEq]
    simp only [wireMap, dif_pos sourceEq]
    exact (joinWireDomain input inner).index?_index outer (by
      simpa [joinWireDomain] using distinct)
  · rw [if_neg sourceEq]
    simp only [wireMap, dif_neg sourceEq]
    exact (joinWireDomain input inner).index?_index sourceWire (by
      simpa [joinWireDomain] using sourceEq)

private theorem interface_image_eq_wireMap_of_some
    (input : Concrete.Diagram)
    (outer inner sourceWire : Fin input.wireCount)
    (distinct : outer ≠ inner)
    (mapped : Fin (Target input outer inner).wireCount)
    (image :
      (joinWireWireTransport input outer inner).image? sourceWire =
        some mapped) :
    mapped = wireMap input outer inner distinct sourceWire := by
  unfold joinWireWireTransport WireTransport.rootFiltered at image
  dsimp only at image
  change
    (if sourceWire = inner then
        (joinWireDomain input inner).index? outer
      else
        (joinWireDomain input inner).index? sourceWire).bind
      (fun candidate =>
        if ((Target input outer inner).wires candidate).scope =
            (Target input outer inner).root then
          some candidate
        else
          none) =
      some mapped at image
  obtain ⟨candidate, candidateImage, filtered⟩ :=
    Option.bind_eq_some_iff.mp image
  have canonical :=
    wireMap_index? input outer inner sourceWire distinct
  have candidateEq :
      candidate = wireMap input outer inner distinct sourceWire :=
    Option.some.inj (candidateImage.symm.trans canonical)
  split at filtered
  · exact (Option.some.inj filtered).symm.trans candidateEq
  · contradiction

theorem interface_transportBoundary_eq_map
    (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner)
    (boundary : List (Fin input.wireCount))
    (mapped : List (Fin (Target input outer inner).wireCount))
    (transport :
      (joinWireWireTransport input outer inner).transportBoundary
          boundary =
        some mapped) :
    mapped = boundary.map (wireMap input outer inner distinct) := by
  have image : ∀ sourceWire, sourceWire ∈ boundary →
      (joinWireWireTransport input outer inner).image? sourceWire =
        some (wireMap input outer inner distinct sourceWire) := by
    intro sourceWire member
    obtain ⟨sourceIndex, sourceGet⟩ := List.mem_iff_get.mp member
    have point :=
      (joinWireWireTransport input outer inner).transportBoundary_get
        transport sourceIndex
    have mappedEq := interface_image_eq_wireMap_of_some input outer inner
      (boundary.get sourceIndex) distinct _ point
    rw [← sourceGet]
    rw [point, mappedEq]
  have canonical :=
    (joinWireWireTransport input outer inner).transportBoundary_eq_map
      (wireMap input outer inner distinct) image
  exact Option.some.inj (transport.symm.trans canonical)

theorem endpointOccurs_preimage
    (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner)
    (targetWire : Fin (Concrete.joinWireRaw input outer inner).wireCount)
    (endpoint : Concrete.CEndpoint input.nodeCount)
    (occurs : (Concrete.joinWireRaw input outer inner).EndpointOccurs
      targetWire endpoint) :
    ∃ sourceWire,
      wireMap input outer inner distinct sourceWire =
        targetWire ∧
      input.EndpointOccurs sourceWire endpoint := by
  let sourceWire := (Concrete.joinWireDomain input inner).origin targetWire
  by_cases isOuter : sourceWire = outer
  · unfold Concrete.Diagram.EndpointOccurs at occurs
    change endpoint ∈
      (if (Concrete.joinWireDomain input inner).origin targetWire = outer then
        { scope := (input.wires outer).scope
          endpoints := (input.wires outer).endpoints ++
            (input.wires inner).endpoints }
      else input.wires
        ((Concrete.joinWireDomain input inner).origin targetWire)).endpoints
      at occurs
    rw [if_pos (by simpa [sourceWire] using isOuter)] at occurs
    rcases List.mem_append.mp occurs with outerOccurs | innerOccurs
    · refine ⟨outer, ?_, outerOccurs⟩
      rw [wireMap_of_ne input outer inner outer
        distinct distinct]
      apply Option.some.inj
      calc
        some ((Concrete.joinWireDomain input inner).index outer _) =
            (Concrete.joinWireDomain input inner).index? outer :=
          ((Concrete.joinWireDomain input inner).index?_index outer _).symm
        _ = (Concrete.joinWireDomain input inner).index? sourceWire :=
          congrArg (Concrete.joinWireDomain input inner).index? isOuter.symm
        _ = some targetWire :=
          (Concrete.joinWireDomain input inner).index?_origin targetWire
    · refine ⟨inner, ?_, innerOccurs⟩
      rw [wireMap_inner]
      apply Option.some.inj
      calc
        some ((Concrete.joinWireDomain input inner).index outer _) =
            (Concrete.joinWireDomain input inner).index? outer :=
          ((Concrete.joinWireDomain input inner).index?_index outer _).symm
        _ = (Concrete.joinWireDomain input inner).index? sourceWire :=
          congrArg (Concrete.joinWireDomain input inner).index? isOuter.symm
        _ = some targetWire :=
          (Concrete.joinWireDomain input inner).index?_origin targetWire
  · have sourceNe : sourceWire ≠ inner := by
      have survives :=
        (Concrete.joinWireDomain input inner).origin_survives targetWire
      simpa [sourceWire, Concrete.joinWireDomain] using survives
    unfold Concrete.Diagram.EndpointOccurs at occurs
    change endpoint ∈
      (if (Concrete.joinWireDomain input inner).origin targetWire = outer then
        { scope := (input.wires outer).scope
          endpoints := (input.wires outer).endpoints ++
            (input.wires inner).endpoints }
      else input.wires
        ((Concrete.joinWireDomain input inner).origin targetWire)).endpoints
      at occurs
    rw [if_neg (by simpa [sourceWire] using isOuter)] at occurs
    refine ⟨sourceWire, ?_, occurs⟩
    rw [wireMap_of_ne input outer inner sourceWire
      distinct sourceNe]
    simpa [sourceWire] using
      (Concrete.joinWireDomain input inner).index_origin targetWire

theorem context_mem_iff
    (input : Concrete.Diagram)
    (wellFormed : input.WellFormed)
    (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner)
    (ordered : input.Encloses (input.wires outer).scope
      (input.wires inner).scope)
    (region : Fin input.regionCount)
    (below : input.Encloses (input.wires inner).scope region)
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext
      (Target input outer inner))
    (sourceExact : sourceContext.Exact region)
    (targetExact : targetContext.Exact region)
    (wire : Fin input.wireCount) :
    wireMap input outer inner distinct wire ∈
        targetContext ↔
      wire ∈ sourceContext := by
  constructor
  · intro targetMember
    apply (sourceExact.mem_iff wire).2
    by_cases isInner : wire = inner
    · simpa only [isInner] using below
    · have targetVisible := (targetExact.mem_iff _).1 targetMember
      rw [target_wire_scope, if_neg isInner,
        target_encloses_iff] at targetVisible
      exact targetVisible
  · intro sourceMember
    apply (targetExact.mem_iff _).2
    exact visible_map input wellFormed outer inner wire
      distinct ordered region ((sourceExact.mem_iff wire).1 sourceMember)

theorem compileNode_map
    (input : Concrete.Diagram)
    (wellFormed : input.WellFormed)
    (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner)
    (ordered : input.Encloses (input.wires outer).scope
      (input.wires inner).scope)
    (targetWellFormed :
      (Target input outer inner).WellFormed)
    (region : Fin input.regionCount)
    (below : input.Encloses (input.wires inner).scope region)
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext
      (Target input outer inner))
    (witness : ContextWitness input outer inner
      distinct sourceContext targetContext)
    (sourceExact : sourceContext.Exact region)
    (targetExact : targetContext.Exact region)
    (binders : Concrete.Elaboration.BinderContext input rels)
    (node : Fin input.nodeCount) :
    Concrete.Elaboration.compileNode?
        (Target input outer inner)
        targetContext binders node =
      (Concrete.Elaboration.compileNode? input sourceContext binders node).map
        (Item.renameWires witness.indexMap) := by
  have nodeShape :
      (Target input outer inner).nodes node =
        match input.nodes node with
        | .atom nodeRegion binder => .atom (id nodeRegion) (id binder)
        | .identity nodeRegion arity => .identity (id nodeRegion) arity := by
    cases shape : input.nodes node <;> simp [shape]
  have ports : ∀ port,
      Concrete.Elaboration.resolvePort?
          (Target input outer inner)
          targetContext node port =
        (Concrete.Elaboration.resolvePort? input sourceContext node port).map
          witness.indexMap := by
    intro port
    exact Concrete.Elaboration.resolvePort?_map_of_occurrence
      sourceContext targetContext node node
      (wireMap input outer inner distinct)
      witness.indexMap targetExact.nodup witness.get
      (context_mem_iff input wellFormed outer inner distinct ordered region
        below sourceContext targetContext sourceExact targetExact)
      (fun wire currentPort occurs =>
        endpointOccurs_map input outer inner wire distinct
          ⟨node, currentPort⟩ occurs)
      (fun targetWire currentPort occurs =>
        endpointOccurs_preimage input outer inner distinct targetWire
          ⟨node, currentPort⟩ occurs)
      targetWellFormed.wire_endpoints_are_disjoint port
  have binderMap : ∀ sourceRegion binder,
      input.nodes node = .atom sourceRegion binder →
      binders (id binder) = (binders binder).map (fun relation =>
        ⟨relation.1,
          identityRelationRenaming rels relation.2⟩) := by
    intro sourceRegion binder shape
    simp [identityRelationRenaming]
  have mapped := Concrete.Elaboration.compileNode?_map sourceContext
    targetContext binders binders node node id id witness.indexMap
      (identityRelationRenaming rels)
      nodeShape ports binderMap
  have identity : (fun {arity} =>
      identityRelationRenaming rels :
        RelationRenaming rels rels) = (fun {arity} relation => relation) := rfl
  rw [identity] at mapped
  simpa only [Item.renameRelations_id] using mapped

noncomputable def localEquiv
    (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner)
    (region : Fin input.regionCount)
    (notInnerScope : region ≠ (input.wires inner).scope) :
    FiniteEquiv
      (Fin (Concrete.Elaboration.exactScopeWires input region).length)
      (Fin (Concrete.Elaboration.exactScopeWires
        (Target input outer inner) region).length) := by
  let forward := localMap input outer inner distinct
    region notInnerScope
  let inverse := fun targetIndex => Classical.choose
    (localMap_surjective input outer inner distinct
      region notInnerScope targetIndex)
  exact {
    toFun := forward
    invFun := inverse
    left_inv := by
      intro sourceIndex
      apply localMap_injective input outer inner distinct
        region notInnerScope
      exact Classical.choose_spec
        (localMap_surjective input outer inner distinct
          region notInnerScope (forward sourceIndex))
    right_inv := by
      intro targetIndex
      exact Classical.choose_spec
        (localMap_surjective input outer inner distinct
          region notInnerScope targetIndex)
  }

def extendedMap
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext
      (Target input outer inner))
    (outerMap : Fin sourceContext.length → Fin targetContext.length)
    (region : Fin input.regionCount)
    (localIso : FiniteEquiv
      (Fin (Concrete.Elaboration.exactScopeWires input region).length)
      (Fin (Concrete.Elaboration.exactScopeWires
        (Target input outer inner) region).length)) :
    Fin (sourceContext.extend region).length →
      Fin (targetContext.extend region).length :=
  fun index =>
    let sourcePosition := Fin.cast
      (Concrete.Elaboration.WireContext.length_extend sourceContext region)
      index
    let targetPosition := Fin.addCases
      (fun inherited => Fin.castAdd
        (Concrete.Elaboration.exactScopeWires
          (Target input outer inner) region).length
        (outerMap inherited))
      (fun localIndex => Fin.natAdd targetContext.length
        (localIso localIndex))
      sourcePosition
    Fin.cast
      (Concrete.Elaboration.WireContext.length_extend targetContext region).symm
      targetPosition

theorem extendedMap_get
    (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner)
    (region : Fin input.regionCount)
    (notInnerScope : region ≠ (input.wires inner).scope)
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext
      (Target input outer inner))
    (witness : ContextWitness input outer inner
      distinct sourceContext targetContext)
    (index : Fin (sourceContext.extend region).length) :
    (targetContext.extend region).get
        (extendedMap sourceContext targetContext witness.indexMap region
          (localEquiv input outer inner distinct region notInnerScope) index) =
      wireMap input outer inner distinct
        ((sourceContext.extend region).get index) := by
  let sourcePosition := Fin.cast
    (Concrete.Elaboration.WireContext.length_extend sourceContext region) index
  have recover : Fin.cast
      (Concrete.Elaboration.WireContext.length_extend sourceContext region).symm
      sourcePosition = index := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_)
    sourcePosition
  · simpa [extendedMap, sourcePosition,
      Concrete.Elaboration.WireContext.extend] using witness.get inherited
  · simpa [extendedMap, sourcePosition, localEquiv,
      Concrete.Elaboration.WireContext.extend] using
      localMap_get input outer inner distinct region
        notInnerScope localIndex

theorem extend_index_eq_extendedMap
    (input : Concrete.Diagram)
    (wellFormed : input.WellFormed)
    (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner)
    (ordered : input.Encloses (input.wires outer).scope
      (input.wires inner).scope)
    (region : Fin input.regionCount)
    (notInnerScope : region ≠ (input.wires inner).scope)
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext
      (Target input outer inner))
    (witness : ContextWitness input outer inner
      distinct sourceContext targetContext)
    (sourceExact : (sourceContext.extend region).Exact region)
    (targetExact : (targetContext.extend region).Exact region)
    (index : Fin (sourceContext.extend region).length) :
    (witness.extend wellFormed ordered region sourceExact targetExact).indexMap
        index =
      extendedMap sourceContext targetContext witness.indexMap region
        (localEquiv input outer inner distinct region notInnerScope) index := by
  apply Fin.ext
  exact (List.getElem_inj targetExact.nodup).mp (by
    simpa only [List.get_eq_getElem] using
      (witness.extend wellFormed ordered region sourceExact targetExact).get
        index |>.trans
      (extendedMap_get input outer inner distinct region notInnerScope
        sourceContext targetContext witness index).symm)

theorem itemSeqIso_after_rename
    (source : ItemSeq sourceWires rels)
    (target : ItemSeq targetWires rels)
    (wireMap : Fin sourceWires → Fin targetWires)
    (positions : FiniteEquiv (Fin source.length) (Fin target.length))
    (items : ∀ sourceIndex,
      ItemIso (FiniteEquiv.refl (Fin targetWires)) rels
        ((source.get sourceIndex).renameWires wireMap)
        (target.get (positions sourceIndex))) :
    ItemSeqIso (FiniteEquiv.refl (Fin targetWires)) rels
      (source.renameWires wireMap) target := by
  let sourcePositions := source.renameWiresPositionEquiv wireMap
  let renamedPositions := sourcePositions.symm.trans positions
  apply ItemSeqIso.permute renamedPositions
  intro renamedIndex
  let sourceIndex := sourcePositions.symm renamedIndex
  have sourceIndexEq : sourcePositions sourceIndex = renamedIndex :=
    sourcePositions.right_inv renamedIndex
  rw [← sourceIndexEq]
  change ItemIso (FiniteEquiv.refl (Fin targetWires)) rels
    ((source.renameWires wireMap).get (sourcePositions sourceIndex))
    (target.get (positions sourceIndex))
  rw [ItemSeq.get_renameWires]
  exact items sourceIndex

theorem compiledItemSeqIso_after_rename
    (input : Concrete.Diagram)
    (outer inner : Fin input.wireCount)
    (sourceRecurse : ∀ {rels : RelCtx},
      (region : Fin input.regionCount) →
      (context : Concrete.Elaboration.WireContext input) →
      Concrete.Elaboration.BinderContext input rels →
      Option (Region context.length rels))
    (targetRecurse : ∀ {rels : RelCtx},
      (region : Fin input.regionCount) →
      (context : Concrete.Elaboration.WireContext
        (Target input outer inner)) →
      Concrete.Elaboration.BinderContext
        (Target input outer inner) rels →
      Option (Region context.length rels))
    (sourceContext : Concrete.Elaboration.WireContext input)
    (targetContext : Concrete.Elaboration.WireContext
      (Target input outer inner))
    (sourceBinders : Concrete.Elaboration.BinderContext input rels)
    (targetBinders : Concrete.Elaboration.BinderContext
      (Target input outer inner) rels)
    (occurrences : List (Concrete.Elaboration.LocalOccurrence
      input.regionCount input.nodeCount))
    {sourceItems : ItemSeq sourceContext.length rels}
    {targetItems : ItemSeq targetContext.length rels}
    (sourceCompiled : Concrete.Elaboration.compileOccurrencesWith?
      input sourceRecurse sourceContext sourceBinders occurrences =
        some sourceItems)
    (targetCompiled : Concrete.Elaboration.compileOccurrencesWith?
      (Target input outer inner) targetRecurse
        targetContext targetBinders occurrences =
        some targetItems)
    (wireMap : Fin sourceContext.length → Fin targetContext.length)
    (items : ∀ index : Fin occurrences.length,
      ItemIso (FiniteEquiv.refl (Fin targetContext.length)) rels
        ((sourceItems.get (Fin.cast
          (Concrete.Elaboration.compileOccurrencesWith?_length sourceRecurse
            sourceContext sourceBinders sourceCompiled).symm index)).renameWires
              wireMap)
        (targetItems.get (Fin.cast
          (Concrete.Elaboration.compileOccurrencesWith?_length targetRecurse
            targetContext targetBinders targetCompiled).symm index))) :
    ItemSeqIso (FiniteEquiv.refl (Fin targetContext.length)) rels
      (sourceItems.renameWires wireMap) targetItems := by
  let sourceLength := Concrete.Elaboration.compileOccurrencesWith?_length
    sourceRecurse sourceContext sourceBinders sourceCompiled
  let targetLength := Concrete.Elaboration.compileOccurrencesWith?_length
    targetRecurse targetContext targetBinders targetCompiled
  let positions := (FiniteEquiv.finCast sourceLength).trans
    (FiniteEquiv.finCast targetLength.symm)
  apply itemSeqIso_after_rename sourceItems targetItems wireMap positions
  intro sourceIndex
  let occurrenceIndex := Fin.cast sourceLength sourceIndex
  have sourcePosition : Fin.cast sourceLength.symm occurrenceIndex =
      sourceIndex := by
    apply Fin.ext
    rfl
  have targetPosition : Fin.cast targetLength.symm occurrenceIndex =
      positions sourceIndex := by
    apply Fin.ext
    rfl
  simpa only [sourcePosition, targetPosition] using items occurrenceIndex

noncomputable def contextEquiv
    {input : Concrete.Diagram}
    {outer inner : Fin input.wireCount}
    {distinct : outer ≠ inner}
    {sourceContext : Concrete.Elaboration.WireContext input}
    {targetContext : Concrete.Elaboration.WireContext
      (Target input outer inner)}
    (witness : ContextWitness input outer inner
      distinct sourceContext targetContext)
    (sourceNodup : sourceContext.Nodup)
    (innerAbsent : inner ∉ sourceContext) :
    FiniteEquiv (Fin sourceContext.length) (Fin targetContext.length) where
  toFun := witness.indexMap
  invFun := fun targetIndex => Classical.choose (witness.surjective targetIndex)
  left_inv := by
    intro sourceIndex
    let chosen := Classical.choose
      (witness.surjective (witness.indexMap sourceIndex))
    have mapped : witness.indexMap chosen = witness.indexMap sourceIndex :=
      Classical.choose_spec
        (witness.surjective (witness.indexMap sourceIndex))
    have getEquality := congrArg targetContext.get mapped
    rw [witness.get, witness.get] at getEquality
    have classified := (wireMap_eq_iff input
      outer inner (sourceContext.get chosen) (sourceContext.get sourceIndex)
      distinct).1 getEquality
    have sourceGet : sourceContext.get chosen = sourceContext.get sourceIndex := by
      rcases classified with same | outerInner | innerOuter
      · exact same
      · exact False.elim
          (innerAbsent (outerInner.2 ▸ List.get_mem sourceContext sourceIndex))
      · exact False.elim
          (innerAbsent (innerOuter.1 ▸ List.get_mem sourceContext chosen))
    apply Fin.ext
    exact (List.getElem_inj sourceNodup).mp (by
      simpa only [List.get_eq_getElem] using sourceGet)
  right_inv := by
    intro targetIndex
    exact Classical.choose_spec (witness.surjective targetIndex)

end VisualProof.Refinement.Implementation.WireJoin
