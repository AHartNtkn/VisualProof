import VisualProof.Diagram.Concrete.Elaboration.Simulation
import VisualProof.Rule.Soundness

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

namespace WireJoinSoundness

variable {signature : List Nat}

abbrev Target (input : ConcreteDiagram)
    (outer inner : Fin input.wireCount) :=
  joinWireRaw input outer inner

def wireMap (input : ConcreteDiagram)
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
    (input : ConcreteDiagram)
    (outer inner : Fin input.wireCount) (distinct : outer ≠ inner) :
    wireMap input outer inner distinct inner =
      (joinWireDomain input inner).index outer
        (by simpa [joinWireDomain] using distinct) := by
  simp [wireMap]

@[simp] theorem wireMap_of_ne
    (input : ConcreteDiagram)
    (outer inner wire : Fin input.wireCount) (distinct : outer ≠ inner)
    (hne : wire ≠ inner) :
    wireMap input outer inner distinct wire =
      (joinWireDomain input inner).index wire
        (by simpa [joinWireDomain] using hne) := by
  simp [wireMap, hne]

theorem origin_wireMap
    (input : ConcreteDiagram)
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
    (input : ConcreteDiagram)
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
    (input : ConcreteDiagram)
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
    (input : ConcreteDiagram) (outer inner : Fin input.wireCount) :
    (Target input outer inner).regionCount = input.regionCount :=
  rfl

@[simp] theorem target_nodeCount
    (input : ConcreteDiagram) (outer inner : Fin input.wireCount) :
    (Target input outer inner).nodeCount = input.nodeCount :=
  rfl

@[simp] theorem target_root
    (input : ConcreteDiagram) (outer inner : Fin input.wireCount) :
    (Target input outer inner).root = input.root :=
  rfl

@[simp] theorem target_regions
    (input : ConcreteDiagram) (outer inner : Fin input.wireCount)
    (region : Fin input.regionCount) :
    (Target input outer inner).regions region = input.regions region :=
  rfl

@[simp] theorem target_nodes
    (input : ConcreteDiagram) (outer inner : Fin input.wireCount)
    (node : Fin input.nodeCount) :
    (Target input outer inner).nodes node = input.nodes node :=
  rfl

theorem target_wire_scope
    (input : ConcreteDiagram)
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
    (input : ConcreteDiagram)
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
    (input : ConcreteDiagram)
    (outer inner : Fin input.wireCount)
    (steps : Nat) (region : Fin input.regionCount) :
    (Target input outer inner).climb steps region =
      input.climb steps region := by
  induction steps generalizing region with
  | zero => rfl
  | succ steps induction =>
      cases parent : (input.regions region).parent? with
      | none =>
          simp [ConcreteDiagram.climb, target_regions, parent]
      | some directParent =>
          simpa [ConcreteDiagram.climb, target_regions, parent] using
            induction directParent

theorem target_encloses_iff
    (input : ConcreteDiagram)
    (outer inner : Fin input.wireCount)
    (ancestor descendant : Fin input.regionCount) :
    (Target input outer inner).Encloses ancestor descendant ↔
      input.Encloses ancestor descendant := by
  unfold ConcreteDiagram.Encloses
  constructor <;> rintro ⟨steps, encloses⟩ <;>
    exact ⟨steps, by simpa [target_climb] using encloses⟩

theorem endpointOccurs_map
    (input : ConcreteDiagram)
    (outer inner wire : Fin input.wireCount) (distinct : outer ≠ inner)
    (endpoint : CEndpoint input.nodeCount)
    (occurs : input.EndpointOccurs wire endpoint) :
    (Target input outer inner).EndpointOccurs
      (wireMap input outer inner distinct wire) endpoint := by
  unfold ConcreteDiagram.EndpointOccurs at occurs ⊢
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
    (input : ConcreteDiagram)
    (wellFormed : input.WellFormed signature)
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
    exact ConcreteElaboration.checked_encloses_trans wellFormed ordered visible
  · rw [if_neg hwire, target_encloses_iff]
    exact visible

theorem visible_preimage
    (input : ConcreteDiagram)
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
    (input : ConcreteDiagram)
    (outer inner : Fin input.wireCount) (distinct : outer ≠ inner)
    (sourceContext : ConcreteElaboration.WireContext input)
    (targetContext :
      ConcreteElaboration.WireContext (Target input outer inner)) :
    ConcreteElaboration.ContextIndexRelation
      sourceContext.length targetContext.length where
  Rel sourceIndex targetIndex :=
    wireMap input outer inner distinct (sourceContext.get sourceIndex) =
      targetContext.get targetIndex

structure ContextWitness
    (input : ConcreteDiagram)
    (outer inner : Fin input.wireCount) (distinct : outer ≠ inner)
    (sourceContext : ConcreteElaboration.WireContext input)
    (targetContext :
      ConcreteElaboration.WireContext (Target input outer inner)) where
  indexMap : Fin sourceContext.length → Fin targetContext.length
  get : ∀ sourceIndex,
    targetContext.get (indexMap sourceIndex) =
      wireMap input outer inner distinct (sourceContext.get sourceIndex)
  surjective : Function.Surjective indexMap

noncomputable def ContextWitness.ofExact
    (input : ConcreteDiagram)
    (wellFormed : input.WellFormed signature)
    (outer inner : Fin input.wireCount) (distinct : outer ≠ inner)
    (ordered :
      input.Encloses (input.wires outer).scope (input.wires inner).scope)
    (region : Fin input.regionCount)
    (sourceContext : ConcreteElaboration.WireContext input)
    (targetContext :
      ConcreteElaboration.WireContext (Target input outer inner))
    (sourceExact : sourceContext.Exact region)
    (targetExact : targetContext.Exact region) :
    ContextWitness input outer inner distinct sourceContext targetContext := by
  let indexMap : Fin sourceContext.length → Fin targetContext.length :=
    fun sourceIndex => Classical.choose (by
      have sourceMember := List.get_mem sourceContext sourceIndex
      have sourceVisible := (sourceExact.mem_iff _).1 sourceMember
      have targetVisible := visible_map input wellFormed outer inner
        (sourceContext.get sourceIndex) distinct ordered region sourceVisible
      exact ConcreteElaboration.WireContext.lookup?_complete
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
    exact ConcreteElaboration.WireContext.lookup?_sound
      (Classical.choose_spec
        (ConcreteElaboration.WireContext.lookup?_complete targetMember))
  refine ⟨indexMap, get, ?_⟩
  intro targetIndex
  have targetMember := List.get_mem targetContext targetIndex
  have targetVisible := (targetExact.mem_iff _).1 targetMember
  obtain ⟨sourceWire, sourceVisible, mapped⟩ :=
    visible_preimage input outer inner distinct region
      (targetContext.get targetIndex) targetVisible
  have sourceMember := (sourceExact.mem_iff _).2 sourceVisible
  obtain ⟨sourceIndex, lookup⟩ :=
    ConcreteElaboration.WireContext.lookup?_complete sourceMember
  refine ⟨sourceIndex, ?_⟩
  apply Fin.ext
  apply (List.getElem_inj targetExact.nodup).mp
  have sourceGet :=
    ConcreteElaboration.WireContext.lookup?_sound lookup
  have mappedGet :
      wireMap input outer inner distinct (sourceContext.get sourceIndex) =
        targetContext.get targetIndex :=
    (congrArg (wireMap input outer inner distinct) sourceGet).trans mapped
  simpa only [List.get_eq_getElem] using
    (get sourceIndex).trans mappedGet

noncomputable def localMap
    (input : ConcreteDiagram)
    (outer inner : Fin input.wireCount) (distinct : outer ≠ inner)
    (region : Fin input.regionCount)
    (hne : region ≠ (input.wires inner).scope) :
    Fin (ConcreteElaboration.exactScopeWires input region).length →
      Fin (ConcreteElaboration.exactScopeWires
        (Target input outer inner) region).length :=
  fun sourceIndex =>
    let sourceWire :=
      (ConcreteElaboration.exactScopeWires input region).get sourceIndex
    let targetWire := wireMap input outer inner distinct sourceWire
    have sourceScope : (input.wires sourceWire).scope = region :=
      (ConcreteElaboration.mem_exactScopeWires input region sourceWire).1
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
      (ConcreteElaboration.WireContext.lookup?_complete
        ((ConcreteElaboration.mem_exactScopeWires
          (Target input outer inner) region targetWire).2 targetScope))

theorem localMap_get
    (input : ConcreteDiagram)
    (outer inner : Fin input.wireCount) (distinct : outer ≠ inner)
    (region : Fin input.regionCount)
    (hne : region ≠ (input.wires inner).scope)
    (sourceIndex :
      Fin (ConcreteElaboration.exactScopeWires input region).length) :
    (ConcreteElaboration.exactScopeWires
      (Target input outer inner) region).get
        (localMap input outer inner distinct region hne sourceIndex) =
      wireMap input outer inner distinct
        ((ConcreteElaboration.exactScopeWires input region).get
          sourceIndex) := by
  exact ConcreteElaboration.WireContext.lookup?_sound
    (Classical.choose_spec
      (ConcreteElaboration.WireContext.lookup?_complete
        ((ConcreteElaboration.mem_exactScopeWires
          (Target input outer inner) region
          (wireMap input outer inner distinct
            ((ConcreteElaboration.exactScopeWires input region).get
              sourceIndex))).2 (by
            have sourceScope :=
              (ConcreteElaboration.mem_exactScopeWires input region
                ((ConcreteElaboration.exactScopeWires input region).get
                  sourceIndex)).1 (List.get_mem _ sourceIndex)
            have sourceNe :
                (ConcreteElaboration.exactScopeWires input region).get
                    sourceIndex ≠ inner := by
              intro equality
              rw [equality] at sourceScope
              exact hne sourceScope.symm
            rw [target_wire_scope, if_neg sourceNe]
            exact sourceScope))))

theorem localMap_injective
    (input : ConcreteDiagram)
    (outer inner : Fin input.wireCount) (distinct : outer ≠ inner)
    (region : Fin input.regionCount)
    (hne : region ≠ (input.wires inner).scope) :
    Function.Injective (localMap input outer inner distinct region hne) := by
  intro left right equality
  have targetGetEquality := congrArg
    (List.get (ConcreteElaboration.exactScopeWires
      (Target input outer inner) region)) equality
  rw [localMap_get, localMap_get] at targetGetEquality
  have mapped :=
    (wireMap_eq_iff input outer inner
      ((ConcreteElaboration.exactScopeWires input region).get left)
      ((ConcreteElaboration.exactScopeWires input region).get right)
      distinct).1 targetGetEquality
  have sourceGetEquality :
      (ConcreteElaboration.exactScopeWires input region).get left =
        (ConcreteElaboration.exactScopeWires input region).get right := by
    rcases mapped with same | outerInner | innerOuter
    · exact same
    · rcases outerInner with ⟨_, rightInner⟩
      have rightScope :=
        (ConcreteElaboration.mem_exactScopeWires input region
          ((ConcreteElaboration.exactScopeWires input region).get right)).1
          (List.get_mem _ right)
      rw [rightInner] at rightScope
      exact False.elim (hne rightScope.symm)
    · rcases innerOuter with ⟨leftInner, _⟩
      have leftScope :=
        (ConcreteElaboration.mem_exactScopeWires input region
          ((ConcreteElaboration.exactScopeWires input region).get left)).1
          (List.get_mem _ left)
      rw [leftInner] at leftScope
      exact False.elim (hne leftScope.symm)
  apply Fin.ext
  exact (List.getElem_inj
    (ConcreteElaboration.exactScopeWires_nodup input region)).mp
      (by simpa only [List.get_eq_getElem] using sourceGetEquality)

theorem localMap_surjective
    (input : ConcreteDiagram)
    (outer inner : Fin input.wireCount) (distinct : outer ≠ inner)
    (region : Fin input.regionCount)
    (hne : region ≠ (input.wires inner).scope) :
    Function.Surjective
      (localMap input outer inner distinct region hne) := by
  intro targetIndex
  let targetWire :=
    (ConcreteElaboration.exactScopeWires
      (Target input outer inner) region).get targetIndex
  have targetScope :
      ((Target input outer inner).wires targetWire).scope = region :=
    (ConcreteElaboration.mem_exactScopeWires
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
    (ConcreteElaboration.mem_exactScopeWires input region sourceWire).2
      sourceScope
  obtain ⟨sourceIndex, lookup⟩ :=
    ConcreteElaboration.WireContext.lookup?_complete sourceMember
  refine ⟨sourceIndex, ?_⟩
  have sourceGet :=
    ConcreteElaboration.WireContext.lookup?_sound lookup
  have targetGet :
      (ConcreteElaboration.exactScopeWires
        (Target input outer inner) region).get
          (localMap input outer inner distinct region hne sourceIndex) =
        targetWire := by
    calc
      _ = wireMap input outer inner distinct
          ((ConcreteElaboration.exactScopeWires input region).get
            sourceIndex) :=
        localMap_get input outer inner distinct region hne sourceIndex
      _ = wireMap input outer inner distinct sourceWire :=
        congrArg (wireMap input outer inner distinct) sourceGet
      _ = targetWire := mapped
  apply Fin.ext
  exact (List.getElem_inj
    (ConcreteElaboration.exactScopeWires_nodup
      (Target input outer inner) region)).mp (by
        simpa only [List.get_eq_getElem] using targetGet)

noncomputable def ContextWitness.extend
    (_witness : ContextWitness input outer inner distinct
      sourceContext targetContext)
    (wellFormed : input.WellFormed signature)
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
    (wellFormed : input.WellFormed signature)
    (ordered :
      input.Encloses (input.wires outer).scope (input.wires inner).scope)
    (region : Fin input.regionCount)
    (sourceExact : (sourceContext.extend region).Exact region)
    (targetExact : (targetContext.extend region).Exact region)
    (sourceIndex : Fin sourceContext.length) :
    (witness.extend wellFormed ordered region sourceExact targetExact).indexMap
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend sourceContext
            region).symm
          (Fin.castAdd
            (ConcreteElaboration.exactScopeWires input region).length
            sourceIndex)) =
      Fin.cast
        (ConcreteElaboration.WireContext.length_extend targetContext
          region).symm
        (Fin.castAdd
          (ConcreteElaboration.exactScopeWires
            (Target input outer inner) region).length
          (witness.indexMap sourceIndex)) := by
  let sourceExtendedIndex : Fin (sourceContext.extend region).length :=
    Fin.cast
      (ConcreteElaboration.WireContext.length_extend sourceContext region).symm
      (Fin.castAdd
        (ConcreteElaboration.exactScopeWires input region).length sourceIndex)
  let targetExtendedIndex : Fin (targetContext.extend region).length :=
    Fin.cast
      (ConcreteElaboration.WireContext.length_extend targetContext region).symm
      (Fin.castAdd
        (ConcreteElaboration.exactScopeWires
          (Target input outer inner) region).length
        (witness.indexMap sourceIndex))
  change
    (witness.extend wellFormed ordered region sourceExact targetExact).indexMap
      sourceExtendedIndex = targetExtendedIndex
  apply Fin.ext
  have sourceGet :
      (sourceContext.extend region).get sourceExtendedIndex =
        sourceContext.get sourceIndex := by
    simp [sourceExtendedIndex, ConcreteElaboration.WireContext.extend]
  have targetGet :
      (targetContext.extend region).get targetExtendedIndex =
        targetContext.get (witness.indexMap sourceIndex) := by
    simp [targetExtendedIndex, ConcreteElaboration.WireContext.extend]
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
    (wellFormed : input.WellFormed signature)
    (ordered :
      input.Encloses (input.wires outer).scope (input.wires inner).scope)
    (region : Fin input.regionCount)
    (hne : region ≠ (input.wires inner).scope)
    (sourceExact : (sourceContext.extend region).Exact region)
    (targetExact : (targetContext.extend region).Exact region)
    (sourceLocal :
      Fin (ConcreteElaboration.exactScopeWires input region).length) :
    (witness.extend wellFormed ordered region sourceExact targetExact).indexMap
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend sourceContext
            region).symm
          (Fin.natAdd sourceContext.length sourceLocal)) =
      Fin.cast
        (ConcreteElaboration.WireContext.length_extend targetContext
          region).symm
        (Fin.natAdd targetContext.length
          (localMap input outer inner distinct region hne sourceLocal)) := by
  let sourceExtendedIndex : Fin (sourceContext.extend region).length :=
    Fin.cast
      (ConcreteElaboration.WireContext.length_extend sourceContext region).symm
      (Fin.natAdd sourceContext.length sourceLocal)
  let targetExtendedIndex : Fin (targetContext.extend region).length :=
    Fin.cast
      (ConcreteElaboration.WireContext.length_extend targetContext region).symm
      (Fin.natAdd targetContext.length
        (localMap input outer inner distinct region hne sourceLocal))
  change
    (witness.extend wellFormed ordered region sourceExact targetExact).indexMap
      sourceExtendedIndex = targetExtendedIndex
  apply Fin.ext
  have sourceGet :
      (sourceContext.extend region).get sourceExtendedIndex =
        (ConcreteElaboration.exactScopeWires input region).get sourceLocal := by
    simp [sourceExtendedIndex, ConcreteElaboration.WireContext.extend]
  have targetGet :
      (targetContext.extend region).get targetExtendedIndex =
        (ConcreteElaboration.exactScopeWires
          (Target input outer inner) region).get
            (localMap input outer inner distinct region hne sourceLocal) := by
    simp [targetExtendedIndex, ConcreteElaboration.WireContext.extend]
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
    (input : ConcreteDiagram)
    (outer inner : Fin input.wireCount) (distinct : outer ≠ inner)
    (region : Fin input.regionCount)
    (hne : region ≠ (input.wires inner).scope)
    (targetIndex : Fin (ConcreteElaboration.exactScopeWires
      (Target input outer inner) region).length) :
    Fin (ConcreteElaboration.exactScopeWires input region).length :=
  Classical.choose
    (localMap_surjective input outer inner distinct region hne targetIndex)

theorem localInverse_spec
    (input : ConcreteDiagram)
    (outer inner : Fin input.wireCount) (distinct : outer ≠ inner)
    (region : Fin input.regionCount)
    (hne : region ≠ (input.wires inner).scope)
    (targetIndex : Fin (ConcreteElaboration.exactScopeWires
      (Target input outer inner) region).length) :
    localMap input outer inner distinct region hne
        (localInverse input outer inner distinct region hne targetIndex) =
      targetIndex :=
  Classical.choose_spec
    (localMap_surjective input outer inner distinct region hne targetIndex)

theorem localInverse_localMap
    (input : ConcreteDiagram)
    (outer inner : Fin input.wireCount) (distinct : outer ≠ inner)
    (region : Fin input.regionCount)
    (hne : region ≠ (input.wires inner).scope)
    (sourceIndex :
      Fin (ConcreteElaboration.exactScopeWires input region).length) :
    localInverse input outer inner distinct region hne
        (localMap input outer inner distinct region hne sourceIndex) =
      sourceIndex := by
  apply localMap_injective input outer inner distinct region hne
  exact localInverse_spec input outer inner distinct region hne _

noncomputable def targetLocalOfSource
    (input : ConcreteDiagram)
    (outer inner : Fin input.wireCount) (distinct : outer ≠ inner)
    (region : Fin input.regionCount)
    (hne : region ≠ (input.wires inner).scope)
    (sourceLocal :
      Fin (ConcreteElaboration.exactScopeWires input region).length → D) :
    Fin (ConcreteElaboration.exactScopeWires
      (Target input outer inner) region).length → D :=
  sourceLocal ∘ localInverse input outer inner distinct region hne

@[simp] theorem targetLocalOfSource_localMap
    (input : ConcreteDiagram)
    (outer inner : Fin input.wireCount) (distinct : outer ≠ inner)
    (region : Fin input.regionCount)
    (hne : region ≠ (input.wires inner).scope)
    (sourceLocal :
      Fin (ConcreteElaboration.exactScopeWires input region).length → D)
    (sourceIndex :
      Fin (ConcreteElaboration.exactScopeWires input region).length) :
    targetLocalOfSource input outer inner distinct region hne sourceLocal
        (localMap input outer inner distinct region hne sourceIndex) =
      sourceLocal sourceIndex := by
  change sourceLocal
      (localInverse input outer inner distinct region hne
        (localMap input outer inner distinct region hne sourceIndex)) =
    sourceLocal sourceIndex
  rw [localInverse_localMap]

noncomputable def sourceLocalOfTarget
    (witness : ContextWitness input outer inner distinct
      sourceContext targetContext)
    (wellFormed : input.WellFormed signature)
    (ordered :
      input.Encloses (input.wires outer).scope (input.wires inner).scope)
    (region : Fin input.regionCount)
    (sourceExact : (sourceContext.extend region).Exact region)
    (targetExact : (targetContext.extend region).Exact region)
    (targetOuter : Fin targetContext.length → D)
    (targetLocal : Fin (ConcreteElaboration.exactScopeWires
      (Target input outer inner) region).length → D) :
    Fin (ConcreteElaboration.exactScopeWires input region).length → D :=
  fun sourceLocal =>
    ConcreteElaboration.extendedEnvironment targetContext region
      targetOuter targetLocal
      ((witness.extend wellFormed ordered region sourceExact
        targetExact).indexMap
        (Fin.cast
          (ConcreteElaboration.WireContext.length_extend sourceContext
            region).symm
          (Fin.natAdd sourceContext.length sourceLocal)))

theorem ContextWitness.extendedEnvironment_forward
    (witness : ContextWitness input outer inner distinct
      sourceContext targetContext)
    (wellFormed : input.WellFormed signature)
    (ordered :
      input.Encloses (input.wires outer).scope (input.wires inner).scope)
    (region : Fin input.regionCount)
    (hne : region ≠ (input.wires inner).scope)
    (sourceExact : (sourceContext.extend region).Exact region)
    (targetExact : (targetContext.extend region).Exact region)
    (sourceOuter : Fin sourceContext.length → D)
    (targetOuter : Fin targetContext.length → D)
    (outerAgrees : sourceOuter = targetOuter ∘ witness.indexMap)
    (sourceLocal :
      Fin (ConcreteElaboration.exactScopeWires input region).length → D) :
    ConcreteElaboration.extendedEnvironment sourceContext region
        sourceOuter sourceLocal =
      ConcreteElaboration.extendedEnvironment targetContext region
          targetOuter
          (targetLocalOfSource input outer inner distinct region hne
            sourceLocal) ∘
        (witness.extend wellFormed ordered region sourceExact
          targetExact).indexMap := by
  funext sourceIndex
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend sourceContext region)
    sourceIndex
  have recover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend sourceContext region).symm
      split = sourceIndex := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_) split
  · have indexEq := witness.extend_index_inherited wellFormed ordered region
      sourceExact targetExact inherited
    simp only [ConcreteElaboration.extendedEnvironment, Function.comp_apply,
      extendWireEnv]
    rw [indexEq]
    simpa [Function.comp_def] using congrFun outerAgrees inherited
  · have indexEq := witness.extend_index_local_of_ne wellFormed ordered region
      hne sourceExact targetExact localIndex
    simp only [ConcreteElaboration.extendedEnvironment, Function.comp_apply,
      extendWireEnv]
    rw [indexEq]
    simp [targetLocalOfSource_localMap]

theorem ContextWitness.extendedEnvironment_backward
    (witness : ContextWitness input outer inner distinct
      sourceContext targetContext)
    (wellFormed : input.WellFormed signature)
    (ordered :
      input.Encloses (input.wires outer).scope (input.wires inner).scope)
    (region : Fin input.regionCount)
    (sourceExact : (sourceContext.extend region).Exact region)
    (targetExact : (targetContext.extend region).Exact region)
    (sourceOuter : Fin sourceContext.length → D)
    (targetOuter : Fin targetContext.length → D)
    (outerAgrees : sourceOuter = targetOuter ∘ witness.indexMap)
    (targetLocal : Fin (ConcreteElaboration.exactScopeWires
      (Target input outer inner) region).length → D) :
    ConcreteElaboration.extendedEnvironment sourceContext region sourceOuter
        (sourceLocalOfTarget witness wellFormed ordered region sourceExact
          targetExact targetOuter targetLocal) =
      ConcreteElaboration.extendedEnvironment targetContext region
          targetOuter targetLocal ∘
        (witness.extend wellFormed ordered region sourceExact
          targetExact).indexMap := by
  funext sourceIndex
  let split := Fin.cast
    (ConcreteElaboration.WireContext.length_extend sourceContext region)
    sourceIndex
  have recover : Fin.cast
      (ConcreteElaboration.WireContext.length_extend sourceContext region).symm
      split = sourceIndex := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun inherited => ?_) (fun localIndex => ?_) split
  · have indexEq := witness.extend_index_inherited wellFormed ordered region
      sourceExact targetExact inherited
    simp only [ConcreteElaboration.extendedEnvironment, Function.comp_apply,
      extendWireEnv]
    rw [indexEq]
    simpa [Function.comp_def] using congrFun outerAgrees inherited
  · simp [sourceLocalOfTarget, ConcreteElaboration.extendedEnvironment,
      Function.comp_def, extendWireEnv]

def direction : Orientation → ConcreteElaboration.SimulationDirection
  | .forward => .forward
  | .backward => .backward

def depthAllowed
    (simulationDirection : ConcreteElaboration.SimulationDirection)
    (depth : Nat) : Prop :=
  match simulationDirection with
  | .forward => depth % 2 = 1
  | .backward => depth % 2 = 0

def Allowed (input : ConcreteDiagram)
    (site : Fin input.regionCount)
    (simulationDirection : ConcreteElaboration.SimulationDirection)
    (region : Fin input.regionCount) : Prop :=
  ∀ {path depth} (route : Diagram.Splice.RegionRoute input region site path),
    route.HasCutDepth depth → depthAllowed simulationDirection depth

theorem allowed_cut
    (input : ConcreteDiagram) (site : Fin input.regionCount)
    (simulationDirection : ConcreteElaboration.SimulationDirection)
    (child parent : Fin input.regionCount)
    (childKind : input.regions child = .cut parent)
    (allowed : Allowed input site simulationDirection parent) :
    Allowed input site simulationDirection.flip child := by
  intro path depth route routeDepth
  have hparent : (input.regions child).parent? = some parent := by
    rw [childKind]
    rfl
  obtain ⟨position, hposition⟩ := indexOf?_complete
    ((ConcreteElaboration.mem_localOccurrences_child input parent child).2
      hparent)
  let parentRoute :=
    Diagram.Splice.RegionRoute.step hparent position hposition route
  have parentDepth : parentRoute.HasCutDepth (depth + 1) := by
    exact Diagram.Splice.RegionRoute.HasCutDepth.cut
      (hparent := hparent) (position := position) (hposition := hposition)
      childKind routeDepth
  have parity := allowed parentRoute parentDepth
  cases simulationDirection <;> simp [depthAllowed] at parity ⊢ <;> omega

theorem allowed_bubble
    (input : ConcreteDiagram) (site : Fin input.regionCount)
    (simulationDirection : ConcreteElaboration.SimulationDirection)
    (child parent : Fin input.regionCount) (arity : Nat)
    (childKind : input.regions child = .bubble parent arity)
    (allowed : Allowed input site simulationDirection parent) :
    Allowed input site simulationDirection child := by
  intro path depth route routeDepth
  have hparent : (input.regions child).parent? = some parent := by
    rw [childKind]
    rfl
  obtain ⟨position, hposition⟩ := indexOf?_complete
    ((ConcreteElaboration.mem_localOccurrences_child input parent child).2
      hparent)
  let parentRoute :=
    Diagram.Splice.RegionRoute.step hparent position hposition route
  have parentDepth : parentRoute.HasCutDepth depth := by
    exact Diagram.Splice.RegionRoute.HasCutDepth.bubble
      (hparent := hparent) (position := position) (hposition := hposition)
      childKind routeDepth
  exact allowed parentRoute parentDepth

theorem allowed_root
    (source : CheckedOpenDiagram signature)
    (site : Fin source.val.diagram.regionCount)
    (orientation : Orientation)
    (polarity : spawnPolarity orientation
      (concreteCutDepth source.val.diagram site)) :
    Allowed source.val.diagram site (direction orientation)
      source.val.diagram.root := by
  intro path depth route routeDepth
  let view := Classical.choice
    (Diagram.Splice.openSiteView_complete source site)
  have pathEq : path = view.path :=
    Diagram.Splice.Input.RegionRoute.path_unique
      source.property.diagram_well_formed route view.route
  subst path
  have routeEq : route = view.route := Subsingleton.elim _ _
  subst route
  have depthEq : depth = view.focus.context.cutDepth :=
    regionRoute_cutDepth_unique routeDepth view.cutDepth
  subst depth
  rw [← openSiteView_concreteCutDepth_eq view]
  cases orientation <;> exact polarity

theorem allowed_forward_ne_site
    (input : ConcreteDiagram) (site region : Fin input.regionCount)
    (allowed : Allowed input site .forward region) :
    region ≠ site := by
  intro equality
  subst region
  have impossible := allowed (Diagram.Splice.RegionRoute.here site)
    (Diagram.Splice.RegionRoute.HasCutDepth.here site)
  simp [depthAllowed] at impossible

@[simp] theorem target_localOccurrences
    (input : ConcreteDiagram) (outer inner : Fin input.wireCount)
    (region : Fin input.regionCount) :
    ConcreteElaboration.localOccurrences (Target input outer inner) region =
      ConcreteElaboration.localOccurrences input region := by
  unfold ConcreteElaboration.localOccurrences
  simp only [target_nodeCount, target_regionCount, target_nodes,
    target_regions]
  rfl

theorem resolvedPorts_related
    (input : ConcreteDiagram)
    (outer inner : Fin input.wireCount) (distinct : outer ≠ inner)
    (targetWellFormed : (Target input outer inner).WellFormed signature)
    (sourceContext : ConcreteElaboration.WireContext input)
    (targetContext :
      ConcreteElaboration.WireContext (Target input outer inner))
    (witness : ContextWitness input outer inner distinct
      sourceContext targetContext)
    (targetNodup : targetContext.Nodup)
    (node : Fin input.nodeCount) (port : CPort)
    (sourceIndex : Fin sourceContext.length)
    (targetIndex : Fin targetContext.length)
    (sourceResolved :
      ConcreteElaboration.resolvePort? input sourceContext node port =
        some sourceIndex)
    (targetResolved :
      ConcreteElaboration.resolvePort? (Target input outer inner)
        targetContext node port = some targetIndex) :
    (ConcreteElaboration.ContextIndexRelation.forwardMap witness.indexMap).Rel
      sourceIndex targetIndex := by
  obtain ⟨sourceWire, sourceOccurs, sourceGet⟩ :=
    ConcreteElaboration.resolvePort?_sound sourceResolved
  obtain ⟨targetWire, targetOccurs, targetGet⟩ :=
    ConcreteElaboration.resolvePort?_sound targetResolved
  have mappedOccurs :=
    endpointOccurs_map input outer inner sourceWire distinct
      ⟨node, port⟩ sourceOccurs
  have wireEq :
      wireMap input outer inner distinct sourceWire = targetWire :=
    ConcreteElaboration.endpoint_wire_unique
      targetWellFormed.wire_endpoints_are_disjoint mappedOccurs targetOccurs
  have contextGet :
      targetContext.get (witness.indexMap sourceIndex) =
        targetContext.get targetIndex := by
    calc
      _ = wireMap input outer inner distinct
          (sourceContext.get sourceIndex) := witness.get sourceIndex
      _ = wireMap input outer inner distinct sourceWire :=
        congrArg (wireMap input outer inner distinct) sourceGet
      _ = targetWire := wireEq
      _ = targetContext.get targetIndex := targetGet.symm
  apply Fin.ext
  exact (List.getElem_inj targetNodup).mp (by
    simpa only [List.get_eq_getElem] using contextGet)

noncomputable def simulation
    (source : CheckedOpenDiagram signature)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.val.diagram.Encloses
      (source.val.diagram.wires outer).scope
      (source.val.diagram.wires inner).scope)
    (targetWellFormed :
      (Target source.val.diagram outer inner).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature) :
    ConcreteElaboration.ConcreteSemanticSimulation signature
      source.val.diagram (Target source.val.diagram outer inner) model named where
  source_wellFormed := source.property.diagram_well_formed
  target_wellFormed := targetWellFormed
  regionMap := id
  binderMap := id
  Distinguished := fun _ => False
  occurrenceMap := fun _ _ occurrence => occurrence
  occurrenceMap_node := by
    intro region regular node nodeRegion
    exact ⟨node, rfl⟩
  occurrenceMap_child := by
    intro region regular child
    rfl
  root_eq := rfl
  region_shape := by
    intro parent regular child childParent
    rw [target_regions]
    cases kind : source.val.diagram.regions child <;> simp [kind, id]
  localOccurrences_map := by
    intro region regular
    simp
  BinderWitness := fun {sourceRels targetRels} sourceBinders targetBinders =>
    ConcreteElaboration.IdentityBinderWitness
      (sourceRels := sourceRels) (targetRels := targetRels)
      source.val.diagram (Target source.val.diagram outer inner)
      sourceBinders targetBinders
  relationMap := fun witness =>
    ConcreteElaboration.IdentityBinderWitness.relationMap witness
  binders_empty := {
    relationContexts_eq := rfl
    binders_eq := HEq.rfl
  }
  binders_push := by
    intro sourceRels targetRels sourceBinders targetBinders witness child parent
      arity kind regular
    rcases witness with ⟨relationContextsEq, bindersEq⟩
    subst targetRels
    cases bindersEq
    exact ⟨rfl, HEq.rfl⟩
  relationMap_push := by
    intro sourceRels targetRels sourceBinders targetBinders witness child parent
      arity kind regular
    rcases witness with ⟨relationContextsEq, bindersEq⟩
    subst targetRels
    cases bindersEq
    simpa [ConcreteElaboration.IdentityBinderWitness.relationMap,
      ConcreteElaboration.identityRelationRenaming] using
        (RelationRenaming.lift_id_fun
          (source := sourceRels) arity).symm
  Allowed := Allowed source.val.diagram
    (source.val.diagram.wires inner).scope
  allowed_cut := by
    intro simulationDirection child parent childKind regular allowed
    exact allowed_cut source.val.diagram
      (source.val.diagram.wires inner).scope simulationDirection child parent
      childKind allowed
  allowed_bubble := by
    intro simulationDirection child parent arity childKind regular allowed
    exact allowed_bubble source.val.diagram
      (source.val.diagram.wires inner).scope simulationDirection child parent
      arity childKind allowed
  ContextWitness := fun sourceContext targetContext =>
    ContextWitness source.val.diagram outer inner distinct
      sourceContext targetContext
  AtRegion := fun _ _ => True
  indexRelation := fun witness =>
    ConcreteElaboration.ContextIndexRelation.forwardMap witness.indexMap
  extendContext := by
    intro sourceContext targetContext witness region regular sourceExact
      targetExact
    exact witness.extend source.property.diagram_well_formed ordered region
      sourceExact targetExact
  extendFocusedContext := by
    intro sourceContext targetContext witness region atRegion focused sourceExact
      targetExact
    exact False.elim focused
  at_child := by simp
  at_extended := by simp
  at_focused_child := by
    intro sourceContext targetContext witness parent focused sourceExact
      targetExact child atParent sourceParent targetParent
    exact False.elim focused
  localTransport := by
    intro sourceRels targetRels simulationDirection fuelSource fuelTarget
      sourceContext targetContext witness sourceBinders targetBinders
      binderWitness region atRegion regular allowed sourceExact targetExact
      _ _ _ _ sourceItems targetItems sourceCompiled targetCompiled itemSemantics
    refine ConcreteElaboration.directionalLocalTransport_of_agreement
      simulationDirection sourceContext targetContext region region
      (ConcreteElaboration.ContextIndexRelation.forwardMap witness.indexMap)
      (ConcreteElaboration.ContextIndexRelation.forwardMap
        (witness.extend source.property.diagram_well_formed ordered region
          sourceExact targetExact).indexMap)
      model named
      (sourceItems.renameRelations
        (ConcreteElaboration.IdentityBinderWitness.relationMap binderWitness))
      targetItems ?_ itemSemantics
    intro sourceOuter targetOuter outerAgrees
    rw [ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
      at outerAgrees
    cases simulationDirection with
    | forward =>
        intro sourceLocal
        have hne := allowed_forward_ne_site source.val.diagram
          (source.val.diagram.wires inner).scope region allowed
        refine ⟨targetLocalOfSource source.val.diagram outer inner distinct
          region hne sourceLocal, ?_⟩
        rw [ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
        exact witness.extendedEnvironment_forward
          source.property.diagram_well_formed ordered region hne sourceExact
          targetExact sourceOuter targetOuter outerAgrees sourceLocal
    | backward =>
        intro targetLocal
        refine ⟨sourceLocalOfTarget witness
          source.property.diagram_well_formed ordered region sourceExact
          targetExact targetOuter targetLocal, ?_⟩
        rw [ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
        exact witness.extendedEnvironment_backward
          source.property.diagram_well_formed ordered region sourceExact
          targetExact sourceOuter targetOuter outerAgrees targetLocal
  nodeSemantic := by
    intro sourceRels targetRels simulationDirection region sourceContext
      targetContext witness atRegion sourceNodup targetNodup sourceBinders
      targetBinders allowed binderWitness sourceNode targetNode regular
      nodeMapped nodeRegion sourceItem targetItem sourceCompiled targetCompiled
    rcases binderWitness with ⟨relationContextsEq, bindersEq⟩
    subst targetRels
    cases bindersEq
    have nodeEq : sourceNode = targetNode :=
      ConcreteElaboration.LocalOccurrence.node.inj nodeMapped
    subst targetNode
    apply ConcreteElaboration.compileNode?_itemSimulation_of_related_ports
      model named simulationDirection sourceContext targetContext
      (ConcreteElaboration.ContextIndexRelation.forwardMap witness.indexMap)
      sourceBinders sourceBinders
      (ConcreteElaboration.identityRelationRenaming sourceRels)
      sourceNode sourceNode id id
    · cases nodeShape : source.val.diagram.nodes sourceNode <;>
        simp [nodeShape, id]
    · intro port sourceIndex targetIndex sourceResolved targetResolved
      exact resolvedPorts_related source.val.diagram outer inner distinct
        targetWellFormed sourceContext targetContext witness targetNodup
        sourceNode port sourceIndex targetIndex sourceResolved targetResolved
    · intro atomRegion binder arity sourceRelation nodeShape binderLookup
      simpa [ConcreteElaboration.identityRelationRenaming] using binderLookup
    · exact sourceCompiled
    · exact targetCompiled
  focusedRegionKernel := by
    intro sourceRels targetRels simulationDirection fuelSource fuelTarget region
      sourceContext targetContext witness sourceBinders targetBinders atRegion
      focused
    exact False.elim focused

def targetOpenRaw
    (source : OpenConcreteDiagram)
    (outer inner : Fin source.diagram.wireCount)
    (distinct : outer ≠ inner) :
    OpenConcreteDiagram where
  diagram := Target source.diagram outer inner
  boundary := source.boundary.map
    (wireMap source.diagram outer inner distinct)

theorem targetOpenRaw_wellFormed
    (source : CheckedOpenDiagram signature)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.val.diagram.Encloses
      (source.val.diagram.wires outer).scope
      (source.val.diagram.wires inner).scope)
    (targetWellFormed :
      (Target source.val.diagram outer inner).WellFormed signature) :
    (targetOpenRaw source.val outer inner distinct).WellFormed signature where
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
      exact ConcreteElaboration.encloses_sheet_eq
        source.property.diagram_well_formed.root_is_sheet
        outerEnclosesRoot
    · simpa [hwire] using sourceRoot

def targetOpen
    (source : CheckedOpenDiagram signature)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.val.diagram.Encloses
      (source.val.diagram.wires outer).scope
      (source.val.diagram.wires inner).scope)
    (targetWellFormed :
      (Target source.val.diagram outer inner).WellFormed signature) :
    CheckedOpenDiagram signature :=
  ⟨targetOpenRaw source.val outer inner distinct,
    targetOpenRaw_wellFormed source outer inner distinct ordered
      targetWellFormed⟩

theorem targetOpenRaw_exposed_mem_iff
    (source : OpenConcreteDiagram)
    (outer inner : Fin source.diagram.wireCount)
    (distinct : outer ≠ inner)
    (targetWire : Fin (Target source.diagram outer inner).wireCount) :
    targetWire ∈
        (targetOpenRaw source outer inner distinct).exposedWires ↔
      ∃ sourceWire ∈ source.exposedWires,
        wireMap source.diagram outer inner distinct sourceWire = targetWire := by
  unfold OpenConcreteDiagram.exposedWires targetOpenRaw
  simp only [List.mem_eraseDups, List.mem_map]

noncomputable def exposedMap
    (source : OpenConcreteDiagram)
    (outer inner : Fin source.diagram.wireCount)
    (distinct : outer ≠ inner) :
    Fin source.exposedWires.length →
      Fin (targetOpenRaw source outer inner distinct).exposedWires.length :=
  fun sourceIndex =>
    Classical.choose
      (ConcreteElaboration.WireContext.lookup?_complete
        ((targetOpenRaw_exposed_mem_iff source outer inner distinct _).2
          ⟨source.exposedWires.get sourceIndex,
            List.get_mem _ sourceIndex, rfl⟩))

theorem exposedMap_get
    (source : OpenConcreteDiagram)
    (outer inner : Fin source.diagram.wireCount)
    (distinct : outer ≠ inner)
    (sourceIndex : Fin source.exposedWires.length) :
    (targetOpenRaw source outer inner distinct).exposedWires.get
        (exposedMap source outer inner distinct sourceIndex) =
      wireMap source.diagram outer inner distinct
        (source.exposedWires.get sourceIndex) := by
  exact ConcreteElaboration.WireContext.lookup?_sound
    (Classical.choose_spec
      (ConcreteElaboration.WireContext.lookup?_complete
        ((targetOpenRaw_exposed_mem_iff source outer inner distinct _).2
          ⟨source.exposedWires.get sourceIndex,
            List.get_mem _ sourceIndex, rfl⟩)))

theorem exposedMap_surjective
    (source : OpenConcreteDiagram)
    (outer inner : Fin source.diagram.wireCount)
    (distinct : outer ≠ inner) :
    Function.Surjective (exposedMap source outer inner distinct) := by
  intro targetIndex
  obtain ⟨sourceWire, sourceMember, mapped⟩ :=
    (targetOpenRaw_exposed_mem_iff source outer inner distinct
      ((targetOpenRaw source outer inner distinct).exposedWires.get
        targetIndex)).1 (List.get_mem _ targetIndex)
  obtain ⟨sourceIndex, lookup⟩ :=
    ConcreteElaboration.WireContext.lookup?_complete sourceMember
  refine ⟨sourceIndex, ?_⟩
  apply Fin.ext
  exact (List.getElem_inj
    (targetOpenRaw source outer inner distinct).exposedWires_nodup).mp (by
  have sourceGet :=
    ConcreteElaboration.WireContext.lookup?_sound lookup
  have chosenGet := exposedMap_get source outer inner distinct sourceIndex
  simpa only [List.get_eq_getElem] using
    chosenGet.trans
      ((congrArg (wireMap source.diagram outer inner distinct)
        sourceGet).trans mapped))

theorem exposedMap_injective_of_root_ne
    (source : CheckedOpenDiagram signature)
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
    (source : CheckedOpenDiagram signature)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.val.diagram.Encloses
      (source.val.diagram.wires outer).scope
      (source.val.diagram.wires inner).scope)
    (targetWellFormed :
      (Target source.val.diagram outer inner).WellFormed signature) :
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
      simpa only [OpenConcreteDiagram.rootWires] using
        ConcreteElaboration.openRootWires_exact source.property)
    (by
      let target := targetOpen source outer inner distinct ordered
        targetWellFormed
      simpa only [OpenConcreteDiagram.rootWires] using
        ConcreteElaboration.openRootWires_exact target.property)

theorem rootWitness_index_exposed
    (source : CheckedOpenDiagram signature)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.val.diagram.Encloses
      (source.val.diagram.wires outer).scope
      (source.val.diagram.wires inner).scope)
    (targetWellFormed :
      (Target source.val.diagram outer inner).WellFormed signature)
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
    simpa only [OpenConcreteDiagram.rootWires] using
      (targetOpenRaw source.val outer inner distinct).rootWires_nodup
  exact (List.getElem_inj targetNodup).mp (by
    simpa only [List.get_eq_getElem] using hget)

noncomputable def hiddenMap
    (source : CheckedOpenDiagram signature)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (rootNe : source.val.diagram.root ≠
      (source.val.diagram.wires inner).scope) :
    Fin source.val.hiddenWires.length →
      Fin (targetOpenRaw source.val outer inner distinct).hiddenWires.length :=
  fun sourceIndex =>
    let sourceWire := source.val.hiddenWires.get sourceIndex
    let targetWire :=
      wireMap source.val.diagram outer inner distinct sourceWire
    Classical.choose
      (ConcreteElaboration.WireContext.lookup?_complete (by
        apply (OpenConcreteDiagram.mem_hiddenWires
          (targetOpenRaw source.val outer inner distinct) targetWire).2
        have sourceHidden :=
          (OpenConcreteDiagram.mem_hiddenWires source.val sourceWire).1
            (List.get_mem source.val.hiddenWires sourceIndex)
        have sourceNe : sourceWire ≠ inner := by
          intro equality
          rw [equality] at sourceHidden
          exact rootNe sourceHidden.1.symm
        constructor
        · change
            ((Target source.val.diagram outer inner).wires
              (wireMap source.val.diagram outer inner distinct
                sourceWire)).scope =
              (Target source.val.diagram outer inner).root
          rw [target_wire_scope, if_neg sourceNe]
          exact sourceHidden.1
        · intro targetExposed
          obtain ⟨exposedWire, exposedMember, mapped⟩ :=
            (targetOpenRaw_exposed_mem_iff source.val outer inner distinct
              targetWire).1 targetExposed
          have collision := (wireMap_eq_iff source.val.diagram outer inner
            exposedWire sourceWire distinct).1 mapped
          rcases collision with same | outerInner | innerOuter
          · exact sourceHidden.2 (same ▸ exposedMember)
          · exact sourceNe outerInner.2
          · have innerRoot := source.property.exposed_root_scoped
              (innerOuter.1 ▸ exposedMember)
            exact rootNe innerRoot.symm))

theorem hiddenMap_get
    (source : CheckedOpenDiagram signature)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (rootNe : source.val.diagram.root ≠
      (source.val.diagram.wires inner).scope)
    (sourceIndex : Fin source.val.hiddenWires.length) :
    (targetOpenRaw source.val outer inner distinct).hiddenWires.get
        (hiddenMap source outer inner distinct rootNe sourceIndex) =
      wireMap source.val.diagram outer inner distinct
        (source.val.hiddenWires.get sourceIndex) := by
  exact ConcreteElaboration.WireContext.lookup?_sound
    (Classical.choose_spec
      (ConcreteElaboration.WireContext.lookup?_complete (by
        apply (OpenConcreteDiagram.mem_hiddenWires
          (targetOpenRaw source.val outer inner distinct)
          (wireMap source.val.diagram outer inner distinct
            (source.val.hiddenWires.get sourceIndex))).2
        have sourceHidden :=
          (OpenConcreteDiagram.mem_hiddenWires source.val
            (source.val.hiddenWires.get sourceIndex)).1
            (List.get_mem source.val.hiddenWires sourceIndex)
        have sourceNe : source.val.hiddenWires.get sourceIndex ≠ inner := by
          intro equality
          rw [equality] at sourceHidden
          exact rootNe sourceHidden.1.symm
        constructor
        · change
            ((Target source.val.diagram outer inner).wires
              (wireMap source.val.diagram outer inner distinct
                (source.val.hiddenWires.get sourceIndex))).scope =
              (Target source.val.diagram outer inner).root
          rw [target_wire_scope, if_neg sourceNe]
          exact sourceHidden.1
        · intro targetExposed
          obtain ⟨exposedWire, exposedMember, mapped⟩ :=
            (targetOpenRaw_exposed_mem_iff source.val outer inner distinct
              _).1 targetExposed
          have collision := (wireMap_eq_iff source.val.diagram outer inner
            exposedWire (source.val.hiddenWires.get sourceIndex)
            distinct).1 mapped
          rcases collision with same | outerInner | innerOuter
          · exact sourceHidden.2 (same ▸ exposedMember)
          · exact sourceNe outerInner.2
          · have innerRoot := source.property.exposed_root_scoped
              (innerOuter.1 ▸ exposedMember)
            exact rootNe innerRoot.symm)))

theorem hiddenMap_injective
    (source : CheckedOpenDiagram signature)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (rootNe : source.val.diagram.root ≠
      (source.val.diagram.wires inner).scope) :
    Function.Injective (hiddenMap source outer inner distinct rootNe) := by
  intro left right equality
  have getEquality := congrArg
    (List.get (targetOpenRaw source.val outer inner distinct).hiddenWires)
    equality
  rw [hiddenMap_get, hiddenMap_get] at getEquality
  have collision := (wireMap_eq_iff source.val.diagram outer inner
    (source.val.hiddenWires.get left)
    (source.val.hiddenWires.get right) distinct).1 getEquality
  have sourceGetEquality :
      source.val.hiddenWires.get left =
        source.val.hiddenWires.get right := by
    rcases collision with same | outerInner | innerOuter
    · exact same
    · have rightHidden :=
        (OpenConcreteDiagram.mem_hiddenWires source.val
          (source.val.hiddenWires.get right)).1
          (List.get_mem source.val.hiddenWires right)
      rw [outerInner.2] at rightHidden
      exact False.elim (rootNe rightHidden.1.symm)
    · have leftHidden :=
        (OpenConcreteDiagram.mem_hiddenWires source.val
          (source.val.hiddenWires.get left)).1
          (List.get_mem source.val.hiddenWires left)
      rw [innerOuter.1] at leftHidden
      exact False.elim (rootNe leftHidden.1.symm)
  apply Fin.ext
  exact (List.getElem_inj source.val.hiddenWires_nodup).mp (by
    simpa only [List.get_eq_getElem] using sourceGetEquality)

theorem hiddenMap_surjective
    (source : CheckedOpenDiagram signature)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (rootNe : source.val.diagram.root ≠
      (source.val.diagram.wires inner).scope) :
    Function.Surjective (hiddenMap source outer inner distinct rootNe) := by
  intro targetIndex
  let targetWire :=
    (targetOpenRaw source.val outer inner distinct).hiddenWires.get targetIndex
  let sourceWire := (joinWireDomain source.val.diagram inner).origin targetWire
  have sourceNe : sourceWire ≠ inner := by
    have survives :=
      (joinWireDomain source.val.diagram inner).origin_survives targetWire
    simpa [sourceWire, joinWireDomain] using survives
  have mapped :
      wireMap source.val.diagram outer inner distinct sourceWire =
        targetWire := by
    rw [wireMap_of_ne source.val.diagram outer inner sourceWire distinct
      sourceNe]
    exact (joinWireDomain source.val.diagram inner).index_origin targetWire
  have targetHidden :=
    (OpenConcreteDiagram.mem_hiddenWires
      (targetOpenRaw source.val outer inner distinct) targetWire).1
      (List.get_mem
        (targetOpenRaw source.val outer inner distinct).hiddenWires targetIndex)
  have sourceRoot :
      (source.val.diagram.wires sourceWire).scope =
        source.val.diagram.root := by
    have targetScope := targetHidden.1
    change
      ((Target source.val.diagram outer inner).wires targetWire).scope =
        (Target source.val.diagram outer inner).root at targetScope
    rw [← mapped, target_wire_scope, if_neg sourceNe] at targetScope
    exact targetScope
  have sourceNotExposed : sourceWire ∉ source.val.exposedWires := by
    intro sourceExposed
    have targetExposed :
        targetWire ∈
          (targetOpenRaw source.val outer inner distinct).exposedWires :=
      (targetOpenRaw_exposed_mem_iff source.val outer inner distinct
        targetWire).2 ⟨sourceWire, sourceExposed, mapped⟩
    exact targetHidden.2 targetExposed
  have sourceMember : sourceWire ∈ source.val.hiddenWires :=
    (OpenConcreteDiagram.mem_hiddenWires source.val sourceWire).2
      ⟨sourceRoot, sourceNotExposed⟩
  obtain ⟨sourceIndex, lookup⟩ :=
    ConcreteElaboration.WireContext.lookup?_complete sourceMember
  refine ⟨sourceIndex, ?_⟩
  apply Fin.ext
  exact (List.getElem_inj
    (targetOpenRaw source.val outer inner distinct).hiddenWires_nodup).mp (by
      have sourceGet :=
        ConcreteElaboration.WireContext.lookup?_sound lookup
      have chosenGet :=
        hiddenMap_get source outer inner distinct rootNe sourceIndex
      have hget :
          (targetOpenRaw source.val outer inner distinct).hiddenWires.get
              (hiddenMap source outer inner distinct rootNe sourceIndex) =
            (targetOpenRaw source.val outer inner distinct).hiddenWires.get
              targetIndex :=
        chosenGet.trans
          ((congrArg (wireMap source.val.diagram outer inner distinct)
            sourceGet).trans mapped)
      simpa only [List.get_eq_getElem] using hget)

noncomputable def hiddenInverse
    (source : CheckedOpenDiagram signature)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (rootNe : source.val.diagram.root ≠
      (source.val.diagram.wires inner).scope)
    (targetIndex :
      Fin (targetOpenRaw source.val outer inner distinct).hiddenWires.length) :
    Fin source.val.hiddenWires.length :=
  Classical.choose
    (hiddenMap_surjective source outer inner distinct rootNe targetIndex)

theorem hiddenInverse_spec
    (source : CheckedOpenDiagram signature)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (rootNe : source.val.diagram.root ≠
      (source.val.diagram.wires inner).scope)
    (targetIndex :
      Fin (targetOpenRaw source.val outer inner distinct).hiddenWires.length) :
    hiddenMap source outer inner distinct rootNe
        (hiddenInverse source outer inner distinct rootNe targetIndex) =
      targetIndex :=
  Classical.choose_spec
    (hiddenMap_surjective source outer inner distinct rootNe targetIndex)

theorem hiddenInverse_hiddenMap
    (source : CheckedOpenDiagram signature)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (rootNe : source.val.diagram.root ≠
      (source.val.diagram.wires inner).scope)
    (sourceIndex : Fin source.val.hiddenWires.length) :
    hiddenInverse source outer inner distinct rootNe
        (hiddenMap source outer inner distinct rootNe sourceIndex) =
      sourceIndex := by
  apply hiddenMap_injective source outer inner distinct rootNe
  exact hiddenInverse_spec source outer inner distinct rootNe _

def rightIndex (left right : List α) :
    Fin right.length → Fin (left ++ right).length :=
  fun index => Fin.cast
    (by simp : left.length + right.length = (left ++ right).length)
    (Fin.natAdd left.length index)

@[simp] theorem get_rightIndex (left right : List α)
    (index : Fin right.length) :
    (left ++ right).get (rightIndex left right index) = right.get index := by
  simp [rightIndex]

@[simp] theorem rootEnvironment_leftIndex
    (left right : ConcreteElaboration.WireContext diagram)
    (outerEnv : Fin left.length → D)
    (localEnv : Fin right.length → D)
    (index : Fin left.length) :
    ConcreteElaboration.rootEnvironment left right outerEnv localEnv
        (leftIndex left right index) =
      outerEnv index := by
  simp [ConcreteElaboration.rootEnvironment, leftIndex, extendWireEnv]

@[simp] theorem rootEnvironment_rightIndex
    (left right : ConcreteElaboration.WireContext diagram)
    (outerEnv : Fin left.length → D)
    (localEnv : Fin right.length → D)
    (index : Fin right.length) :
    ConcreteElaboration.rootEnvironment left right outerEnv localEnv
        (rightIndex left right index) =
      localEnv index := by
  simp [ConcreteElaboration.rootEnvironment, rightIndex, extendWireEnv]

theorem rootWitness_index_hidden
    (source : CheckedOpenDiagram signature)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.val.diagram.Encloses
      (source.val.diagram.wires outer).scope
      (source.val.diagram.wires inner).scope)
    (targetWellFormed :
      (Target source.val.diagram outer inner).WellFormed signature)
    (rootNe : source.val.diagram.root ≠
      (source.val.diagram.wires inner).scope)
    (sourceIndex : Fin source.val.hiddenWires.length) :
    (rootWitness source outer inner distinct ordered targetWellFormed).indexMap
        (rightIndex source.val.exposedWires source.val.hiddenWires
          sourceIndex) =
      rightIndex
        (targetOpenRaw source.val outer inner distinct).exposedWires
        (targetOpenRaw source.val outer inner distinct).hiddenWires
        (hiddenMap source outer inner distinct rootNe sourceIndex) := by
  let witness := rootWitness source outer inner distinct ordered
    targetWellFormed
  change witness.indexMap
      (rightIndex source.val.exposedWires source.val.hiddenWires sourceIndex) =
    rightIndex
      (targetOpenRaw source.val outer inner distinct).exposedWires
      (targetOpenRaw source.val outer inner distinct).hiddenWires
      (hiddenMap source outer inner distinct rootNe sourceIndex)
  apply Fin.ext
  have mappedGet := witness.get
    (rightIndex source.val.exposedWires source.val.hiddenWires sourceIndex)
  rw [get_rightIndex] at mappedGet
  have hget :
      ((targetOpenRaw source.val outer inner distinct).exposedWires ++
          (targetOpenRaw source.val outer inner distinct).hiddenWires).get
          (witness.indexMap
            (rightIndex source.val.exposedWires source.val.hiddenWires
              sourceIndex)) =
        ((targetOpenRaw source.val outer inner distinct).exposedWires ++
          (targetOpenRaw source.val outer inner distinct).hiddenWires).get
          (rightIndex
            (targetOpenRaw source.val outer inner distinct).exposedWires
            (targetOpenRaw source.val outer inner distinct).hiddenWires
            (hiddenMap source outer inner distinct rootNe sourceIndex)) := by
    simpa only [get_rightIndex] using
      mappedGet.trans
        (hiddenMap_get source outer inner distinct rootNe sourceIndex).symm
  have targetNodup :
      ((targetOpenRaw source.val outer inner distinct).exposedWires ++
        (targetOpenRaw source.val outer inner distinct).hiddenWires).Nodup := by
    simpa only [OpenConcreteDiagram.rootWires] using
      (targetOpenRaw source.val outer inner distinct).rootWires_nodup
  exact (List.getElem_inj targetNodup).mp (by
    simpa only [List.get_eq_getElem] using hget)

noncomputable def targetHiddenOfSource
    (source : CheckedOpenDiagram signature)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (rootNe : source.val.diagram.root ≠
      (source.val.diagram.wires inner).scope)
    (sourceHidden : Fin source.val.hiddenWires.length → D) :
    Fin (targetOpenRaw source.val outer inner distinct).hiddenWires.length → D :=
  sourceHidden ∘ hiddenInverse source outer inner distinct rootNe

@[simp] theorem targetHiddenOfSource_hiddenMap
    (source : CheckedOpenDiagram signature)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (rootNe : source.val.diagram.root ≠
      (source.val.diagram.wires inner).scope)
    (sourceHidden : Fin source.val.hiddenWires.length → D)
    (sourceIndex : Fin source.val.hiddenWires.length) :
    targetHiddenOfSource source outer inner distinct rootNe sourceHidden
        (hiddenMap source outer inner distinct rootNe sourceIndex) =
      sourceHidden sourceIndex := by
  simp [targetHiddenOfSource, hiddenInverse_hiddenMap]

noncomputable def sourceHiddenOfTarget
    (source : CheckedOpenDiagram signature)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.val.diagram.Encloses
      (source.val.diagram.wires outer).scope
      (source.val.diagram.wires inner).scope)
    (targetWellFormed :
      (Target source.val.diagram outer inner).WellFormed signature)
    (targetOuter :
      Fin (targetOpenRaw source.val outer inner distinct).exposedWires.length → D)
    (targetHidden :
      Fin (targetOpenRaw source.val outer inner distinct).hiddenWires.length → D) :
    Fin source.val.hiddenWires.length → D :=
  fun sourceIndex =>
    ConcreteElaboration.rootEnvironment
      (targetOpenRaw source.val outer inner distinct).exposedWires
      (targetOpenRaw source.val outer inner distinct).hiddenWires
      targetOuter targetHidden
      ((rootWitness source outer inner distinct ordered
        targetWellFormed).indexMap
        (rightIndex source.val.exposedWires source.val.hiddenWires
          sourceIndex))

theorem rootEnvironment_forward
    (source : CheckedOpenDiagram signature)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.val.diagram.Encloses
      (source.val.diagram.wires outer).scope
      (source.val.diagram.wires inner).scope)
    (targetWellFormed :
      (Target source.val.diagram outer inner).WellFormed signature)
    (rootNe : source.val.diagram.root ≠
      (source.val.diagram.wires inner).scope)
    (sourceOuter : Fin source.val.exposedWires.length → D)
    (targetOuter :
      Fin (targetOpenRaw source.val outer inner distinct).exposedWires.length → D)
    (outerAgrees :
      sourceOuter = targetOuter ∘ exposedMap source.val outer inner distinct)
    (sourceHidden : Fin source.val.hiddenWires.length → D) :
    ConcreteElaboration.rootEnvironment source.val.exposedWires
        source.val.hiddenWires sourceOuter sourceHidden =
      ConcreteElaboration.rootEnvironment
          (targetOpenRaw source.val outer inner distinct).exposedWires
          (targetOpenRaw source.val outer inner distinct).hiddenWires
          targetOuter
          (targetHiddenOfSource source outer inner distinct rootNe
            sourceHidden) ∘
        (rootWitness source outer inner distinct ordered
          targetWellFormed).indexMap := by
  funext sourceIndex
  let split : Fin
      (source.val.exposedWires.length + source.val.hiddenWires.length) :=
    Fin.cast (by simp) sourceIndex
  have recover :
      Fin.cast
          (by simp :
            source.val.exposedWires.length + source.val.hiddenWires.length =
              (source.val.exposedWires ++ source.val.hiddenWires).length)
          split =
        sourceIndex := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun exposedIndex => ?_) (fun hiddenIndex => ?_) split
  · have indexEq := rootWitness_index_exposed source outer inner distinct
      ordered targetWellFormed exposedIndex
    have inputEq :
        Fin.cast (by simp)
            (Fin.castAdd source.val.hiddenWires.length exposedIndex) =
          leftIndex source.val.exposedWires source.val.hiddenWires
            exposedIndex := by
      apply Fin.ext
      rfl
    simp only [Function.comp_apply]
    rw [inputEq, rootEnvironment_leftIndex, indexEq,
      rootEnvironment_leftIndex]
    simpa [Function.comp_def] using congrFun outerAgrees exposedIndex
  · have indexEq := rootWitness_index_hidden source outer inner distinct
      ordered targetWellFormed rootNe hiddenIndex
    have inputEq :
        Fin.cast (by simp)
            (Fin.natAdd source.val.exposedWires.length hiddenIndex) =
          rightIndex source.val.exposedWires source.val.hiddenWires
            hiddenIndex := by
      apply Fin.ext
      rfl
    simp only [Function.comp_apply]
    rw [inputEq, rootEnvironment_rightIndex, indexEq,
      rootEnvironment_rightIndex, targetHiddenOfSource_hiddenMap]

theorem rootEnvironment_backward
    (source : CheckedOpenDiagram signature)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.val.diagram.Encloses
      (source.val.diagram.wires outer).scope
      (source.val.diagram.wires inner).scope)
    (targetWellFormed :
      (Target source.val.diagram outer inner).WellFormed signature)
    (sourceOuter : Fin source.val.exposedWires.length → D)
    (targetOuter :
      Fin (targetOpenRaw source.val outer inner distinct).exposedWires.length → D)
    (outerAgrees :
      sourceOuter = targetOuter ∘ exposedMap source.val outer inner distinct)
    (targetHidden :
      Fin (targetOpenRaw source.val outer inner distinct).hiddenWires.length → D) :
    ConcreteElaboration.rootEnvironment source.val.exposedWires
        source.val.hiddenWires sourceOuter
        (sourceHiddenOfTarget source outer inner distinct ordered
          targetWellFormed targetOuter targetHidden) =
      ConcreteElaboration.rootEnvironment
          (targetOpenRaw source.val outer inner distinct).exposedWires
          (targetOpenRaw source.val outer inner distinct).hiddenWires
          targetOuter targetHidden ∘
        (rootWitness source outer inner distinct ordered
          targetWellFormed).indexMap := by
  funext sourceIndex
  let split : Fin
      (source.val.exposedWires.length + source.val.hiddenWires.length) :=
    Fin.cast (by simp) sourceIndex
  have recover :
      Fin.cast
          (by simp :
            source.val.exposedWires.length + source.val.hiddenWires.length =
              (source.val.exposedWires ++ source.val.hiddenWires).length)
          split =
        sourceIndex := by
    apply Fin.ext
    rfl
  rw [← recover]
  refine Fin.addCases (fun exposedIndex => ?_) (fun hiddenIndex => ?_) split
  · have indexEq := rootWitness_index_exposed source outer inner distinct
      ordered targetWellFormed exposedIndex
    have inputEq :
        Fin.cast (by simp)
            (Fin.castAdd source.val.hiddenWires.length exposedIndex) =
          leftIndex source.val.exposedWires source.val.hiddenWires
            exposedIndex := by
      apply Fin.ext
      rfl
    simp only [Function.comp_apply]
    rw [inputEq, rootEnvironment_leftIndex, indexEq,
      rootEnvironment_leftIndex]
    simpa [Function.comp_def] using congrFun outerAgrees exposedIndex
  · have inputEq :
        Fin.cast (by simp)
            (Fin.natAdd source.val.exposedWires.length hiddenIndex) =
          rightIndex source.val.exposedWires source.val.hiddenWires
            hiddenIndex := by
      apply Fin.ext
      rfl
    simp only [Function.comp_apply]
    rw [inputEq, rootEnvironment_rightIndex]
    rfl

noncomputable def rootContext
    (source : CheckedOpenDiagram signature)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.val.diagram.Encloses
      (source.val.diagram.wires outer).scope
      (source.val.diagram.wires inner).scope)
    (targetWellFormed :
      (Target source.val.diagram outer inner).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (orientation : Orientation) :
    let semanticSimulation := simulation source outer inner distinct ordered
      targetWellFormed model named
    ConcreteElaboration.ConcreteSemanticSimulation.RootContextSimulation
      semanticSimulation (direction orientation)
      source.val.exposedWires source.val.hiddenWires
      (targetOpenRaw source.val outer inner distinct).exposedWires
      (targetOpenRaw source.val outer inner distinct).hiddenWires := by
  let semanticSimulation := simulation source outer inner distinct ordered
    targetWellFormed model named
  refine {
    outer := ConcreteElaboration.ContextIndexRelation.forwardMap
      (exposedMap source.val outer inner distinct)
    context := rootWitness source outer inner distinct ordered
      targetWellFormed
    atRoot := True.intro
    atRootChild := by
      intro regular child parent
      trivial
    atFocusedRootChild := by
      intro focused
      exact False.elim focused
    transport := ?_
    focusedRootKernel := ?_
  }
  · intro regular allowed sourceItems targetItems sourceCompiled
      targetCompiled itemSemantics
    refine ConcreteElaboration.directionalRootTransport_of_agreement
      (direction orientation)
      source.val.exposedWires source.val.hiddenWires
      (targetOpenRaw source.val outer inner distinct).exposedWires
      (targetOpenRaw source.val outer inner distinct).hiddenWires
      (ConcreteElaboration.ContextIndexRelation.forwardMap
        (exposedMap source.val outer inner distinct))
      (ConcreteElaboration.ContextIndexRelation.forwardMap
        (rootWitness source outer inner distinct ordered
          targetWellFormed).indexMap)
      model named
      (sourceItems.renameRelations
        (semanticSimulation.relationMap semanticSimulation.binders_empty))
      targetItems ?_ itemSemantics
    intro sourceOuter targetOuter outerAgrees
    rw [ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
      at outerAgrees
    cases orientation with
    | forward =>
        intro sourceHidden
        have rootNe := allowed_forward_ne_site source.val.diagram
          (source.val.diagram.wires inner).scope source.val.diagram.root allowed
        refine ⟨targetHiddenOfSource source outer inner distinct rootNe
          sourceHidden, ?_⟩
        rw [ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
        exact rootEnvironment_forward source outer inner distinct ordered
          targetWellFormed rootNe sourceOuter targetOuter outerAgrees
          sourceHidden
    | backward =>
        intro targetHidden
        refine ⟨sourceHiddenOfTarget source outer inner distinct ordered
          targetWellFormed targetOuter targetHidden, ?_⟩
        rw [ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
        exact rootEnvironment_backward source outer inner distinct ordered
          targetWellFormed sourceOuter targetOuter outerAgrees targetHidden
  · intro atRoot distinguished
    exact False.elim distinguished

theorem boundaryLengthEq
    (source : OpenConcreteDiagram)
    (outer inner : Fin source.diagram.wireCount)
    (distinct : outer ≠ inner) :
    (targetOpenRaw source outer inner distinct).boundary.length =
      source.boundary.length := by
  simp [targetOpenRaw]

theorem boundaryClass_map
    (source : OpenConcreteDiagram)
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

noncomputable def exposedInverse
    (source : OpenConcreteDiagram)
    (outer inner : Fin source.diagram.wireCount)
    (distinct : outer ≠ inner)
    (targetIndex :
      Fin (targetOpenRaw source outer inner distinct).exposedWires.length) :
    Fin source.exposedWires.length :=
  Classical.choose
    (exposedMap_surjective source outer inner distinct targetIndex)

theorem exposedInverse_spec
    (source : OpenConcreteDiagram)
    (outer inner : Fin source.diagram.wireCount)
    (distinct : outer ≠ inner)
    (targetIndex :
      Fin (targetOpenRaw source outer inner distinct).exposedWires.length) :
    exposedMap source outer inner distinct
        (exposedInverse source outer inner distinct targetIndex) =
      targetIndex :=
  Classical.choose_spec
    (exposedMap_surjective source outer inner distinct targetIndex)

theorem exposedInverse_exposedMap
    (source : CheckedOpenDiagram signature)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (rootNe : source.val.diagram.root ≠
      (source.val.diagram.wires inner).scope)
    (sourceIndex : Fin source.val.exposedWires.length) :
    exposedInverse source.val outer inner distinct
        (exposedMap source.val outer inner distinct sourceIndex) =
      sourceIndex := by
  apply exposedMap_injective_of_root_ne source outer inner distinct rootNe
  exact exposedInverse_spec source.val outer inner distinct _

private theorem boundaryWitness
    (source : CheckedOpenDiagram signature)
    (outer inner : Fin source.val.diagram.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.val.diagram.Encloses
      (source.val.diagram.wires outer).scope
      (source.val.diagram.wires inner).scope)
    (targetWellFormed :
      (Target source.val.diagram outer inner).WellFormed signature)
    (orientation : Orientation)
    (allowed :
      Allowed source.val.diagram (source.val.diagram.wires inner).scope
        (direction orientation) source.val.diagram.root)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (sourceArgs : Fin source.val.boundary.length → model.Carrier) :
    ConcreteElaboration.ConcreteSemanticSimulation.DirectionalBoundaryWitness
      (direction orientation) source.elaborate
      (targetOpen source outer inner distinct ordered
        targetWellFormed).elaborate
      (ConcreteElaboration.ContextIndexRelation.forwardMap
        (exposedMap source.val outer inner distinct))
      model named sourceArgs
      (sourceArgs ∘
        Fin.cast (boundaryLengthEq source.val outer inner distinct)) := by
  cases orientation with
  | forward =>
      intro sourceAssignment sourceArgsEq sourceDenotes
      have rootNe := allowed_forward_ne_site source.val.diagram
        (source.val.diagram.wires inner).scope source.val.diagram.root allowed
      let targetAssignment : BoundaryAssignment
          (targetOpen source outer inner distinct ordered
            targetWellFormed).elaborate model.Carrier := {
        args := sourceArgs ∘
          Fin.cast (boundaryLengthEq source.val outer inner distinct)
        classes := sourceAssignment.classes ∘
          exposedInverse source.val outer inner distinct
        agrees := by
          intro targetPosition
          let sourcePosition := Fin.cast
            (boundaryLengthEq source.val outer inner distinct) targetPosition
          have classEq := boundaryClass_map source.val outer inner distinct
            targetPosition
          change sourceAssignment.classes
              (exposedInverse source.val outer inner distinct
                ((targetOpenRaw source.val outer inner distinct).boundaryClass
                  targetPosition)) =
            sourceArgs sourcePosition
          rw [classEq]
          have inverseEq :
              exposedInverse source.val outer inner distinct
                  (exposedMap source.val outer inner distinct
                    (source.val.boundaryClass sourcePosition)) =
                source.val.boundaryClass sourcePosition := by
            exact exposedInverse_exposedMap source outer inner distinct rootNe _
          rw [inverseEq]
          have sourceAgrees := sourceAssignment.agrees sourcePosition
          rw [sourceArgsEq] at sourceAgrees
          exact sourceAgrees
      }
      refine ⟨targetAssignment, rfl, ?_⟩
      rw [ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]
      funext sourceClass
      simp [targetAssignment,
        exposedInverse_exposedMap source outer inner distinct rootNe]
  | backward =>
      intro targetAssignment targetArgsEq targetDenotes
      let sourceAssignment : BoundaryAssignment source.elaborate
          model.Carrier := {
        args := sourceArgs
        classes := targetAssignment.classes ∘
          exposedMap source.val outer inner distinct
        agrees := by
          intro sourcePosition
          let targetPosition := Fin.cast
            (boundaryLengthEq source.val outer inner distinct).symm
            sourcePosition
          have classEq := boundaryClass_map source.val outer inner distinct
            targetPosition
          have positionEq :
              Fin.cast (boundaryLengthEq source.val outer inner distinct)
                  targetPosition =
                sourcePosition := by
            apply Fin.ext
            rfl
          rw [positionEq] at classEq
          change targetAssignment.classes
              (exposedMap source.val outer inner distinct
                (source.val.boundaryClass sourcePosition)) =
            sourceArgs sourcePosition
          rw [← classEq]
          have targetAgrees := targetAssignment.agrees targetPosition
          rw [targetArgsEq] at targetAgrees
          exact targetAgrees
      }
      refine ⟨sourceAssignment, rfl, ?_⟩
      rw [ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap]

private theorem wireMap_index?
    (input : ConcreteDiagram)
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
    (input : ConcreteDiagram)
    (outer inner sourceWire : Fin input.wireCount)
    (distinct : outer ≠ inner)
    (mapped : Fin (Target input outer inner).wireCount)
    (image :
      (joinWireInterfaceTransport input outer inner).image? sourceWire =
        some mapped) :
    mapped = wireMap input outer inner distinct sourceWire := by
  unfold joinWireInterfaceTransport InterfaceTransport.rootFiltered at image
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
    (input : ConcreteDiagram)
    (outer inner : Fin input.wireCount)
    (distinct : outer ≠ inner)
    (boundary : List (Fin input.wireCount))
    (mapped : List (Fin (Target input outer inner).wireCount))
    (transport :
      (joinWireInterfaceTransport input outer inner).transportBoundary
          boundary =
        some mapped) :
    mapped = boundary.map (wireMap input outer inner distinct) := by
  have image : ∀ sourceWire, sourceWire ∈ boundary →
      (joinWireInterfaceTransport input outer inner).image? sourceWire =
        some (wireMap input outer inner distinct sourceWire) := by
    intro sourceWire member
    obtain ⟨sourceIndex, sourceGet⟩ := List.mem_iff_get.mp member
    have point :=
      (joinWireInterfaceTransport input outer inner).transportBoundary_get
        transport sourceIndex
    have mappedEq := interface_image_eq_wireMap_of_some input outer inner
      (boundary.get sourceIndex) distinct _ point
    rw [← sourceGet]
    rw [point, mappedEq]
  have canonical :=
    (joinWireInterfaceTransport input outer inner).transportBoundary_eq_map
      (wireMap input outer inner distinct) image
  exact Option.some.inj (transport.symm.trans canonical)

private def operationalOpen
    (source : OpenProofState signature)
    (outer inner : Fin source.diagram.val.wireCount)
    (distinct : outer ≠ inner)
    (ordered : source.diagram.val.Encloses
      (source.diagram.val.wires outer).scope
      (source.diagram.val.wires inner).scope)
    (targetWellFormed :
      (Target source.diagram.val outer inner).WellFormed signature) :
    CheckedOpenDiagram signature :=
  targetOpen source.asCheckedOpen outer inner distinct ordered targetWellFormed

private def operationalIso
    {input : CheckedDiagram signature}
    {receipt : StepReceipt input}
    {outer inner : Fin input.val.wireCount}
    (realizes : receipt.Realizes
      (Target input.val outer inner)
      (joinWireProvenance input.val outer inner)
      (joinWireInterfaceTransport input.val outer inner))
    (distinct : outer ≠ inner)
    (ordered : input.val.Encloses
      (input.val.wires outer).scope (input.val.wires inner).scope)
    (targetWellFormed : (Target input.val outer inner).WellFormed signature)
    (boundary : List (Fin input.val.wireCount))
    (sourceRoot : ∀ candidate, candidate ∈ boundary →
      (input.val.wires candidate).scope = input.val.root)
    (mapped : List (Fin receipt.result.val.wireCount))
    (transport : receipt.interface.transportBoundary boundary = some mapped) :
    OpenConcreteIso
      (operationalOpen {
        diagram := input
        boundary := boundary
        boundary_root_scoped := sourceRoot
      } outer inner distinct ordered targetWellFormed).val
      (realizes.rawResultOpen mapped) := by
  apply realizes.operationalIso_to_rawResultOpen transport
    (boundary.map (wireMap input.val outer inner distinct))
  have expected := realizes.transportBoundary_expected transport
  have rawEq := interface_transportBoundary_eq_map input.val outer inner
    distinct boundary _ expected
  simpa [rawEq] using expected

private theorem orderedReceipt_sound
    (context : ProofContext signature)
    (orientation : Orientation)
    (input : CheckedDiagram signature)
    (stepFirst stepSecond outer inner : Fin input.val.wireCount)
    (receipt : StepReceipt input)
    (realizes : receipt.Realizes
      (Target input.val outer inner)
      (joinWireProvenance input.val outer inner)
      (joinWireInterfaceTransport input.val outer inner))
    (distinct : outer ≠ inner)
    (ordered : input.val.Encloses
      (input.val.wires outer).scope (input.val.wires inner).scope)
    (polarity : spawnPolarity orientation
      (concreteCutDepth input.val (input.val.wires inner).scope)) :
    SuccessfulReceiptSound context orientation input
      (.wireJoin stepFirst stepSecond) receipt := by
  have targetWellFormed :
      (Target input.val outer inner).WellFormed signature :=
    realizes.result_eq ▸ receipt.result.property
  apply SuccessfulReceiptSound.of_realized_operational realizes
    (operational := fun boundary sourceRoot mapped transport =>
      operationalOpen {
        diagram := input
        boundary := boundary
        boundary_root_scoped := sourceRoot
      } outer inner distinct ordered targetWellFormed)
    (operationalIso := fun boundary sourceRoot mapped transport =>
      operationalIso realizes distinct ordered targetWellFormed boundary
        sourceRoot mapped transport)
  intro boundary sourceRoot mapped transport valid args
  let source : OpenProofState signature := {
    diagram := input
    boundary := boundary
    boundary_root_scoped := sourceRoot
  }
  let target := operationalOpen source outer inner distinct ordered
    targetWellFormed
  let model := Lambda.canonicalModel
  let named := Theory.interpretDefinitions context.definitions
  let semanticSimulation := simulation source.asCheckedOpen outer inner
    distinct ordered targetWellFormed model named
  let rootSimulation := rootContext source.asCheckedOpen outer inner distinct
    ordered targetWellFormed model named orientation
  have allowed :
      semanticSimulation.Allowed (direction orientation)
        source.asCheckedOpen.val.diagram.root := by
    exact allowed_root source.asCheckedOpen
      (source.asCheckedOpen.val.diagram.wires inner).scope orientation polarity
  have boundaryTransport := boundaryWitness source.asCheckedOpen outer inner
    distinct ordered targetWellFormed orientation allowed model named args
  have semantic :=
    ConcreteElaboration.ConcreteSemanticSimulation.elaborateOpen_denote
      source.asCheckedOpen target model named semanticSimulation
      (direction orientation) rootSimulation allowed args
      (args ∘ Fin.cast
        (boundaryLengthEq source.asCheckedOpen.val outer inner distinct))
      boundaryTransport
  dsimp only
  unfold DirectedEntailment DirectedImplication
  cases orientation with
  | forward =>
      intro sourceDenotes
      have targetDenotes := semantic sourceDenotes
      simpa [source, target, direction, operationalOpen, targetOpen] using
        targetDenotes
  | backward =>
      intro targetDenotes
      apply semantic
      simpa [source, target, direction, operationalOpen, targetOpen] using
        targetDenotes

/-- Every successful wire-join receipt preserves ordered-open semantics. -/
theorem wireJoinReceipt_sound
    (context : ProofContext signature)
    (orientation : Orientation)
    (input : CheckedDiagram signature)
    (first second : Fin input.val.wireCount)
    (receipt : StepReceipt input)
    (applyResult :
      applyWireJoin orientation input first second = .ok receipt) :
    SuccessfulReceiptSound context orientation input
      (.wireJoin first second) receipt := by
  unfold applyWireJoin at applyResult
  split at applyResult
  · contradiction
  · rename_i distinct
    dsimp only at applyResult
    split at applyResult
    · rename_i ordered
      split at applyResult
      · rename_i polarity
        split at applyResult
        · contradiction
        · rename_i checked checkResult
          cases applyResult
          apply orderedReceipt_sound context orientation input first second
            first second _ _ distinct ordered polarity
          exact StepReceipt.ofChecked_realizes _ _ _ _ checked checkResult
      · contradiction
    · split at applyResult
      · rename_i reverseOrdered
        split at applyResult
        · rename_i polarity
          split at applyResult
          · contradiction
          · rename_i checked checkResult
            cases applyResult
            apply orderedReceipt_sound context orientation input first second
              second first _ _
                (fun equality => distinct equality.symm)
                reverseOrdered polarity
            exact StepReceipt.ofChecked_realizes _ _ _ _ checked checkResult
        · contradiction
      · contradiction

end WireJoinSoundness

end VisualProof.Rule
