import VisualProof.Rule.Soundness.Modal.Root
import VisualProof.Rule.Structural.Semantics

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram

private theorem map_append_elimination
    (map : α → β) (first second : List α) :
    (first ++ second).map map = first.map map ++ second.map map := by
  induction first with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.cons_append, List.map_cons]
      rw [induction]

private theorem eq_singleton_of_nodup_mem_unique
    [DecidableEq α] (items : List α) (chosen : α)
    (nodup : items.Nodup) (member : chosen ∈ items)
    (unique : ∀ item, item ∈ items → item = chosen) :
    items = [chosen] := by
  cases items with
  | nil => exact False.elim (List.not_mem_nil member)
  | cons head tail =>
      have headEq : head = chosen := unique head (by simp)
      subst head
      cases tail with
      | nil => rfl
      | cons next rest =>
          have nextEq : next = chosen := unique next (by simp)
          subst next
          have absent := (List.nodup_cons.mp nodup).1
          exact False.elim (absent (by simp))

namespace DoubleCutElimTrace

theorem outer_parent
    (trace : DoubleCutElimTrace input outer raw) :
    (input.regions outer).parent? = some trace.target := by
  simp [trace.outer_eq, CRegion.parent?]

theorem inner_parent
    (trace : DoubleCutElimTrace input outer raw) :
    (input.regions trace.inner).parent? = some outer := by
  simp [trace.inner_eq, CRegion.parent?]

private theorem directParent_encloses
    (input : ConcreteDiagram)
    {child parent : Fin input.regionCount}
    (parentEq : (input.regions child).parent? = some parent) :
    input.Encloses parent child := by
  refine ⟨⟨1, by have := child.isLt; omega⟩, ?_⟩
  simp [ConcreteDiagram.climb, parentEq]

theorem outer_ne_inner
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature) :
    outer ≠ trace.inner := by
  intro equality
  apply ConcreteElaboration.checked_direct_child_not_encloses_parent
    wellFormed trace.inner_parent
  rw [← equality]
  exact ConcreteDiagram.Encloses.refl input outer

theorem outer_ne_target
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature) :
    outer ≠ trace.target := by
  intro equality
  apply ConcreteElaboration.checked_direct_child_not_encloses_parent
    wellFormed trace.outer_parent
  rw [← equality]
  exact ConcreteDiagram.Encloses.refl input outer

theorem inner_ne_target
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature) :
    trace.inner ≠ trace.target := by
  intro equality
  apply ConcreteElaboration.checked_direct_child_not_encloses_parent
    wellFormed trace.inner_parent
  have encloses := directParent_encloses input trace.outer_parent
  simpa [equality] using encloses

theorem child_eq_inner
    (trace : DoubleCutElimTrace input outer raw)
    (child : Fin input.regionCount)
    (parentEq : (input.regions child).parent? = some outer) :
    child = trace.inner := by
  have member :
      child ∈ filterFin (fun region =>
        decide ((input.regions region).parent? = some outer)) := by
    rw [mem_filterFin]
    exact decide_eq_true parentEq
  rw [trace.children_eq] at member
  simpa using member

theorem node_region_ne_outer
    (trace : DoubleCutElimTrace input outer raw)
    (node : Fin input.nodeCount) :
    (input.nodes node).region ≠ outer := by
  intro equality
  have empty :
      (filterFin fun candidate =>
        decide ((input.nodes candidate).region = outer)) = [] :=
    List.isEmpty_iff.mp trace.outer_nodes_empty
  have member :
      node ∈ filterFin (fun candidate =>
        decide ((input.nodes candidate).region = outer)) := by
    rw [mem_filterFin]
    exact decide_eq_true equality
  rw [empty] at member
  exact List.not_mem_nil member

theorem wire_scope_ne_outer
    (trace : DoubleCutElimTrace input outer raw)
    (wire : Fin input.wireCount) :
    (input.wires wire).scope ≠ outer := by
  intro equality
  have empty :
      (filterFin fun candidate =>
        decide ((input.wires candidate).scope = outer)) = [] :=
    List.isEmpty_iff.mp trace.outer_wires_empty
  have member :
      wire ∈ filterFin (fun candidate =>
        decide ((input.wires candidate).scope = outer)) := by
    rw [mem_filterFin]
    exact decide_eq_true equality
  rw [empty] at member
  exact List.not_mem_nil member

@[simp] theorem domain_outer
    (trace : DoubleCutElimTrace input outer raw) :
    (doubleCutRegionDomain input outer trace.inner).survives outer = false := by
  simp [doubleCutRegionDomain]

@[simp] theorem domain_inner
    (trace : DoubleCutElimTrace input outer raw) :
    (doubleCutRegionDomain input outer trace.inner).survives trace.inner =
      false := by
  simp [doubleCutRegionDomain]

@[simp] theorem domain_target
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature) :
    (doubleCutRegionDomain input outer trace.inner).survives trace.target =
      true := by
  have targetNeOuter : trace.target ≠ outer :=
    fun equality => trace.outer_ne_target wellFormed equality.symm
  have targetNeInner : trace.target ≠ trace.inner :=
    fun equality => trace.inner_ne_target wellFormed equality.symm
  simp [doubleCutRegionDomain, targetNeOuter, targetNeInner]

def targetIndex
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature) :
    Fin (doubleCutRegionDomain input outer trace.inner).count :=
  (doubleCutRegionDomain input outer trace.inner).index trace.target
    (trace.domain_target wellFormed)

@[simp] theorem targetIndex_origin
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature) :
    (doubleCutRegionDomain input outer trace.inner).origin
        (trace.targetIndex wellFormed) =
      trace.target := by
  exact SurvivorDomain.origin_index _ _ _

def regionMap
    (trace : DoubleCutElimTrace input outer raw) :
    Fin raw.regionCount → Fin input.regionCount :=
  fun region =>
    (doubleCutRegionDomain input outer trace.inner).origin
      (Fin.cast trace.promotion.raw_regionCount region)

def nodeMap
    (trace : DoubleCutElimTrace input outer raw) :
    Fin raw.nodeCount → Fin input.nodeCount :=
  Fin.cast trace.promotion.raw_nodeCount

def wireMap
    (trace : DoubleCutElimTrace input outer raw) :
    Fin raw.wireCount → Fin input.wireCount :=
  Fin.cast trace.promotion.raw_wireCount

theorem regionMap_root
    (trace : DoubleCutElimTrace input outer raw) :
    trace.regionMap raw.root = input.root := by
  unfold regionMap
  have rootCast :
      Fin.cast trace.promotion.raw_regionCount raw.root =
        trace.promotion.root := by
    apply Fin.ext
    exact congrArg (fun diagram : ConcreteDiagram => diagram.root.val)
      trace.promotion.raw_eq
  rw [rootCast]
  exact trace.promotion.root_origin

@[simp] theorem nodeMap_val
    (trace : DoubleCutElimTrace input outer raw)
    (node : Fin raw.nodeCount) :
    (trace.nodeMap node).val = node.val := rfl

@[simp] theorem wireMap_val
    (trace : DoubleCutElimTrace input outer raw)
    (wire : Fin raw.wireCount) :
    (trace.wireMap wire).val = wire.val := rfl

private theorem mappedOwner_eq_targetIndex_iff
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (owner : Fin input.regionCount)
    (mapped :
      Fin (doubleCutRegionDomain input outer trace.inner).count)
    (result :
      (doubleCutRegionDomain input outer trace.inner).index?
          (if owner = trace.inner then trace.target else owner) =
        some mapped) :
    mapped = trace.targetIndex wellFormed ↔
      owner = trace.target ∨ owner = trace.inner := by
  let domain := doubleCutRegionDomain input outer trace.inner
  have mappedOrigin :
      domain.origin mapped =
        (if owner = trace.inner then trace.target else owner) :=
    (domain.index?_eq_some_iff _ _).1 result
  constructor
  · intro equality
    by_cases ownerInner : owner = trace.inner
    · exact Or.inr ownerInner
    · left
      rw [if_neg ownerInner, equality] at mappedOrigin
      exact mappedOrigin.symm.trans (trace.targetIndex_origin wellFormed)
  · rintro (ownerTarget | ownerInner)
    · apply domain.origin_injective
      rw [trace.targetIndex_origin]
      simpa [domain, ownerTarget, trace.inner_ne_target wellFormed] using
        mappedOrigin
    · apply domain.origin_injective
      rw [trace.targetIndex_origin]
      simpa [domain, ownerInner] using mappedOrigin

private theorem mappedOwner_eq_region_iff
    (trace : DoubleCutElimTrace input outer raw)
    (owner : Fin input.regionCount)
    (mapped region :
      Fin (doubleCutRegionDomain input outer trace.inner).count)
    (result :
      (doubleCutRegionDomain input outer trace.inner).index?
          (if owner = trace.inner then trace.target else owner) =
        some mapped) :
    mapped = region ↔
      (if owner = trace.inner then trace.target else owner) =
        (doubleCutRegionDomain input outer trace.inner).origin region := by
  let domain := doubleCutRegionDomain input outer trace.inner
  have mappedOrigin :
      domain.origin mapped =
        (if owner = trace.inner then trace.target else owner) :=
    (domain.index?_eq_some_iff _ _).1 result
  constructor
  · intro equality
    exact mappedOrigin.symm.trans (congrArg domain.origin equality)
  · intro equality
    apply domain.origin_injective
    exact mappedOrigin.trans equality

private theorem chosenOwner_eq_origin_regular_iff
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (owner : Fin input.regionCount)
    (region :
      Fin (doubleCutRegionDomain input outer trace.inner).count)
    (regular : region ≠ trace.targetIndex wellFormed) :
    (if owner = trace.inner then trace.target else owner) =
        (doubleCutRegionDomain input outer trace.inner).origin region ↔
      owner =
        (doubleCutRegionDomain input outer trace.inner).origin region := by
  by_cases innerOwner : owner = trace.inner
  · rw [if_pos innerOwner]
    constructor
    · intro targetOrigin
      exfalso
      apply regular
      apply (doubleCutRegionDomain input outer trace.inner).origin_injective
      rw [trace.targetIndex_origin]
      exact targetOrigin.symm
    · intro ownerOrigin
      exfalso
      have survives :=
        (doubleCutRegionDomain input outer trace.inner).origin_survives region
      have originNeInner :
          (doubleCutRegionDomain input outer trace.inner).origin region ≠
            trace.inner := by
        have distinct :
            (doubleCutRegionDomain input outer trace.inner).origin region ≠
                outer ∧
              (doubleCutRegionDomain input outer trace.inner).origin region ≠
                trace.inner := by
          simpa [doubleCutRegionDomain] using survives
        exact distinct.2
      exact originNeInner (ownerOrigin.symm.trans innerOwner)
  · simp [innerOwner]

theorem promotedNode_region_eq_targetIndex_iff
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (node : Fin input.nodeCount) :
    (trace.promotion.nodes node).region = trace.targetIndex wellFormed ↔
      (input.nodes node).region = trace.target ∨
        (input.nodes node).region = trace.inner := by
  have result := trace.promotion.node_result node
  cases nodeShape : input.nodes node with
  | term owner freePorts term =>
      rw [nodeShape] at result
      simp only [promoteNode?] at result
      rw [Option.map_eq_some_iff] at result
      obtain ⟨mapped, mappedResult, nodeResult⟩ := result
      change (trace.promotion.nodes node).region =
          trace.targetIndex wellFormed ↔
        owner = trace.target ∨ owner = trace.inner
      have regionResult := congrArg CNode.region nodeResult
      rw [← regionResult]
      exact mappedOwner_eq_targetIndex_iff trace wellFormed owner mapped
        mappedResult
  | atom owner binder =>
      rw [nodeShape] at result
      simp only [promoteNode?] at result
      change ((doubleCutRegionDomain input outer trace.inner).index?
          (if owner = trace.inner then trace.target else owner)).bind
          (fun mappedOwner =>
            ((doubleCutRegionDomain input outer trace.inner).index?
              binder).bind
              (fun mappedBinder =>
                some (.atom mappedOwner mappedBinder))) =
        some (trace.promotion.nodes node) at result
      rw [Option.bind_eq_some_iff] at result
      obtain ⟨mappedOwner, ownerResult, result⟩ := result
      rw [Option.bind_eq_some_iff] at result
      obtain ⟨mappedBinder, binderResult, nodeResult⟩ := result
      change (trace.promotion.nodes node).region =
          trace.targetIndex wellFormed ↔
        owner = trace.target ∨ owner = trace.inner
      have regionResult := congrArg CNode.region (Option.some.inj nodeResult)
      rw [← regionResult]
      exact mappedOwner_eq_targetIndex_iff trace wellFormed owner mappedOwner
        ownerResult
  | named owner definition arity =>
      rw [nodeShape] at result
      simp only [promoteNode?] at result
      rw [Option.map_eq_some_iff] at result
      obtain ⟨mapped, mappedResult, nodeResult⟩ := result
      change (trace.promotion.nodes node).region =
          trace.targetIndex wellFormed ↔
        owner = trace.target ∨ owner = trace.inner
      have regionResult := congrArg CNode.region nodeResult
      rw [← regionResult]
      exact mappedOwner_eq_targetIndex_iff trace wellFormed owner mapped
        mappedResult

theorem promotedNode_region_eq_regular_iff
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (node : Fin input.nodeCount)
    (region :
      Fin (doubleCutRegionDomain input outer trace.inner).count)
    (regular : region ≠ trace.targetIndex wellFormed) :
    (trace.promotion.nodes node).region = region ↔
      (input.nodes node).region =
        (doubleCutRegionDomain input outer trace.inner).origin region := by
  have result := trace.promotion.node_result node
  cases nodeShape : input.nodes node with
  | term owner freePorts term =>
      rw [nodeShape] at result
      simp only [promoteNode?] at result
      rw [Option.map_eq_some_iff] at result
      obtain ⟨mapped, mappedResult, nodeResult⟩ := result
      change (trace.promotion.nodes node).region = region ↔
        owner =
          (doubleCutRegionDomain input outer trace.inner).origin region
      have regionResult := congrArg CNode.region nodeResult
      rw [← regionResult]
      exact (mappedOwner_eq_region_iff trace owner mapped region
        mappedResult).trans
          (trace.chosenOwner_eq_origin_regular_iff wellFormed owner region
            regular)
  | atom owner binder =>
      rw [nodeShape] at result
      simp only [promoteNode?] at result
      change ((doubleCutRegionDomain input outer trace.inner).index?
          (if owner = trace.inner then trace.target else owner)).bind
          (fun mappedOwner =>
            ((doubleCutRegionDomain input outer trace.inner).index?
              binder).bind
              (fun mappedBinder =>
                some (.atom mappedOwner mappedBinder))) =
        some (trace.promotion.nodes node) at result
      rw [Option.bind_eq_some_iff] at result
      obtain ⟨mappedOwner, ownerResult, result⟩ := result
      rw [Option.bind_eq_some_iff] at result
      obtain ⟨mappedBinder, binderResult, nodeResult⟩ := result
      change (trace.promotion.nodes node).region = region ↔
        owner =
          (doubleCutRegionDomain input outer trace.inner).origin region
      have regionResult := congrArg CNode.region (Option.some.inj nodeResult)
      rw [← regionResult]
      exact (mappedOwner_eq_region_iff trace owner mappedOwner region
        ownerResult).trans
          (trace.chosenOwner_eq_origin_regular_iff wellFormed owner region
            regular)
  | named owner definition arity =>
      rw [nodeShape] at result
      simp only [promoteNode?] at result
      rw [Option.map_eq_some_iff] at result
      obtain ⟨mapped, mappedResult, nodeResult⟩ := result
      change (trace.promotion.nodes node).region = region ↔
        owner =
          (doubleCutRegionDomain input outer trace.inner).origin region
      have regionResult := congrArg CNode.region nodeResult
      rw [← regionResult]
      exact (mappedOwner_eq_region_iff trace owner mapped region
        mappedResult).trans
          (trace.chosenOwner_eq_origin_regular_iff wellFormed owner region
            regular)

theorem regular_nodeShape
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (region :
      Fin (doubleCutRegionDomain input outer trace.inner).count)
    (regular : region ≠ trace.targetIndex wellFormed)
    (node : Fin input.nodeCount)
    (nodeRegion : (trace.promotion.nodes node).region = region) :
    input.nodes node =
      match trace.promotion.nodes node with
      | .term owner freePorts term =>
          .term
            ((doubleCutRegionDomain input outer trace.inner).origin owner)
            freePorts term
      | .atom owner binder =>
          .atom
            ((doubleCutRegionDomain input outer trace.inner).origin owner)
            ((doubleCutRegionDomain input outer trace.inner).origin binder)
      | .named owner definition arity =>
          .named
            ((doubleCutRegionDomain input outer trace.inner).origin owner)
            definition arity := by
  have result := trace.promotion.node_result node
  have ownerEq :=
    (trace.promotedNode_region_eq_regular_iff
      wellFormed node region regular).1 nodeRegion
  cases originalShape : input.nodes node with
  | term owner freePorts term =>
      rw [originalShape] at result ownerEq
      simp only [CNode.region, promoteNode?] at result ownerEq
      rw [Option.map_eq_some_iff] at result
      obtain ⟨mapped, mappedResult, nodeResult⟩ := result
      have mappedEq : mapped = region :=
        (congrArg CNode.region nodeResult).trans nodeRegion
      rw [← nodeResult]
      simp [originalShape, ownerEq, mappedEq]
  | atom owner binder =>
      rw [originalShape] at result ownerEq
      simp only [CNode.region, promoteNode?] at result ownerEq
      change ((doubleCutRegionDomain input outer trace.inner).index?
          (if owner = trace.inner then trace.target else owner)).bind
          (fun mappedOwner =>
            ((doubleCutRegionDomain input outer trace.inner).index?
              binder).bind
              (fun mappedBinder => some (.atom mappedOwner mappedBinder))) =
        some (trace.promotion.nodes node) at result
      rw [Option.bind_eq_some_iff] at result
      obtain ⟨mappedOwner, ownerResult, result⟩ := result
      rw [Option.bind_eq_some_iff] at result
      obtain ⟨mappedBinder, binderResult, nodeResult⟩ := result
      have mappedOwnerEq : mappedOwner = region :=
        (congrArg CNode.region (Option.some.inj nodeResult)).trans nodeRegion
      have binderEq :
          (doubleCutRegionDomain input outer trace.inner).origin mappedBinder =
            binder :=
        ((doubleCutRegionDomain input outer trace.inner).index?_eq_some_iff
          binder mappedBinder).1 binderResult
      rw [← Option.some.inj nodeResult]
      simp [ownerEq, mappedOwnerEq, binderEq.symm]
  | named owner definition arity =>
      rw [originalShape] at result ownerEq
      simp only [CNode.region, promoteNode?] at result ownerEq
      rw [Option.map_eq_some_iff] at result
      obtain ⟨mapped, mappedResult, nodeResult⟩ := result
      have mappedEq : mapped = region :=
        (congrArg CNode.region nodeResult).trans nodeRegion
      rw [← nodeResult]
      simp [originalShape, ownerEq, mappedEq]

theorem focused_nodeShape
    (trace : DoubleCutElimTrace input outer raw)
    (node : Fin input.nodeCount) (owner : Fin input.regionCount)
    (ownerEq : (input.nodes node).region = owner) :
    input.nodes node =
      match trace.promotion.nodes node with
      | .term _ freePorts term => .term owner freePorts term
      | .atom _ binder =>
          .atom owner
            ((doubleCutRegionDomain input outer trace.inner).origin binder)
      | .named _ definition arity => .named owner definition arity := by
  have result := trace.promotion.node_result node
  cases originalShape : input.nodes node with
  | term originalOwner freePorts term =>
      rw [originalShape] at result ownerEq
      simp only [CNode.region, promoteNode?] at result ownerEq
      rw [Option.map_eq_some_iff] at result
      obtain ⟨mapped, mappedResult, nodeResult⟩ := result
      rw [← nodeResult]
      simp [ownerEq]
  | atom originalOwner binder =>
      rw [originalShape] at result ownerEq
      simp only [CNode.region, promoteNode?] at result ownerEq
      change ((doubleCutRegionDomain input outer trace.inner).index?
          (if originalOwner = trace.inner then trace.target else
            originalOwner)).bind
          (fun mappedOwner =>
            ((doubleCutRegionDomain input outer trace.inner).index?
              binder).bind
              (fun mappedBinder => some (.atom mappedOwner mappedBinder))) =
        some (trace.promotion.nodes node) at result
      rw [Option.bind_eq_some_iff] at result
      obtain ⟨mappedOwner, ownerResult, result⟩ := result
      rw [Option.bind_eq_some_iff] at result
      obtain ⟨mappedBinder, binderResult, nodeResult⟩ := result
      have binderEq :
          (doubleCutRegionDomain input outer trace.inner).origin mappedBinder =
            binder :=
        ((doubleCutRegionDomain input outer trace.inner).index?_eq_some_iff
          binder mappedBinder).1 binderResult
      rw [← Option.some.inj nodeResult]
      simp [ownerEq, binderEq.symm]
  | named originalOwner definition arity =>
      rw [originalShape] at result ownerEq
      simp only [CNode.region, promoteNode?] at result ownerEq
      rw [Option.map_eq_some_iff] at result
      obtain ⟨mapped, mappedResult, nodeResult⟩ := result
      rw [← nodeResult]
      simp [ownerEq]

theorem promotedWire_scope_eq_targetIndex_iff
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (wire : Fin input.wireCount) :
    (trace.promotion.wires wire).scope = trace.targetIndex wellFormed ↔
      (input.wires wire).scope = trace.target ∨
        (input.wires wire).scope = trace.inner := by
  have result := trace.promotion.wire_result wire
  unfold promoteWire? at result
  change ((doubleCutRegionDomain input outer trace.inner).index?
      (if (input.wires wire).scope = trace.inner then
        trace.target
      else (input.wires wire).scope)).bind
        (fun mapped =>
          some {
            scope := mapped
            endpoints := (input.wires wire).endpoints
          }) =
    some (trace.promotion.wires wire) at result
  rw [Option.bind_eq_some_iff] at result
  obtain ⟨mapped, mappedResult, wireResult⟩ := result
  change (trace.promotion.wires wire).scope =
      trace.targetIndex wellFormed ↔
    (input.wires wire).scope = trace.target ∨
      (input.wires wire).scope = trace.inner
  have scopeResult := congrArg CWire.scope (Option.some.inj wireResult)
  rw [← scopeResult]
  exact mappedOwner_eq_targetIndex_iff trace wellFormed
    (input.wires wire).scope mapped mappedResult

theorem promotedWire_scope_eq_regular_iff
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (wire : Fin input.wireCount)
    (region :
      Fin (doubleCutRegionDomain input outer trace.inner).count)
    (regular : region ≠ trace.targetIndex wellFormed) :
    (trace.promotion.wires wire).scope = region ↔
      (input.wires wire).scope =
        (doubleCutRegionDomain input outer trace.inner).origin region := by
  have result := trace.promotion.wire_result wire
  unfold promoteWire? at result
  change ((doubleCutRegionDomain input outer trace.inner).index?
      (if (input.wires wire).scope = trace.inner then
        trace.target
      else (input.wires wire).scope)).bind
        (fun mapped =>
          some {
            scope := mapped
            endpoints := (input.wires wire).endpoints
          }) =
    some (trace.promotion.wires wire) at result
  rw [Option.bind_eq_some_iff] at result
  obtain ⟨mapped, mappedResult, wireResult⟩ := result
  have scopeResult := congrArg CWire.scope (Option.some.inj wireResult)
  rw [← scopeResult]
  rw [mappedOwner_eq_region_iff trace (input.wires wire).scope mapped
    region mappedResult]
  by_cases innerScope : (input.wires wire).scope = trace.inner
  · rw [if_pos innerScope]
    constructor
    · intro targetOrigin
      exfalso
      apply regular
      apply (doubleCutRegionDomain input outer trace.inner).origin_injective
      rw [trace.targetIndex_origin]
      exact targetOrigin.symm
    · intro scopeOrigin
      exfalso
      have originNeInner :
          (doubleCutRegionDomain input outer trace.inner).origin region ≠
            trace.inner := by
        have survives :=
          (doubleCutRegionDomain input outer trace.inner).origin_survives region
        have distinct :
            (doubleCutRegionDomain input outer trace.inner).origin region ≠
                outer ∧
              (doubleCutRegionDomain input outer trace.inner).origin region ≠
                trace.inner := by
          simpa [doubleCutRegionDomain] using survives
        exact distinct.2
      exact originNeInner (scopeOrigin.symm.trans innerScope)
  · simp [innerScope]

theorem regular_exactScopeWires
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (region :
      Fin (doubleCutRegionDomain input outer trace.inner).count)
    (regular : region ≠ trace.targetIndex wellFormed) :
    ConcreteElaboration.exactScopeWires trace.promotion.diagram region =
      ConcreteElaboration.exactScopeWires input
        ((doubleCutRegionDomain input outer trace.inner).origin region) := by
  unfold ConcreteElaboration.exactScopeWires filterFin
    PromoteDiagramTrace.diagram
  apply congrArg
    (fun predicate => List.filter predicate (allFin input.wireCount))
  funext wire
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact trace.promotedWire_scope_eq_regular_iff wellFormed wire region regular

theorem promotedWire_endpoints
    (trace : DoubleCutElimTrace input outer raw)
    (wire : Fin input.wireCount) :
    (trace.promotion.wires wire).endpoints =
      (input.wires wire).endpoints := by
  have result := trace.promotion.wire_result wire
  unfold promoteWire? at result
  change ((doubleCutRegionDomain input outer trace.inner).index?
      (if (input.wires wire).scope = trace.inner then
        trace.target
      else (input.wires wire).scope)).bind
        (fun mapped =>
          some {
            scope := mapped
            endpoints := (input.wires wire).endpoints
          }) =
    some (trace.promotion.wires wire) at result
  rw [Option.bind_eq_some_iff] at result
  obtain ⟨mapped, mappedResult, wireResult⟩ := result
  have equality := Option.some.inj wireResult
  exact (congrArg CWire.endpoints equality).symm

theorem promotedRegion_parent_eq_targetIndex_iff
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (region :
      Fin (doubleCutRegionDomain input outer trace.inner).count) :
    (trace.promotion.regions region).parent? =
        some (trace.targetIndex wellFormed) ↔
      (input.regions
          ((doubleCutRegionDomain input outer trace.inner).origin region)).parent? =
          some trace.target ∨
        (input.regions
          ((doubleCutRegionDomain input outer trace.inner).origin region)).parent? =
          some trace.inner := by
  have result := trace.promotion.region_result region
  cases regionShape :
      input.regions
        ((doubleCutRegionDomain input outer trace.inner).origin region) with
  | sheet =>
      rw [regionShape] at result
      simp only [promoteRegion?] at result
      have regionResult := Option.some.inj result
      simp only [CRegion.parent?] at ⊢
      rw [← regionResult]
      simp
  | cut parent =>
      rw [regionShape] at result
      simp only [promoteRegion?] at result
      have normalized :
          (if parent = trace.inner then
              Option.map CRegion.cut
                ((doubleCutRegionDomain input outer trace.inner).index?
                  trace.target)
            else
              Option.map CRegion.cut
                ((doubleCutRegionDomain input outer trace.inner).index?
                  parent)) =
            Option.map CRegion.cut
              ((doubleCutRegionDomain input outer trace.inner).index?
                (if parent = trace.inner then trace.target else parent)) := by
        by_cases parentInner : parent = trace.inner <;> simp [parentInner]
      rw [normalized] at result
      rw [Option.map_eq_some_iff] at result
      obtain ⟨mapped, mappedResult, regionResult⟩ := result
      change (trace.promotion.regions region).parent? =
          some (trace.targetIndex wellFormed) ↔
        some parent = some trace.target ∨ some parent = some trace.inner
      have parentResult := congrArg CRegion.parent? regionResult
      rw [← parentResult]
      simp only [CRegion.parent?, Option.some.injEq]
      have mappedChoice :
          (doubleCutRegionDomain input outer trace.inner).index?
              (if parent = trace.inner then trace.target else parent) =
            some mapped := mappedResult
      exact mappedOwner_eq_targetIndex_iff trace wellFormed parent mapped
        mappedChoice
  | bubble parent arity =>
      rw [regionShape] at result
      simp only [promoteRegion?] at result
      have normalized :
          (if parent = trace.inner then
              Option.map (fun mapped => CRegion.bubble mapped arity)
                ((doubleCutRegionDomain input outer trace.inner).index?
                  trace.target)
            else
              Option.map (fun mapped => CRegion.bubble mapped arity)
                ((doubleCutRegionDomain input outer trace.inner).index?
                  parent)) =
            Option.map (fun mapped => CRegion.bubble mapped arity)
              ((doubleCutRegionDomain input outer trace.inner).index?
                (if parent = trace.inner then trace.target else parent)) := by
        by_cases parentInner : parent = trace.inner <;> simp [parentInner]
      rw [normalized] at result
      rw [Option.map_eq_some_iff] at result
      obtain ⟨mapped, mappedResult, regionResult⟩ := result
      change (trace.promotion.regions region).parent? =
          some (trace.targetIndex wellFormed) ↔
        some parent = some trace.target ∨ some parent = some trace.inner
      have parentResult := congrArg CRegion.parent? regionResult
      rw [← parentResult]
      simp only [CRegion.parent?, Option.some.injEq]
      have mappedChoice :
          (doubleCutRegionDomain input outer trace.inner).index?
              (if parent = trace.inner then trace.target else parent) =
            some mapped := mappedResult
      exact mappedOwner_eq_targetIndex_iff trace wellFormed parent mapped
        mappedChoice

theorem promotedRegion_parent_eq_regular_iff
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (child region :
      Fin (doubleCutRegionDomain input outer trace.inner).count)
    (regular : region ≠ trace.targetIndex wellFormed) :
    (trace.promotion.regions child).parent? = some region ↔
      (input.regions
          ((doubleCutRegionDomain input outer trace.inner).origin child)).parent? =
        some ((doubleCutRegionDomain input outer trace.inner).origin region) := by
  have result := trace.promotion.region_result child
  cases regionShape :
      input.regions
        ((doubleCutRegionDomain input outer trace.inner).origin child) with
  | sheet =>
      rw [regionShape] at result
      simp only [promoteRegion?] at result
      have regionResult := Option.some.inj result
      simp only [CRegion.parent?] at ⊢
      rw [← regionResult]
      simp
  | cut parent =>
      rw [regionShape] at result
      simp only [promoteRegion?] at result
      have normalized :
          (if parent = trace.inner then
              Option.map CRegion.cut
                ((doubleCutRegionDomain input outer trace.inner).index?
                  trace.target)
            else
              Option.map CRegion.cut
                ((doubleCutRegionDomain input outer trace.inner).index?
                  parent)) =
            Option.map CRegion.cut
              ((doubleCutRegionDomain input outer trace.inner).index?
                (if parent = trace.inner then trace.target else parent)) := by
        by_cases parentInner : parent = trace.inner <;> simp [parentInner]
      rw [normalized] at result
      rw [Option.map_eq_some_iff] at result
      obtain ⟨mapped, mappedResult, regionResult⟩ := result
      change (trace.promotion.regions child).parent? = some region ↔
        some parent = some
          ((doubleCutRegionDomain input outer trace.inner).origin region)
      have parentResult := congrArg CRegion.parent? regionResult
      rw [← parentResult]
      simp only [CRegion.parent?, Option.some.injEq]
      exact (mappedOwner_eq_region_iff trace parent mapped region
        mappedResult).trans
          (trace.chosenOwner_eq_origin_regular_iff wellFormed parent region
            regular)
  | bubble parent arity =>
      rw [regionShape] at result
      simp only [promoteRegion?] at result
      have normalized :
          (if parent = trace.inner then
              Option.map (fun mapped => CRegion.bubble mapped arity)
                ((doubleCutRegionDomain input outer trace.inner).index?
                  trace.target)
            else
              Option.map (fun mapped => CRegion.bubble mapped arity)
                ((doubleCutRegionDomain input outer trace.inner).index?
                  parent)) =
            Option.map (fun mapped => CRegion.bubble mapped arity)
              ((doubleCutRegionDomain input outer trace.inner).index?
                (if parent = trace.inner then trace.target else parent)) := by
        by_cases parentInner : parent = trace.inner <;> simp [parentInner]
      rw [normalized] at result
      rw [Option.map_eq_some_iff] at result
      obtain ⟨mapped, mappedResult, regionResult⟩ := result
      change (trace.promotion.regions child).parent? = some region ↔
        some parent = some
          ((doubleCutRegionDomain input outer trace.inner).origin region)
      have parentResult := congrArg CRegion.parent? regionResult
      rw [← parentResult]
      simp only [CRegion.parent?, Option.some.injEq]
      exact (mappedOwner_eq_region_iff trace parent mapped region
        mappedResult).trans
          (trace.chosenOwner_eq_origin_regular_iff wellFormed parent region
            regular)

theorem regular_regionShape
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (parent :
      Fin (doubleCutRegionDomain input outer trace.inner).count)
    (regular : parent ≠ trace.targetIndex wellFormed)
    (child : Fin (doubleCutRegionDomain input outer trace.inner).count)
    (childParent :
      (trace.promotion.regions child).parent? = some parent) :
    input.regions
        ((doubleCutRegionDomain input outer trace.inner).origin child) =
      match trace.promotion.regions child with
      | .sheet => .sheet
      | .cut _ =>
          .cut ((doubleCutRegionDomain input outer trace.inner).origin parent)
      | .bubble _ arity =>
          .bubble
            ((doubleCutRegionDomain input outer trace.inner).origin parent)
            arity := by
  have targetParent :=
    (trace.promotedRegion_parent_eq_regular_iff
      wellFormed child parent regular).1 childParent
  have result := trace.promotion.region_result child
  cases originalShape : input.regions
      ((doubleCutRegionDomain input outer trace.inner).origin child) with
  | sheet =>
      rw [originalShape] at targetParent
      simp [CRegion.parent?] at targetParent
  | cut originalParent =>
      have originalParentEq :
          originalParent =
            (doubleCutRegionDomain input outer trace.inner).origin parent := by
        rw [originalShape] at targetParent
        exact Option.some.inj targetParent
      rw [originalShape] at result
      simp only [promoteRegion?] at result
      have normalized :
          (if originalParent = trace.inner then
              Option.map CRegion.cut
                ((doubleCutRegionDomain input outer trace.inner).index?
                  trace.target)
            else
              Option.map CRegion.cut
                ((doubleCutRegionDomain input outer trace.inner).index?
                  originalParent)) =
            Option.map CRegion.cut
              ((doubleCutRegionDomain input outer trace.inner).index?
                (if originalParent = trace.inner then
                  trace.target else originalParent)) := by
        by_cases parentInner : originalParent = trace.inner <;>
          simp [parentInner]
      rw [normalized, Option.map_eq_some_iff] at result
      obtain ⟨mapped, mappedResult, regionResult⟩ := result
      rw [← regionResult]
      simp [originalParentEq]
  | bubble originalParent arity =>
      have originalParentEq :
          originalParent =
            (doubleCutRegionDomain input outer trace.inner).origin parent := by
        rw [originalShape] at targetParent
        exact Option.some.inj targetParent
      rw [originalShape] at result
      simp only [promoteRegion?] at result
      have normalized :
          (if originalParent = trace.inner then
              Option.map (fun mapped => CRegion.bubble mapped arity)
                ((doubleCutRegionDomain input outer trace.inner).index?
                  trace.target)
            else
              Option.map (fun mapped => CRegion.bubble mapped arity)
                ((doubleCutRegionDomain input outer trace.inner).index?
                  originalParent)) =
            Option.map (fun mapped => CRegion.bubble mapped arity)
              ((doubleCutRegionDomain input outer trace.inner).index?
                (if originalParent = trace.inner then
                  trace.target else originalParent)) := by
        by_cases parentInner : originalParent = trace.inner <;>
          simp [parentInner]
      rw [normalized, Option.map_eq_some_iff] at result
      obtain ⟨mapped, mappedResult, regionResult⟩ := result
      rw [← regionResult]
      simp [originalParentEq]

theorem focused_regionShape
    (trace : DoubleCutElimTrace input outer raw)
    (child : Fin (doubleCutRegionDomain input outer trace.inner).count)
    (parent : Fin input.regionCount)
    (parentEq :
      (input.regions
        ((doubleCutRegionDomain input outer trace.inner).origin child)).parent? =
          some parent) :
    input.regions
        ((doubleCutRegionDomain input outer trace.inner).origin child) =
      match trace.promotion.regions child with
      | .sheet => .sheet
      | .cut _ => .cut parent
      | .bubble _ arity => .bubble parent arity := by
  have result := trace.promotion.region_result child
  cases originalShape : input.regions
      ((doubleCutRegionDomain input outer trace.inner).origin child) with
  | sheet =>
      rw [originalShape] at parentEq
      simp [CRegion.parent?] at parentEq
  | cut originalParent =>
      have originalParentEq : originalParent = parent := by
        rw [originalShape] at parentEq
        exact Option.some.inj parentEq
      rw [originalShape] at result
      simp only [promoteRegion?] at result
      have normalized :
          (if originalParent = trace.inner then
              Option.map CRegion.cut
                ((doubleCutRegionDomain input outer trace.inner).index?
                  trace.target)
            else
              Option.map CRegion.cut
                ((doubleCutRegionDomain input outer trace.inner).index?
                  originalParent)) =
            Option.map CRegion.cut
              ((doubleCutRegionDomain input outer trace.inner).index?
                (if originalParent = trace.inner then
                  trace.target else originalParent)) := by
        by_cases parentInner : originalParent = trace.inner <;>
          simp [parentInner]
      rw [normalized, Option.map_eq_some_iff] at result
      obtain ⟨mapped, mappedResult, regionResult⟩ := result
      rw [← regionResult]
      simp [originalParentEq]
  | bubble originalParent arity =>
      have originalParentEq : originalParent = parent := by
        rw [originalShape] at parentEq
        exact Option.some.inj parentEq
      rw [originalShape] at result
      simp only [promoteRegion?] at result
      have normalized :
          (if originalParent = trace.inner then
              Option.map (fun mapped => CRegion.bubble mapped arity)
                ((doubleCutRegionDomain input outer trace.inner).index?
                  trace.target)
            else
              Option.map (fun mapped => CRegion.bubble mapped arity)
                ((doubleCutRegionDomain input outer trace.inner).index?
                  originalParent)) =
            Option.map (fun mapped => CRegion.bubble mapped arity)
              ((doubleCutRegionDomain input outer trace.inner).index?
                (if originalParent = trace.inner then
                  trace.target else originalParent)) := by
        by_cases parentInner : originalParent = trace.inner <;>
          simp [parentInner]
      rw [normalized, Option.map_eq_some_iff] at result
      obtain ⟨mapped, mappedResult, regionResult⟩ := result
      rw [← regionResult]
      simp [originalParentEq]

abbrev sourceDiagram
    (trace : DoubleCutElimTrace input outer raw) : ConcreteDiagram :=
  trace.promotion.diagram

def origin
    (trace : DoubleCutElimTrace input outer raw) :
    Fin trace.sourceDiagram.regionCount → Fin input.regionCount :=
  (doubleCutRegionDomain input outer trace.inner).origin

theorem origin_injective
    (trace : DoubleCutElimTrace input outer raw) :
    Function.Injective trace.origin :=
  (doubleCutRegionDomain input outer trace.inner).origin_injective

def occurrenceMap
    (trace : DoubleCutElimTrace input outer raw) :
    ConcreteElaboration.LocalOccurrence
        trace.sourceDiagram.regionCount trace.sourceDiagram.nodeCount →
      ConcreteElaboration.LocalOccurrence input.regionCount input.nodeCount
  | .node node => .node node
  | .child child =>
      .child
        ((doubleCutRegionDomain input outer trace.inner).origin child)

def wireIdentityRelation
    (trace : DoubleCutElimTrace input outer raw)
    (sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input) :
    ConcreteElaboration.ContextIndexRelation
      sourceContext.length targetContext.length where
  Rel sourceIndex targetIndex :=
    sourceContext.get sourceIndex = targetContext.get targetIndex

structure PromotedBinderWitness
    (trace : DoubleCutElimTrace input outer raw)
    {sourceRels targetRels : RelCtx}
    (sourceBinders : ConcreteElaboration.BinderContext
      trace.sourceDiagram sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext input targetRels) : Type
    where
  relationContexts_eq : sourceRels = targetRels
  binders_eq : ∀ region,
    HEq (sourceBinders region)
      (targetBinders (trace.origin region))

namespace PromotedBinderWitness

def relationMap
    (witness : PromotedBinderWitness trace
      (sourceRels := sourceRels) (targetRels := targetRels)
      sourceBinders targetBinders) :
    RelationRenaming sourceRels targetRels := by
  cases witness.relationContexts_eq
  exact ConcreteElaboration.identityRelationRenaming sourceRels

def push
    {input : ConcreteDiagram} {outer : Fin input.regionCount}
    {raw : ConcreteDiagram}
    {trace : DoubleCutElimTrace input outer raw}
    {sourceRels targetRels : RelCtx}
    {sourceBinders : ConcreteElaboration.BinderContext
      trace.sourceDiagram sourceRels}
    {targetBinders : ConcreteElaboration.BinderContext input targetRels}
    (witness : PromotedBinderWitness trace sourceBinders targetBinders)
    (child parent : Fin trace.sourceDiagram.regionCount) (arity : Nat) :
    PromotedBinderWitness trace
      (sourceBinders.push child arity)
      (targetBinders.push (trace.origin child) arity) := by
  refine ⟨congrArg (List.cons arity) witness.relationContexts_eq, ?_⟩
  intro region
  cases witness.relationContexts_eq
  simp only [ConcreteElaboration.BinderContext.push]
  by_cases equality : region = child
  · subst region
    simp
  · have originNe :
        trace.origin region ≠ trace.origin child := by
      exact fun originEq => equality (trace.origin_injective originEq)
    rw [if_neg equality, if_neg originNe]
    apply heq_of_eq
    rw [eq_of_heq (witness.binders_eq region)]

theorem relationMap_push
    {input : ConcreteDiagram} {outer : Fin input.regionCount}
    {raw : ConcreteDiagram}
    {trace : DoubleCutElimTrace input outer raw}
    {sourceRels targetRels : RelCtx}
    {sourceBinders : ConcreteElaboration.BinderContext
      trace.sourceDiagram sourceRels}
    {targetBinders : ConcreteElaboration.BinderContext input targetRels}
    (witness : PromotedBinderWitness trace
      (sourceRels := sourceRels) (targetRels := targetRels)
      sourceBinders targetBinders)
    (child parent : Fin trace.sourceDiagram.regionCount) (arity : Nat) :
    (relationMap (push witness child parent arity) :
        RelationRenaming (arity :: sourceRels) (arity :: targetRels)) =
      (RelationRenaming.lift (relationMap witness) arity :
        RelationRenaming (arity :: sourceRels) (arity :: targetRels)) := by
  cases witness.relationContexts_eq
  simpa [relationMap, ConcreteElaboration.identityRelationRenaming] using
    (RelationRenaming.lift_id_fun (source := sourceRels) arity).symm

end PromotedBinderWitness

structure PromotedContextWitness
    (trace : DoubleCutElimTrace input outer raw)
    (sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input) : Prop where
  target_subset_source : ∀ wire, wire ∈ targetContext → wire ∈ sourceContext
  source_subset_target_or_inner : ∀ wire, wire ∈ sourceContext →
    wire ∈ targetContext ∨
      wire ∈ ConcreteElaboration.exactScopeWires input trace.inner

namespace PromotedContextWitness

def indexRelation
    (witness : PromotedContextWitness trace sourceContext targetContext) :
    ConcreteElaboration.ContextIndexRelation
      sourceContext.length targetContext.length :=
  trace.wireIdentityRelation sourceContext targetContext

def extendRegular
    {input : ConcreteDiagram} {outer : Fin input.regionCount}
    {raw : ConcreteDiagram}
    {trace : DoubleCutElimTrace input outer raw}
    {sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram}
    {targetContext : ConcreteElaboration.WireContext input}
    (witness : PromotedContextWitness trace sourceContext targetContext)
    (wellFormed : input.WellFormed signature)
    (region : Fin trace.sourceDiagram.regionCount)
    (regular : region ≠ trace.targetIndex wellFormed) :
    PromotedContextWitness trace
      (sourceContext.extend region)
      (targetContext.extend (trace.origin region)) := by
  refine ⟨?_, ?_⟩
  · intro wire member
    rcases List.mem_append.mp member with outerMember | localMember
    · exact List.mem_append_left _
        (witness.target_subset_source wire outerMember)
    · apply List.mem_append_right sourceContext
      rw [trace.regular_exactScopeWires wellFormed region regular]
      exact localMember
  · intro wire member
    rcases List.mem_append.mp member with outerMember | localMember
    · rcases witness.source_subset_target_or_inner wire outerMember with
        targetMember | innerMember
      · exact Or.inl (List.mem_append_left _ targetMember)
      · exact Or.inr innerMember
    · exact Or.inl (List.mem_append_right targetContext (by
        change wire ∈ ConcreteElaboration.exactScopeWires input
          ((doubleCutRegionDomain input outer trace.inner).origin region)
        rw [← trace.regular_exactScopeWires wellFormed region regular]
        exact localMember))

noncomputable def sourceIndex
    (witness : PromotedContextWitness trace sourceContext targetContext)
    (targetIndex : Fin targetContext.length) : Fin sourceContext.length :=
  Classical.choose (ConcreteElaboration.WireContext.lookup?_complete
    (witness.target_subset_source (targetContext.get targetIndex)
      (List.get_mem targetContext targetIndex)))

theorem sourceIndex_lookup
    (witness : PromotedContextWitness trace sourceContext targetContext)
    (targetIndex : Fin targetContext.length) :
    sourceContext.lookup? (targetContext.get targetIndex) =
      some (witness.sourceIndex targetIndex) :=
  Classical.choose_spec (ConcreteElaboration.WireContext.lookup?_complete
    (witness.target_subset_source (targetContext.get targetIndex)
      (List.get_mem targetContext targetIndex)))

theorem sourceIndex_get
    (witness : PromotedContextWitness trace sourceContext targetContext)
    (targetIndex : Fin targetContext.length) :
    sourceContext.get (witness.sourceIndex targetIndex) =
      targetContext.get targetIndex :=
  ConcreteElaboration.WireContext.lookup?_sound
    (witness.sourceIndex_lookup targetIndex)

noncomputable def targetEnvironment
    (witness : PromotedContextWitness trace sourceContext targetContext)
    (sourceEnvironment : Fin sourceContext.length → D) :
    Fin targetContext.length → D :=
  fun targetIndex => sourceEnvironment (witness.sourceIndex targetIndex)

theorem targetEnvironment_agrees
    (witness : PromotedContextWitness trace sourceContext targetContext)
    (sourceNodup : sourceContext.Nodup)
    (sourceEnvironment : Fin sourceContext.length → D) :
    witness.indexRelation.EnvironmentsAgree sourceEnvironment
      (witness.targetEnvironment sourceEnvironment) := by
  intro sourceIndex targetIndex related
  have sourceIndexEq :=
    ConcreteElaboration.WireContext.lookup?_unique sourceNodup
      (witness.sourceIndex_lookup targetIndex) related
  subst sourceIndex
  rfl

noncomputable def targetIndex
    (witness : PromotedContextWitness trace sourceContext targetContext)
    (sourceSubset : ∀ wire, wire ∈ sourceContext → wire ∈ targetContext)
    (sourceIndex : Fin sourceContext.length) : Fin targetContext.length :=
  Classical.choose (ConcreteElaboration.WireContext.lookup?_complete
    (sourceSubset (sourceContext.get sourceIndex)
      (List.get_mem sourceContext sourceIndex)))

theorem targetIndex_lookup
    (witness : PromotedContextWitness trace sourceContext targetContext)
    (sourceSubset : ∀ wire, wire ∈ sourceContext → wire ∈ targetContext)
    (sourceIndex : Fin sourceContext.length) :
    targetContext.lookup? (sourceContext.get sourceIndex) =
      some (witness.targetIndex sourceSubset sourceIndex) :=
  Classical.choose_spec (ConcreteElaboration.WireContext.lookup?_complete
    (sourceSubset (sourceContext.get sourceIndex)
      (List.get_mem sourceContext sourceIndex)))

theorem targetIndex_get
    (witness : PromotedContextWitness trace sourceContext targetContext)
    (sourceSubset : ∀ wire, wire ∈ sourceContext → wire ∈ targetContext)
    (sourceIndex : Fin sourceContext.length) :
    targetContext.get (witness.targetIndex sourceSubset sourceIndex) =
      sourceContext.get sourceIndex :=
  ConcreteElaboration.WireContext.lookup?_sound
    (witness.targetIndex_lookup sourceSubset sourceIndex)

noncomputable def sourceEnvironment
    (witness : PromotedContextWitness trace sourceContext targetContext)
    (sourceSubset : ∀ wire, wire ∈ sourceContext → wire ∈ targetContext)
    (targetEnvironment : Fin targetContext.length → D) :
    Fin sourceContext.length → D :=
  fun sourceIndex => targetEnvironment
    (witness.targetIndex sourceSubset sourceIndex)

theorem sourceEnvironment_agrees
    (witness : PromotedContextWitness trace sourceContext targetContext)
    (sourceSubset : ∀ wire, wire ∈ sourceContext → wire ∈ targetContext)
    (targetNodup : targetContext.Nodup)
    (targetEnvironment : Fin targetContext.length → D) :
    witness.indexRelation.EnvironmentsAgree
      (witness.sourceEnvironment sourceSubset targetEnvironment)
      targetEnvironment := by
  intro sourceIndex targetIndex related
  have targetIndexEq :=
    ConcreteElaboration.WireContext.lookup?_unique targetNodup
      (witness.targetIndex_lookup sourceSubset sourceIndex) related.symm
  subst targetIndex
  rfl

end PromotedContextWitness

private theorem promoted_endpointOccurs
    (trace : DoubleCutElimTrace input outer raw)
    (wire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount) :
  trace.sourceDiagram.EndpointOccurs wire endpoint ↔
      input.EndpointOccurs wire endpoint := by
  simp only [ConcreteDiagram.EndpointOccurs]
  change endpoint ∈ (trace.promotion.wires wire).endpoints ↔
    endpoint ∈ (input.wires wire).endpoints
  rw [trace.promotedWire_endpoints wire]

theorem resolvedPorts_related
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input)
    (node : Fin input.nodeCount) (port : CPort)
    (sourceIndex : Fin sourceContext.length)
    (targetIndex : Fin targetContext.length)
    (sourceResolved :
      ConcreteElaboration.resolvePort? trace.sourceDiagram sourceContext
        node port = some sourceIndex)
    (targetResolved :
      ConcreteElaboration.resolvePort? input targetContext node port =
        some targetIndex) :
    (trace.wireIdentityRelation sourceContext targetContext).Rel
      sourceIndex targetIndex := by
  obtain ⟨sourceWire, sourceOccurs, sourceGet⟩ :=
    ConcreteElaboration.resolvePort?_sound sourceResolved
  obtain ⟨targetWire, targetOccurs, targetGet⟩ :=
    ConcreteElaboration.resolvePort?_sound targetResolved
  have sourceOccursInput :
      input.EndpointOccurs sourceWire ⟨node, port⟩ :=
    (trace.promoted_endpointOccurs sourceWire ⟨node, port⟩).1 sourceOccurs
  have wireEq : sourceWire = targetWire :=
    ConcreteElaboration.endpoint_wire_unique
      wellFormed.wire_endpoints_are_disjoint sourceOccursInput targetOccurs
  exact sourceGet.trans (wireEq.trans targetGet.symm)

def occurrenceSelected
    (trace : DoubleCutElimTrace input outer raw) :
    ConcreteElaboration.LocalOccurrence
        trace.sourceDiagram.regionCount trace.sourceDiagram.nodeCount →
      Bool
  | .node node =>
      decide ((input.nodes node).region = trace.inner)
  | .child child =>
      decide ((input.regions
        ((doubleCutRegionDomain input outer trace.inner).origin child)).parent? =
          some trace.inner)

@[simp] theorem occurrenceMap_map_nodes
    (trace : DoubleCutElimTrace input outer raw)
    (nodes : List (Fin input.nodeCount)) :
    (nodes.map ConcreteElaboration.LocalOccurrence.node).map
        trace.occurrenceMap =
      nodes.map ConcreteElaboration.LocalOccurrence.node := by
  induction nodes with
  | nil => rfl
  | cons node rest induction =>
      change ConcreteElaboration.LocalOccurrence.node node ::
          (rest.map ConcreteElaboration.LocalOccurrence.node).map
            trace.occurrenceMap =
        ConcreteElaboration.LocalOccurrence.node node ::
          rest.map ConcreteElaboration.LocalOccurrence.node
      rw [induction]

@[simp] theorem occurrenceMap_map_children
    (trace : DoubleCutElimTrace input outer raw)
    (children :
      List (Fin (doubleCutRegionDomain input outer trace.inner).count)) :
    (children.map ConcreteElaboration.LocalOccurrence.child).map
        trace.occurrenceMap =
      children.map (ConcreteElaboration.LocalOccurrence.child ∘
        (doubleCutRegionDomain input outer trace.inner).origin) := by
  induction children with
  | nil => rfl
  | cons child rest induction =>
      change ConcreteElaboration.LocalOccurrence.child
            ((doubleCutRegionDomain input outer trace.inner).origin child) ::
          (rest.map ConcreteElaboration.LocalOccurrence.child).map
            trace.occurrenceMap =
        ConcreteElaboration.LocalOccurrence.child
            ((doubleCutRegionDomain input outer trace.inner).origin child) ::
          rest.map (ConcreteElaboration.LocalOccurrence.child ∘
            (doubleCutRegionDomain input outer trace.inner).origin)
      rw [induction]

def selectedOccurrences
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature) :
    List (ConcreteElaboration.LocalOccurrence
      trace.sourceDiagram.regionCount trace.sourceDiagram.nodeCount) :=
  (ConcreteElaboration.localOccurrences trace.sourceDiagram
      (trace.targetIndex wellFormed)).filter trace.occurrenceSelected

def keptOccurrences
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature) :
    List (ConcreteElaboration.LocalOccurrence
      trace.sourceDiagram.regionCount trace.sourceDiagram.nodeCount) :=
  (ConcreteElaboration.localOccurrences trace.sourceDiagram
      (trace.targetIndex wellFormed)).filter
        (fun occurrence => !trace.occurrenceSelected occurrence)

theorem kept_node_region
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (node : Fin input.nodeCount)
    (member : ConcreteElaboration.LocalOccurrence.node node ∈
      trace.keptOccurrences wellFormed) :
    (input.nodes node).region = trace.target := by
  have filtered := List.mem_filter.mp member
  have atFocus :=
    (ConcreteElaboration.mem_localOccurrences_node trace.sourceDiagram
      (trace.targetIndex wellFormed) node).mp filtered.1
  have notInner : (input.nodes node).region ≠ trace.inner := by
    simpa [occurrenceSelected] using filtered.2
  rcases (trace.promotedNode_region_eq_targetIndex_iff
    wellFormed node).1 atFocus with atTarget | atInner
  · exact atTarget
  · exact False.elim (notInner atInner)

theorem selected_node_region
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (node : Fin input.nodeCount)
    (member : ConcreteElaboration.LocalOccurrence.node node ∈
      trace.selectedOccurrences wellFormed) :
    (input.nodes node).region = trace.inner := by
  exact of_decide_eq_true (List.mem_filter.mp member).2

theorem kept_child_parent
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (child : Fin trace.sourceDiagram.regionCount)
    (member : ConcreteElaboration.LocalOccurrence.child child ∈
      trace.keptOccurrences wellFormed) :
    (input.regions (trace.origin child)).parent? = some trace.target := by
  have filtered := List.mem_filter.mp member
  have atFocus :=
    (ConcreteElaboration.mem_localOccurrences_child trace.sourceDiagram
      (trace.targetIndex wellFormed) child).mp filtered.1
  have notInner :
      (input.regions (trace.origin child)).parent? ≠ some trace.inner := by
    simpa [occurrenceSelected, origin] using filtered.2
  rcases (trace.promotedRegion_parent_eq_targetIndex_iff
    wellFormed child).1 atFocus with atTarget | atInner
  · simpa [origin] using atTarget
  · exact False.elim (notInner (by simpa [origin] using atInner))

theorem selected_child_parent
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (child : Fin trace.sourceDiagram.regionCount)
    (member : ConcreteElaboration.LocalOccurrence.child child ∈
      trace.selectedOccurrences wellFormed) :
    (input.regions (trace.origin child)).parent? = some trace.inner := by
  simpa [occurrenceSelected, origin] using
    (of_decide_eq_true (List.mem_filter.mp member).2)

theorem focusOccurrences_perm_partition
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature) :
    List.Perm
      (trace.keptOccurrences wellFormed ++
        trace.selectedOccurrences wellFormed)
      (ConcreteElaboration.localOccurrences trace.sourceDiagram
        (trace.targetIndex wellFormed)) := by
  simpa only [keptOccurrences, selectedOccurrences, Bool.not_not] using
    (List.filter_append_perm
      (fun occurrence => !trace.occurrenceSelected occurrence)
      (ConcreteElaboration.localOccurrences trace.sourceDiagram
        (trace.targetIndex wellFormed)))

def targetKeptOccurrences
    (trace : DoubleCutElimTrace input outer raw) :
    List (ConcreteElaboration.LocalOccurrence input.regionCount
      input.nodeCount) :=
  (ConcreteElaboration.localOccurrences input trace.target).filter
    (fun occurrence => decide
      (occurrence ≠ ConcreteElaboration.LocalOccurrence.child outer))

private def canonicalSelectedOccurrences
    (trace : DoubleCutElimTrace input outer raw) :
    List (ConcreteElaboration.LocalOccurrence
      trace.sourceDiagram.regionCount trace.sourceDiagram.nodeCount) :=
  (filterFin fun node =>
      decide ((input.nodes node).region = trace.inner)).map
        ConcreteElaboration.LocalOccurrence.node ++
    (filterFin fun child =>
      decide ((input.regions
        ((doubleCutRegionDomain input outer trace.inner).origin child)).parent? =
          some trace.inner)).map
        ConcreteElaboration.LocalOccurrence.child

private def canonicalKeptOccurrences
    (trace : DoubleCutElimTrace input outer raw) :
    List (ConcreteElaboration.LocalOccurrence
      trace.sourceDiagram.regionCount trace.sourceDiagram.nodeCount) :=
  (filterFin fun node =>
      decide ((input.nodes node).region = trace.target)).map
        ConcreteElaboration.LocalOccurrence.node ++
    (filterFin fun child =>
      decide ((input.regions
        ((doubleCutRegionDomain input outer trace.inner).origin child)).parent? =
          some trace.target)).map
        ConcreteElaboration.LocalOccurrence.child

private def canonicalTargetKeptOccurrences
    (trace : DoubleCutElimTrace input outer raw) :
    List (ConcreteElaboration.LocalOccurrence input.regionCount
      input.nodeCount) :=
  (filterFin fun node =>
      decide ((input.nodes node).region = trace.target)).map
        ConcreteElaboration.LocalOccurrence.node ++
    (filterFin fun child =>
      decide ((input.regions child).parent? = some trace.target ∧
        child ≠ outer)).map
        ConcreteElaboration.LocalOccurrence.child

private theorem selectedOccurrences_eq_canonical
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature) :
    trace.selectedOccurrences wellFormed =
      trace.canonicalSelectedOccurrences := by
  unfold selectedOccurrences canonicalSelectedOccurrences
    ConcreteElaboration.localOccurrences occurrenceSelected filterFin
    sourceDiagram PromoteDiagramTrace.diagram
  simp only [List.filter_append, List.filter_map, List.filter_filter]
  congr 1
  · apply congrArg
      (List.map ConcreteElaboration.LocalOccurrence.node)
    apply congrArg
      (fun predicate => List.filter predicate (allFin input.nodeCount))
    funext node
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · exact And.left
    · intro inner
      exact ⟨
        inner,
        (trace.promotedNode_region_eq_targetIndex_iff
          wellFormed node).2 (Or.inr inner)⟩
  · apply congrArg
      (List.map ConcreteElaboration.LocalOccurrence.child)
    apply congrArg
      (fun predicate =>
        List.filter predicate
          (allFin
            (doubleCutRegionDomain input outer trace.inner).count))
    funext child
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · exact And.left
    · intro inner
      exact ⟨
        inner,
        (trace.promotedRegion_parent_eq_targetIndex_iff
          wellFormed child).2 (Or.inr inner)⟩

private theorem keptOccurrences_eq_canonical
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature) :
    trace.keptOccurrences wellFormed = trace.canonicalKeptOccurrences := by
  unfold keptOccurrences canonicalKeptOccurrences
    ConcreteElaboration.localOccurrences occurrenceSelected filterFin
    sourceDiagram PromoteDiagramTrace.diagram
  simp only [List.filter_append, List.filter_map, List.filter_filter]
  congr 1
  · apply congrArg
      (List.map ConcreteElaboration.LocalOccurrence.node)
    apply congrArg
      (fun predicate => List.filter predicate (allFin input.nodeCount))
    funext node
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨notInnerBool, atFocus⟩
      have notInner : (input.nodes node).region ≠ trace.inner := by
        simpa using notInnerBool
      rcases (trace.promotedNode_region_eq_targetIndex_iff
        wellFormed node).1 atFocus with atTarget | atInner
      · exact atTarget
      · exact False.elim (notInner atInner)
    · intro atTarget
      have notInner : (input.nodes node).region ≠ trace.inner := by
        intro atInner
        exact trace.inner_ne_target wellFormed (atInner.symm.trans atTarget)
      refine ⟨by simpa using notInner,
        (trace.promotedNode_region_eq_targetIndex_iff
          wellFormed node).2 (Or.inl atTarget)⟩
  · apply congrArg
      (List.map ConcreteElaboration.LocalOccurrence.child)
    apply congrArg
      (fun predicate => List.filter predicate
        (allFin (doubleCutRegionDomain input outer trace.inner).count))
    funext child
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨notInnerBool, atFocus⟩
      have notInner :
          (input.regions
            ((doubleCutRegionDomain input outer trace.inner).origin child)).parent? ≠
            some trace.inner := by
        simpa using notInnerBool
      rcases (trace.promotedRegion_parent_eq_targetIndex_iff
        wellFormed child).1 atFocus with atTarget | atInner
      · exact atTarget
      · exact False.elim (notInner atInner)
    · intro atTarget
      have notInner :
          (input.regions
            ((doubleCutRegionDomain input outer trace.inner).origin child)).parent? ≠
            some trace.inner := by
        intro atInner
        exact trace.inner_ne_target wellFormed
          (Option.some.inj (atInner.symm.trans atTarget))
      refine ⟨by simpa using notInner,
        (trace.promotedRegion_parent_eq_targetIndex_iff
          wellFormed child).2 (Or.inl atTarget)⟩

private theorem targetKeptOccurrences_eq_canonical
    (trace : DoubleCutElimTrace input outer raw) :
    trace.targetKeptOccurrences = trace.canonicalTargetKeptOccurrences := by
  unfold targetKeptOccurrences canonicalTargetKeptOccurrences
    ConcreteElaboration.localOccurrences filterFin
  simp only [List.filter_append, List.filter_map, List.filter_filter]
  congr 1
  apply congrArg
    (List.map ConcreteElaboration.LocalOccurrence.child)
  apply congrArg
    (fun predicate => List.filter predicate (allFin input.regionCount))
  funext child
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨different, parent⟩
    exact ⟨parent, fun equality => different (congrArg
      ConcreteElaboration.LocalOccurrence.child equality)⟩
  · rintro ⟨parent, different⟩
    exact ⟨fun equality => different
      (ConcreteElaboration.LocalOccurrence.child.inj equality), parent⟩

private theorem allFin_map_domain_origin
    (trace : DoubleCutElimTrace input outer raw) :
    (allFin (doubleCutRegionDomain input outer trace.inner).count).map
        (doubleCutRegionDomain input outer trace.inner).origin =
      (doubleCutRegionDomain input outer trace.inner).enumeration := by
  rw [allFin_eq_finRange, List.finRange, List.map_ofFn]
  change List.ofFn (fun index =>
    (doubleCutRegionDomain input outer trace.inner).enumeration.get index) =
      (doubleCutRegionDomain input outer trace.inner).enumeration
  exact List.ofFn_getElem

theorem child_of_inner_survives
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (child : Fin input.regionCount)
    (parentEq : (input.regions child).parent? = some trace.inner) :
    (doubleCutRegionDomain input outer trace.inner).survives child = true := by
  have childNeOuter : child ≠ outer := by
    intro equality
    subst child
    have targetEq : trace.target = trace.inner := by
      exact Option.some.inj (trace.outer_parent.symm.trans parentEq)
    exact trace.inner_ne_target wellFormed targetEq.symm
  have childNeInner : child ≠ trace.inner := by
    intro equality
    apply ConcreteElaboration.checked_direct_child_not_encloses_parent
      wellFormed parentEq
    rw [equality]
    exact ConcreteDiagram.Encloses.refl input trace.inner
  simp [doubleCutRegionDomain, childNeOuter, childNeInner]

theorem child_of_regular_survives
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (region :
      Fin (doubleCutRegionDomain input outer trace.inner).count)
    (regular : region ≠ trace.targetIndex wellFormed)
    (child : Fin input.regionCount)
    (parentEq :
      (input.regions child).parent? =
        some ((doubleCutRegionDomain input outer trace.inner).origin region)) :
    (doubleCutRegionDomain input outer trace.inner).survives child = true := by
  have childNeOuter : child ≠ outer := by
    intro equality
    subst child
    have targetOrigin :
        trace.target =
          (doubleCutRegionDomain input outer trace.inner).origin region :=
      Option.some.inj (trace.outer_parent.symm.trans parentEq)
    apply regular
    apply (doubleCutRegionDomain input outer trace.inner).origin_injective
    rw [trace.targetIndex_origin]
    exact targetOrigin.symm
  have childNeInner : child ≠ trace.inner := by
    intro equality
    subst child
    have outerOrigin :
        outer =
          (doubleCutRegionDomain input outer trace.inner).origin region :=
      Option.some.inj (trace.inner_parent.symm.trans parentEq)
    have survives :=
      (doubleCutRegionDomain input outer trace.inner).origin_survives region
    have originNeOuter :
        (doubleCutRegionDomain input outer trace.inner).origin region ≠ outer := by
      have distinct :
          (doubleCutRegionDomain input outer trace.inner).origin region ≠ outer ∧
            (doubleCutRegionDomain input outer trace.inner).origin region ≠
              trace.inner := by
        simpa [doubleCutRegionDomain] using survives
      exact distinct.1
    exact originNeOuter outerOrigin.symm
  simp [doubleCutRegionDomain, childNeOuter, childNeInner]

theorem child_of_target_ne_outer_survives
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (child : Fin input.regionCount)
    (parentEq : (input.regions child).parent? = some trace.target)
    (childNeOuter : child ≠ outer) :
    (doubleCutRegionDomain input outer trace.inner).survives child = true := by
  have childNeInner : child ≠ trace.inner := by
    intro equality
    subst child
    have outerTarget : outer = trace.target :=
      Option.some.inj (trace.inner_parent.symm.trans parentEq)
    exact trace.outer_ne_target wellFormed outerTarget
  simp [doubleCutRegionDomain, childNeOuter, childNeInner]

theorem targetKeptOccurrences_eq_mapped
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature) :
    trace.targetKeptOccurrences =
      (trace.keptOccurrences wellFormed).map trace.occurrenceMap := by
  rw [trace.targetKeptOccurrences_eq_canonical,
    trace.keptOccurrences_eq_canonical wellFormed]
  unfold canonicalTargetKeptOccurrences canonicalKeptOccurrences filterFin
  change
    (List.filter (fun node =>
        decide ((input.nodes node).region = trace.target))
        (allFin input.nodeCount)).map
          ConcreteElaboration.LocalOccurrence.node ++
      (List.filter (fun child =>
        decide ((input.regions child).parent? = some trace.target ∧
          child ≠ outer))
        (allFin input.regionCount)).map
          ConcreteElaboration.LocalOccurrence.child =
    (((List.filter (fun node =>
        decide ((input.nodes node).region = trace.target))
        (allFin input.nodeCount)).map
          (ConcreteElaboration.LocalOccurrence.node
            (regions :=
              (doubleCutRegionDomain input outer trace.inner).count))) ++
      ((List.filter (fun child =>
        decide ((input.regions
          ((doubleCutRegionDomain input outer trace.inner).origin child)).parent? =
            some trace.target))
        (allFin
          (doubleCutRegionDomain input outer trace.inner).count)).map
          (ConcreteElaboration.LocalOccurrence.child
            (nodes := input.nodeCount)))).map
      trace.occurrenceMap
  dsimp only [sourceDiagram, PromoteDiagramTrace.diagram] at *
  rw [List.map_append]
  simp only [List.map_map, occurrenceMap, Function.comp_apply]
  congr 1
  change
    List.map ConcreteElaboration.LocalOccurrence.child
        (List.filter (fun child => decide
          ((input.regions child).parent? = some trace.target ∧
            child ≠ outer))
          (allFin input.regionCount)) =
      List.map
        (ConcreteElaboration.LocalOccurrence.child ∘
          (doubleCutRegionDomain input outer trace.inner).origin)
        (List.filter (fun child => decide
          ((input.regions
            ((doubleCutRegionDomain input outer trace.inner).origin child)).parent? =
              some trace.target))
          (allFin
            (doubleCutRegionDomain input outer trace.inner).count))
  rw [← List.map_map]
  apply congrArg
    (List.map ConcreteElaboration.LocalOccurrence.child)
  change
    List.filter (fun child => decide
      ((input.regions child).parent? = some trace.target ∧ child ≠ outer))
        (allFin input.regionCount) =
      List.map (doubleCutRegionDomain input outer trace.inner).origin
        (List.filter
          ((fun child => decide
            ((input.regions child).parent? = some trace.target)) ∘
            (doubleCutRegionDomain input outer trace.inner).origin)
          (allFin
            (doubleCutRegionDomain input outer trace.inner).count))
  rw [← List.filter_map]
  rw [trace.allFin_map_domain_origin]
  unfold SurvivorDomain.enumeration filterFin
  rw [List.filter_filter]
  apply congrArg
    (fun predicate => List.filter predicate (allFin input.regionCount))
  funext child
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨parentEq, childNeOuter⟩
    exact ⟨parentEq, trace.child_of_target_ne_outer_survives wellFormed child
      parentEq childNeOuter⟩
  · rintro ⟨parentEq, survives⟩
    have distinct : child ≠ outer ∧ child ≠ trace.inner := by
      simpa [doubleCutRegionDomain] using survives
    exact ⟨parentEq, distinct.1⟩

theorem targetOuterComplement
    (trace : DoubleCutElimTrace input outer raw) :
    (ConcreteElaboration.localOccurrences input trace.target).filter
        (fun occurrence =>
          !decide (occurrence ≠
            ConcreteElaboration.LocalOccurrence.child outer)) =
      [ConcreteElaboration.LocalOccurrence.child outer] := by
  let occurrences :=
    ConcreteElaboration.localOccurrences input trace.target
  let chosen : ConcreteElaboration.LocalOccurrence
      input.regionCount input.nodeCount :=
    .child outer
  apply eq_singleton_of_nodup_mem_unique
  · exact (ConcreteElaboration.localOccurrences_nodup input trace.target).filter _
  · apply List.mem_filter.mpr
    refine ⟨?_, by simp [chosen]⟩
    exact (ConcreteElaboration.mem_localOccurrences_child input trace.target
      outer).mpr trace.outer_parent
  · intro occurrence member
    have selected := (List.mem_filter.mp member).2
    simpa [chosen] using selected

theorem targetFocusOccurrences_perm
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature) :
    List.Perm
      ((trace.keptOccurrences wellFormed).map trace.occurrenceMap ++
        [ConcreteElaboration.LocalOccurrence.child outer])
      (ConcreteElaboration.localOccurrences input trace.target) := by
  have partition := List.filter_append_perm
    (fun occurrence : ConcreteElaboration.LocalOccurrence
      input.regionCount input.nodeCount =>
      decide (occurrence ≠ ConcreteElaboration.LocalOccurrence.child outer))
    (ConcreteElaboration.localOccurrences input trace.target)
  change List.Perm
    (trace.targetKeptOccurrences ++
      (ConcreteElaboration.localOccurrences input trace.target).filter
        (fun occurrence =>
          !decide (occurrence ≠
            ConcreteElaboration.LocalOccurrence.child outer)))
    (ConcreteElaboration.localOccurrences input trace.target) at partition
  rw [trace.targetKeptOccurrences_eq_mapped wellFormed,
    trace.targetOuterComplement] at partition
  exact partition

theorem outer_localOccurrences
    (trace : DoubleCutElimTrace input outer raw) :
    ConcreteElaboration.localOccurrences input outer =
      [ConcreteElaboration.LocalOccurrence.child trace.inner] := by
  have nodesEmpty :
      (filterFin fun node =>
        decide ((input.nodes node).region = outer)) = [] :=
    List.isEmpty_iff.mp trace.outer_nodes_empty
  unfold ConcreteElaboration.localOccurrences
  rw [nodesEmpty, trace.children_eq]
  rfl

theorem outer_exactScopeWires
    (trace : DoubleCutElimTrace input outer raw) :
    ConcreteElaboration.exactScopeWires input outer = [] := by
  exact List.isEmpty_iff.mp trace.outer_wires_empty

theorem targetWire_mem_focusExact
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (wire : Fin input.wireCount)
    (member : wire ∈
      ConcreteElaboration.exactScopeWires input trace.target) :
    wire ∈ ConcreteElaboration.exactScopeWires trace.sourceDiagram
      (trace.targetIndex wellFormed) := by
  rw [ConcreteElaboration.mem_exactScopeWires] at member
  unfold ConcreteElaboration.exactScopeWires
  change wire ∈ filterFin (fun candidate : Fin input.wireCount =>
    decide ((trace.promotion.wires candidate).scope =
      trace.targetIndex wellFormed))
  rw [mem_filterFin]
  exact decide_eq_true ((trace.promotedWire_scope_eq_targetIndex_iff
    wellFormed wire).2 (Or.inl member))

theorem innerWire_mem_focusExact
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (wire : Fin input.wireCount)
    (member : wire ∈
      ConcreteElaboration.exactScopeWires input trace.inner) :
    wire ∈ ConcreteElaboration.exactScopeWires trace.sourceDiagram
      (trace.targetIndex wellFormed) := by
  rw [ConcreteElaboration.mem_exactScopeWires] at member
  unfold ConcreteElaboration.exactScopeWires
  change wire ∈ filterFin (fun candidate : Fin input.wireCount =>
    decide ((trace.promotion.wires candidate).scope =
      trace.targetIndex wellFormed))
  rw [mem_filterFin]
  exact decide_eq_true ((trace.promotedWire_scope_eq_targetIndex_iff
    wellFormed wire).2 (Or.inr member))

def PromotedContextWitness.extendFocused
    {input : ConcreteDiagram} {outer : Fin input.regionCount}
    {raw : ConcreteDiagram}
    {trace : DoubleCutElimTrace input outer raw}
    {sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram}
    {targetContext : ConcreteElaboration.WireContext input}
    (witness : PromotedContextWitness trace sourceContext targetContext)
    (wellFormed : input.WellFormed signature) :
    PromotedContextWitness trace
      (sourceContext.extend (trace.targetIndex wellFormed))
      (targetContext.extend trace.target) := by
  refine ⟨?_, ?_⟩
  · intro wire member
    rcases List.mem_append.mp member with outerMember | localMember
    · exact List.mem_append_left _
        (witness.target_subset_source wire outerMember)
    · exact List.mem_append_right sourceContext
        (trace.targetWire_mem_focusExact wellFormed wire localMember)
  · intro wire member
    rcases List.mem_append.mp member with outerMember | localMember
    · rcases witness.source_subset_target_or_inner wire outerMember with
        targetMember | innerMember
      · exact Or.inl (List.mem_append_left _ targetMember)
      · exact Or.inr innerMember
    · rw [ConcreteElaboration.mem_exactScopeWires] at localMember
      rcases (trace.promotedWire_scope_eq_targetIndex_iff
        wellFormed wire).1 localMember with targetScope | innerScope
      · exact Or.inl (List.mem_append_right targetContext (by
          rw [ConcreteElaboration.mem_exactScopeWires]
          exact targetScope))
      · exact Or.inr (by
          exact (ConcreteElaboration.mem_exactScopeWires input trace.inner
            wire).2 innerScope)

def PromotedContextWitness.extendSelected
    {input : ConcreteDiagram} {outer : Fin input.regionCount}
    {raw : ConcreteDiagram}
    {trace : DoubleCutElimTrace input outer raw}
    {sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram}
    {targetContext : ConcreteElaboration.WireContext input}
    (witness : PromotedContextWitness trace sourceContext targetContext)
    (wellFormed : input.WellFormed signature) :
    PromotedContextWitness trace
      (sourceContext.extend (trace.targetIndex wellFormed))
      (((targetContext.extend trace.target).extend outer).extend trace.inner) := by
  refine ⟨?_, ?_⟩
  · intro wire member
    rcases List.mem_append.mp member with beforeInner | innerLocal
    · rcases List.mem_append.mp beforeInner with beforeOuter | outerLocal
      · rcases List.mem_append.mp beforeOuter with base | targetLocal
        · exact List.mem_append_left _
            (witness.target_subset_source wire base)
        · exact List.mem_append_right sourceContext
            (trace.targetWire_mem_focusExact wellFormed wire targetLocal)
      · rw [trace.outer_exactScopeWires] at outerLocal
        exact False.elim (List.not_mem_nil outerLocal)
    · exact List.mem_append_right sourceContext
        (trace.innerWire_mem_focusExact wellFormed wire innerLocal)
  · intro wire member
    rcases List.mem_append.mp member with base | focusLocal
    · rcases witness.source_subset_target_or_inner wire base with
        targetMember | innerMember
      · exact Or.inl (List.mem_append_left _
          (List.mem_append_left _ (List.mem_append_left _ targetMember)))
      · exact Or.inl (List.mem_append_right _ innerMember)
    · rw [ConcreteElaboration.mem_exactScopeWires] at focusLocal
      rcases (trace.promotedWire_scope_eq_targetIndex_iff
        wellFormed wire).1 focusLocal with targetScope | innerScope
      · exact Or.inl (List.mem_append_left _
          (List.mem_append_left _ (List.mem_append_right targetContext (by
            rw [ConcreteElaboration.mem_exactScopeWires]
            exact targetScope))))
      · exact Or.inl (List.mem_append_right _ (by
          exact (ConcreteElaboration.mem_exactScopeWires input trace.inner
            wire).2 innerScope))

theorem PromotedContextWitness.extendSelected_source_subset_target
    {input : ConcreteDiagram} {outer : Fin input.regionCount}
    {raw : ConcreteDiagram}
    {trace : DoubleCutElimTrace input outer raw}
    {sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram}
    {targetContext : ConcreteElaboration.WireContext input}
    (witness : PromotedContextWitness trace sourceContext targetContext)
    (wellFormed : input.WellFormed signature) :
    ∀ wire,
      wire ∈ sourceContext.extend (trace.targetIndex wellFormed) →
      wire ∈ (((targetContext.extend trace.target).extend outer).extend
        trace.inner) := by
  intro wire member
  let extended := witness.extendSelected wellFormed
  rcases extended.source_subset_target_or_inner wire member with
    targetMember | innerMember
  · exact targetMember
  · exact List.mem_append_right _ innerMember

theorem inner_localOccurrences
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature) :
    ConcreteElaboration.localOccurrences input trace.inner =
      (trace.selectedOccurrences wellFormed).map trace.occurrenceMap := by
  rw [trace.selectedOccurrences_eq_canonical wellFormed]
  unfold canonicalSelectedOccurrences
    ConcreteElaboration.localOccurrences filterFin
  change
    (List.filter (fun node =>
        decide ((input.nodes node).region = trace.inner))
        (allFin input.nodeCount)).map
          ConcreteElaboration.LocalOccurrence.node ++
      (List.filter (fun child =>
        decide ((input.regions child).parent? = some trace.inner))
        (allFin input.regionCount)).map
          ConcreteElaboration.LocalOccurrence.child =
    (((List.filter (fun node =>
        decide ((input.nodes node).region = trace.inner))
        (allFin input.nodeCount)).map
          ConcreteElaboration.LocalOccurrence.node) ++
      ((List.filter (fun child =>
        decide ((input.regions
          ((doubleCutRegionDomain input outer trace.inner).origin child)).parent? =
            some trace.inner))
        (allFin
          (doubleCutRegionDomain input outer trace.inner).count)).map
            ConcreteElaboration.LocalOccurrence.child)).map
      trace.occurrenceMap
  have mappedAppend :
      (((List.filter (fun node =>
          decide ((input.nodes node).region = trace.inner))
          (allFin input.nodeCount)).map
            ConcreteElaboration.LocalOccurrence.node) ++
        ((List.filter (fun child =>
          decide ((input.regions
            ((doubleCutRegionDomain input outer trace.inner).origin child)).parent? =
              some trace.inner))
          (allFin
            (doubleCutRegionDomain input outer trace.inner).count)).map
              ConcreteElaboration.LocalOccurrence.child)).map
          trace.occurrenceMap =
        ((List.filter (fun node =>
          decide ((input.nodes node).region = trace.inner))
          (allFin input.nodeCount)).map
            ConcreteElaboration.LocalOccurrence.node).map
              trace.occurrenceMap ++
        ((List.filter (fun child =>
          decide ((input.regions
            ((doubleCutRegionDomain input outer trace.inner).origin child)).parent? =
              some trace.inner))
          (allFin
            (doubleCutRegionDomain input outer trace.inner).count)).map
              ConcreteElaboration.LocalOccurrence.child).map
                trace.occurrenceMap :=
    map_append_elimination trace.occurrenceMap _ _
  rw [mappedAppend, occurrenceMap_map_nodes,
    occurrenceMap_map_children]
  congr 1
  rw [← List.map_map]
  apply congrArg
    (List.map ConcreteElaboration.LocalOccurrence.child)
  change
    List.filter (fun child =>
      decide ((input.regions child).parent? = some trace.inner))
        (allFin input.regionCount) =
      List.map (doubleCutRegionDomain input outer trace.inner).origin
        (List.filter
          ((fun child =>
            decide ((input.regions child).parent? = some trace.inner)) ∘
              (doubleCutRegionDomain input outer trace.inner).origin)
          (allFin
            (doubleCutRegionDomain input outer trace.inner).count))
  rw [← List.filter_map]
  rw [trace.allFin_map_domain_origin]
  unfold SurvivorDomain.enumeration filterFin
  rw [List.filter_filter]
  apply congrArg
    (fun predicate => List.filter predicate (allFin input.regionCount))
  funext child
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro parentEq
    exact ⟨parentEq,
      trace.child_of_inner_survives wellFormed child parentEq⟩
  · exact And.left

theorem regular_localOccurrences
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (region :
      Fin (doubleCutRegionDomain input outer trace.inner).count)
    (regular : region ≠ trace.targetIndex wellFormed) :
    ConcreteElaboration.localOccurrences input
        ((doubleCutRegionDomain input outer trace.inner).origin region) =
      (ConcreteElaboration.localOccurrences trace.sourceDiagram region).map
        trace.occurrenceMap := by
  unfold ConcreteElaboration.localOccurrences filterFin
  rw [List.map_append]
  simp only [List.map_map, occurrenceMap, Function.comp_apply]
  congr 1
  · apply congrArg
      (List.map ConcreteElaboration.LocalOccurrence.node)
    apply congrArg
      (fun predicate => List.filter predicate (allFin input.nodeCount))
    funext node
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact (trace.promotedNode_region_eq_regular_iff
      wellFormed node region regular).symm
  · have sourceChildren :
        List.filter
            (fun child => decide
              ((trace.promotion.regions child).parent? = some region))
            (allFin
              (doubleCutRegionDomain input outer trace.inner).count) =
          List.filter
            ((fun child => decide
              ((input.regions child).parent? = some
                ((doubleCutRegionDomain input outer trace.inner).origin
                  region))) ∘
              (doubleCutRegionDomain input outer trace.inner).origin)
            (allFin
              (doubleCutRegionDomain input outer trace.inner).count) := by
      apply congrArg
        (fun predicate => List.filter predicate
          (allFin
            (doubleCutRegionDomain input outer trace.inner).count))
      funext child
      apply Bool.eq_iff_iff.mpr
      simp only [Function.comp_apply, decide_eq_true_eq]
      exact trace.promotedRegion_parent_eq_regular_iff
        wellFormed child region regular
    change
      List.map ConcreteElaboration.LocalOccurrence.child
          (List.filter (fun child => decide
            ((input.regions child).parent? = some
              ((doubleCutRegionDomain input outer trace.inner).origin region)))
            (allFin input.regionCount)) =
        List.map
          (ConcreteElaboration.LocalOccurrence.child ∘
            (doubleCutRegionDomain input outer trace.inner).origin)
          (List.filter
            (fun child => decide
              ((trace.promotion.regions child).parent? = some region))
            (allFin
              (doubleCutRegionDomain input outer trace.inner).count))
    rw [sourceChildren]
    rw [← List.map_map]
    apply congrArg
      (List.map ConcreteElaboration.LocalOccurrence.child)
    change
      List.filter (fun child => decide
        ((input.regions child).parent? = some
          ((doubleCutRegionDomain input outer trace.inner).origin region)))
          (allFin input.regionCount) =
        List.map (doubleCutRegionDomain input outer trace.inner).origin
          (List.filter
            ((fun child => decide
              ((input.regions child).parent? = some
                ((doubleCutRegionDomain input outer trace.inner).origin
                  region))) ∘
              (doubleCutRegionDomain input outer trace.inner).origin)
            (allFin
              (doubleCutRegionDomain input outer trace.inner).count))
    rw [← List.filter_map]
    rw [trace.allFin_map_domain_origin]
    unfold SurvivorDomain.enumeration filterFin
    rw [List.filter_filter]
    apply congrArg
      (fun predicate => List.filter predicate (allFin input.regionCount))
    funext child
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · intro parentEq
      exact ⟨parentEq,
        trace.child_of_regular_survives wellFormed region regular child
          parentEq⟩
    · exact And.left

theorem compileNode_itemSimulation
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input)
    (sourceBinders : ConcreteElaboration.BinderContext
      trace.sourceDiagram sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext input targetRels)
    (binderWitness : PromotedBinderWitness trace sourceBinders targetBinders)
    (node : Fin input.nodeCount)
    (regionMap :
      Fin (doubleCutRegionDomain input outer trace.inner).count →
        Fin input.regionCount)
    (nodeShape : input.nodes node =
      match trace.sourceDiagram.nodes node with
      | .term owner freePorts term =>
          .term (regionMap owner) freePorts term
      | .atom owner binder =>
          .atom (regionMap owner)
            ((doubleCutRegionDomain input outer trace.inner).origin binder)
      | .named owner definition arity =>
          .named (regionMap owner) definition arity)
    (sourceItem : Item signature sourceContext.length sourceRels)
    (targetItem : Item signature targetContext.length targetRels)
    (sourceCompiled :
      ConcreteElaboration.compileNode? signature trace.sourceDiagram
        sourceContext sourceBinders node = some sourceItem)
    (targetCompiled :
      ConcreteElaboration.compileNode? signature input targetContext
        targetBinders node = some targetItem) :
    ConcreteElaboration.ItemSimulation model named direction
      (trace.wireIdentityRelation sourceContext targetContext)
      (sourceItem.renameRelations binderWitness.relationMap) targetItem := by
  apply ConcreteElaboration.compileNode?_itemSimulation_of_related_ports
    (source := trace.sourceDiagram) (target := input)
    model named direction sourceContext targetContext
    (trace.wireIdentityRelation sourceContext targetContext)
    sourceBinders targetBinders binderWitness.relationMap node node
    regionMap (doubleCutRegionDomain input outer trace.inner).origin
  · cases sourceShape : trace.sourceDiagram.nodes node <;>
      simpa [sourceShape] using nodeShape
  · intro port sourceIndex targetIndex sourceResolved targetResolved
    exact trace.resolvedPorts_related wellFormed sourceContext targetContext
      node port sourceIndex targetIndex sourceResolved targetResolved
  · intro nodeOwner binder arity sourceRelation sourceAtom sourceLookup
    cases binderWitness.relationContexts_eq
    simpa [PromotedBinderWitness.relationMap] using
      (eq_of_heq (binderWitness.binders_eq binder)).symm.trans sourceLookup
  · exact sourceCompiled
  · exact targetCompiled

end DoubleCutElimTrace

end VisualProof.Rule
