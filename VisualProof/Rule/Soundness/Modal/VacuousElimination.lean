import VisualProof.Rule.Soundness.Modal.Elimination

namespace VisualProof.Rule.VacuousElimTrace

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram

private theorem map_append_vacuous
    (map : α → β) (first second : List α) :
    (first ++ second).map map = first.map map ++ second.map map := by
  induction first with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.cons_append, List.map_cons]
      rw [induction]

@[simp] theorem domain_bubble
    (trace : VacuousElimTrace input bubble raw) :
    (vacuousRegionDomain input bubble).survives bubble = false := by
  simp [vacuousRegionDomain]

@[simp] theorem domain_parent
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature) :
    (vacuousRegionDomain input bubble).survives trace.parent = true :=
  trace.parent_survives wellFormed

def targetIndex
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature) :
    Fin (vacuousRegionDomain input bubble).count :=
  (vacuousRegionDomain input bubble).index trace.parent
    (trace.domain_parent wellFormed)

@[simp] theorem targetIndex_origin
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature) :
    (vacuousRegionDomain input bubble).origin
        (trace.targetIndex wellFormed) = trace.parent := by
  exact SurvivorDomain.origin_index _ _ _

abbrev sourceDiagram
    (trace : VacuousElimTrace input bubble raw) : ConcreteDiagram :=
  trace.promotion.diagram

def origin
    (trace : VacuousElimTrace input bubble raw) :
    Fin trace.sourceDiagram.regionCount → Fin input.regionCount :=
  (vacuousRegionDomain input bubble).origin

theorem origin_injective
    (trace : VacuousElimTrace input bubble raw) :
    Function.Injective trace.origin :=
  (vacuousRegionDomain input bubble).origin_injective

def occurrenceMap
    (trace : VacuousElimTrace input bubble raw) :
    ConcreteElaboration.LocalOccurrence
        trace.sourceDiagram.regionCount trace.sourceDiagram.nodeCount →
      ConcreteElaboration.LocalOccurrence input.regionCount input.nodeCount
  | .node node => .node node
  | .child child => .child (trace.origin child)

private theorem mappedOwner_eq_targetIndex_iff
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (owner : Fin input.regionCount)
    (mapped : Fin (vacuousRegionDomain input bubble).count)
    (result :
      (vacuousRegionDomain input bubble).index?
          (if owner = bubble then trace.parent else owner) = some mapped) :
    mapped = trace.targetIndex wellFormed ↔
      owner = trace.parent ∨ owner = bubble := by
  let domain := vacuousRegionDomain input bubble
  have mappedOrigin :
      domain.origin mapped =
        (if owner = bubble then trace.parent else owner) :=
    (domain.index?_eq_some_iff _ _).1 result
  constructor
  · intro equality
    by_cases ownerBubble : owner = bubble
    · exact Or.inr ownerBubble
    · left
      rw [if_neg ownerBubble, equality] at mappedOrigin
      exact mappedOrigin.symm.trans (trace.targetIndex_origin wellFormed)
  · rintro (ownerParent | ownerBubble)
    · apply domain.origin_injective
      rw [trace.targetIndex_origin]
      simpa [domain, ownerParent, trace.parent_ne_bubble wellFormed] using
        mappedOrigin
    · apply domain.origin_injective
      rw [trace.targetIndex_origin]
      simpa [domain, ownerBubble] using mappedOrigin

private theorem mappedOwner_eq_region_iff
    (trace : VacuousElimTrace input bubble raw)
    (owner : Fin input.regionCount)
    (mapped region : Fin (vacuousRegionDomain input bubble).count)
    (result :
      (vacuousRegionDomain input bubble).index?
          (if owner = bubble then trace.parent else owner) = some mapped) :
    mapped = region ↔
      (if owner = bubble then trace.parent else owner) = trace.origin region := by
  let domain := vacuousRegionDomain input bubble
  have mappedOrigin :
      domain.origin mapped =
        (if owner = bubble then trace.parent else owner) :=
    (domain.index?_eq_some_iff _ _).1 result
  constructor
  · intro equality
    exact mappedOrigin.symm.trans (congrArg domain.origin equality)
  · intro equality
    apply domain.origin_injective
    exact mappedOrigin.trans equality

private theorem chosenOwner_eq_origin_regular_iff
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (owner : Fin input.regionCount)
    (region : Fin (vacuousRegionDomain input bubble).count)
    (regular : region ≠ trace.targetIndex wellFormed) :
    (if owner = bubble then trace.parent else owner) = trace.origin region ↔
      owner = trace.origin region := by
  by_cases bubbleOwner : owner = bubble
  · rw [if_pos bubbleOwner]
    constructor
    · intro parentOrigin
      exfalso
      apply regular
      apply (vacuousRegionDomain input bubble).origin_injective
      rw [trace.targetIndex_origin]
      exact parentOrigin.symm
    · intro ownerOrigin
      exfalso
      exact trace.origin_ne_bubble region (ownerOrigin.symm.trans bubbleOwner)
  · simp [bubbleOwner]

theorem promotedNode_region_eq_targetIndex_iff
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (node : Fin input.nodeCount) :
    (trace.promotion.nodes node).region = trace.targetIndex wellFormed ↔
      (input.nodes node).region = trace.parent ∨
        (input.nodes node).region = bubble := by
  have result := trace.promotion.node_result node
  cases nodeShape : input.nodes node with
  | term owner freePorts term =>
      rw [nodeShape] at result
      simp only [promoteNode?] at result
      rw [Option.map_eq_some_iff] at result
      obtain ⟨mapped, mappedResult, nodeResult⟩ := result
      change (trace.promotion.nodes node).region =
          trace.targetIndex wellFormed ↔
        owner = trace.parent ∨ owner = bubble
      have regionResult := congrArg CNode.region nodeResult
      rw [← regionResult]
      exact mappedOwner_eq_targetIndex_iff trace wellFormed owner mapped
        mappedResult
  | atom owner binder =>
      rw [nodeShape] at result
      simp only [promoteNode?] at result
      change ((vacuousRegionDomain input bubble).index?
          (if owner = bubble then trace.parent else owner)).bind
          (fun mappedOwner =>
            ((vacuousRegionDomain input bubble).index? binder).bind
              (fun mappedBinder => some (.atom mappedOwner mappedBinder))) =
        some (trace.promotion.nodes node) at result
      rw [Option.bind_eq_some_iff] at result
      obtain ⟨mappedOwner, ownerResult, result⟩ := result
      rw [Option.bind_eq_some_iff] at result
      obtain ⟨mappedBinder, binderResult, nodeResult⟩ := result
      change (trace.promotion.nodes node).region =
          trace.targetIndex wellFormed ↔
        owner = trace.parent ∨ owner = bubble
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
        owner = trace.parent ∨ owner = bubble
      have regionResult := congrArg CNode.region nodeResult
      rw [← regionResult]
      exact mappedOwner_eq_targetIndex_iff trace wellFormed owner mapped
        mappedResult

theorem promotedNode_region_eq_regular_iff
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (node : Fin input.nodeCount)
    (region : Fin (vacuousRegionDomain input bubble).count)
    (regular : region ≠ trace.targetIndex wellFormed) :
    (trace.promotion.nodes node).region = region ↔
      (input.nodes node).region = trace.origin region := by
  have result := trace.promotion.node_result node
  cases nodeShape : input.nodes node with
  | term owner freePorts term =>
      rw [nodeShape] at result
      simp only [promoteNode?] at result
      rw [Option.map_eq_some_iff] at result
      obtain ⟨mapped, mappedResult, nodeResult⟩ := result
      change (trace.promotion.nodes node).region = region ↔
        owner = trace.origin region
      have regionResult := congrArg CNode.region nodeResult
      rw [← regionResult]
      exact (mappedOwner_eq_region_iff trace owner mapped region
        mappedResult).trans
          (trace.chosenOwner_eq_origin_regular_iff wellFormed owner region
            regular)
  | atom owner binder =>
      rw [nodeShape] at result
      simp only [promoteNode?] at result
      change ((vacuousRegionDomain input bubble).index?
          (if owner = bubble then trace.parent else owner)).bind
          (fun mappedOwner =>
            ((vacuousRegionDomain input bubble).index? binder).bind
              (fun mappedBinder => some (.atom mappedOwner mappedBinder))) =
        some (trace.promotion.nodes node) at result
      rw [Option.bind_eq_some_iff] at result
      obtain ⟨mappedOwner, ownerResult, result⟩ := result
      rw [Option.bind_eq_some_iff] at result
      obtain ⟨mappedBinder, binderResult, nodeResult⟩ := result
      change (trace.promotion.nodes node).region = region ↔
        owner = trace.origin region
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
        owner = trace.origin region
      have regionResult := congrArg CNode.region nodeResult
      rw [← regionResult]
      exact (mappedOwner_eq_region_iff trace owner mapped region
        mappedResult).trans
          (trace.chosenOwner_eq_origin_regular_iff wellFormed owner region
            regular)

theorem regular_nodeShape
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (region : Fin (vacuousRegionDomain input bubble).count)
    (regular : region ≠ trace.targetIndex wellFormed)
    (node : Fin input.nodeCount)
    (nodeRegion : (trace.promotion.nodes node).region = region) :
    input.nodes node =
      match trace.promotion.nodes node with
      | .term owner freePorts term => .term (trace.origin owner) freePorts term
      | .atom owner binder => .atom (trace.origin owner) (trace.origin binder)
      | .named owner definition arity =>
          .named (trace.origin owner) definition arity := by
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
      change ((vacuousRegionDomain input bubble).index?
          (if owner = bubble then trace.parent else owner)).bind
          (fun mappedOwner =>
            ((vacuousRegionDomain input bubble).index? binder).bind
              (fun mappedBinder => some (.atom mappedOwner mappedBinder))) =
        some (trace.promotion.nodes node) at result
      rw [Option.bind_eq_some_iff] at result
      obtain ⟨mappedOwner, ownerResult, result⟩ := result
      rw [Option.bind_eq_some_iff] at result
      obtain ⟨mappedBinder, binderResult, nodeResult⟩ := result
      have mappedOwnerEq : mappedOwner = region :=
        (congrArg CNode.region (Option.some.inj nodeResult)).trans nodeRegion
      have binderEq : trace.origin mappedBinder = binder :=
        ((vacuousRegionDomain input bubble).index?_eq_some_iff
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
    (trace : VacuousElimTrace input bubble raw)
    (node : Fin input.nodeCount) (owner : Fin input.regionCount)
    (ownerEq : (input.nodes node).region = owner) :
    input.nodes node =
      match trace.promotion.nodes node with
      | .term _ freePorts term => .term owner freePorts term
      | .atom _ binder => .atom owner (trace.origin binder)
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
      change ((vacuousRegionDomain input bubble).index?
          (if originalOwner = bubble then trace.parent else originalOwner)).bind
          (fun mappedOwner =>
            ((vacuousRegionDomain input bubble).index? binder).bind
              (fun mappedBinder => some (.atom mappedOwner mappedBinder))) =
        some (trace.promotion.nodes node) at result
      rw [Option.bind_eq_some_iff] at result
      obtain ⟨mappedOwner, ownerResult, result⟩ := result
      rw [Option.bind_eq_some_iff] at result
      obtain ⟨mappedBinder, binderResult, nodeResult⟩ := result
      have binderEq : trace.origin mappedBinder = binder :=
        ((vacuousRegionDomain input bubble).index?_eq_some_iff
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
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (wire : Fin input.wireCount) :
    (trace.promotion.wires wire).scope = trace.targetIndex wellFormed ↔
      (input.wires wire).scope = trace.parent ∨
        (input.wires wire).scope = bubble := by
  have result := trace.promotion.wire_result wire
  unfold promoteWire? at result
  change ((vacuousRegionDomain input bubble).index?
      (if (input.wires wire).scope = bubble then trace.parent
        else (input.wires wire).scope)).bind
        (fun mapped => some {
          scope := mapped
          endpoints := (input.wires wire).endpoints
        }) = some (trace.promotion.wires wire) at result
  rw [Option.bind_eq_some_iff] at result
  obtain ⟨mapped, mappedResult, wireResult⟩ := result
  have scopeResult := congrArg CWire.scope (Option.some.inj wireResult)
  rw [← scopeResult]
  exact mappedOwner_eq_targetIndex_iff trace wellFormed
    (input.wires wire).scope mapped mappedResult

theorem promotedWire_scope_eq_regular_iff
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (wire : Fin input.wireCount)
    (region : Fin (vacuousRegionDomain input bubble).count)
    (regular : region ≠ trace.targetIndex wellFormed) :
    (trace.promotion.wires wire).scope = region ↔
      (input.wires wire).scope = trace.origin region := by
  have result := trace.promotion.wire_result wire
  unfold promoteWire? at result
  change ((vacuousRegionDomain input bubble).index?
      (if (input.wires wire).scope = bubble then trace.parent
        else (input.wires wire).scope)).bind
        (fun mapped => some {
          scope := mapped
          endpoints := (input.wires wire).endpoints
        }) = some (trace.promotion.wires wire) at result
  rw [Option.bind_eq_some_iff] at result
  obtain ⟨mapped, mappedResult, wireResult⟩ := result
  have scopeResult := congrArg CWire.scope (Option.some.inj wireResult)
  rw [← scopeResult]
  rw [mappedOwner_eq_region_iff trace (input.wires wire).scope mapped
    region mappedResult]
  exact trace.chosenOwner_eq_origin_regular_iff wellFormed
    (input.wires wire).scope region regular

theorem regular_exactScopeWires
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (region : Fin (vacuousRegionDomain input bubble).count)
    (regular : region ≠ trace.targetIndex wellFormed) :
    ConcreteElaboration.exactScopeWires trace.sourceDiagram region =
      ConcreteElaboration.exactScopeWires input (trace.origin region) := by
  unfold ConcreteElaboration.exactScopeWires filterFin sourceDiagram
    PromoteDiagramTrace.diagram
  apply congrArg (fun predicate => List.filter predicate (allFin input.wireCount))
  funext wire
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact trace.promotedWire_scope_eq_regular_iff wellFormed wire region regular

theorem promotedWire_endpoints
    (trace : VacuousElimTrace input bubble raw)
    (wire : Fin input.wireCount) :
    (trace.promotion.wires wire).endpoints = (input.wires wire).endpoints := by
  have result := trace.promotion.wire_result wire
  unfold promoteWire? at result
  change ((vacuousRegionDomain input bubble).index?
      (if (input.wires wire).scope = bubble then trace.parent
        else (input.wires wire).scope)).bind
        (fun mapped => some {
          scope := mapped
          endpoints := (input.wires wire).endpoints
        }) = some (trace.promotion.wires wire) at result
  rw [Option.bind_eq_some_iff] at result
  obtain ⟨mapped, mappedResult, wireResult⟩ := result
  exact (congrArg CWire.endpoints (Option.some.inj wireResult)).symm

theorem promotedRegion_parent_eq_targetIndex_iff
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (region : Fin (vacuousRegionDomain input bubble).count) :
    (trace.promotion.regions region).parent? =
        some (trace.targetIndex wellFormed) ↔
      (input.regions (trace.origin region)).parent? = some trace.parent ∨
        (input.regions (trace.origin region)).parent? = some bubble := by
  have result := trace.promotion.region_result region
  change promoteRegion? (vacuousRegionDomain input bubble) bubble trace.parent
      (input.regions (trace.origin region)) =
    some (trace.promotion.regions region) at result
  cases regionShape : input.regions (trace.origin region) with
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
          (if parent = bubble then
              Option.map CRegion.cut
                ((vacuousRegionDomain input bubble).index? trace.parent)
            else
              Option.map CRegion.cut
                ((vacuousRegionDomain input bubble).index? parent)) =
            Option.map CRegion.cut
              ((vacuousRegionDomain input bubble).index?
                (if parent = bubble then trace.parent else parent)) := by
        by_cases parentBubble : parent = bubble <;> simp [parentBubble]
      rw [normalized, Option.map_eq_some_iff] at result
      obtain ⟨mapped, mappedResult, regionResult⟩ := result
      change (trace.promotion.regions region).parent? =
          some (trace.targetIndex wellFormed) ↔
        some parent = some trace.parent ∨ some parent = some bubble
      have parentResult := congrArg CRegion.parent? regionResult
      rw [← parentResult]
      simp only [CRegion.parent?, Option.some.injEq]
      exact mappedOwner_eq_targetIndex_iff trace wellFormed parent mapped
        mappedResult
  | bubble parent arity =>
      rw [regionShape] at result
      simp only [promoteRegion?] at result
      have normalized :
          (if parent = bubble then
              Option.map (fun mapped => CRegion.bubble mapped arity)
                ((vacuousRegionDomain input bubble).index? trace.parent)
            else
              Option.map (fun mapped => CRegion.bubble mapped arity)
                ((vacuousRegionDomain input bubble).index? parent)) =
            Option.map (fun mapped => CRegion.bubble mapped arity)
              ((vacuousRegionDomain input bubble).index?
                (if parent = bubble then trace.parent else parent)) := by
        by_cases parentBubble : parent = bubble <;> simp [parentBubble]
      rw [normalized, Option.map_eq_some_iff] at result
      obtain ⟨mapped, mappedResult, regionResult⟩ := result
      change (trace.promotion.regions region).parent? =
          some (trace.targetIndex wellFormed) ↔
        some parent = some trace.parent ∨ some parent = some bubble
      have parentResult := congrArg CRegion.parent? regionResult
      rw [← parentResult]
      simp only [CRegion.parent?, Option.some.injEq]
      exact mappedOwner_eq_targetIndex_iff trace wellFormed parent mapped
        mappedResult

theorem promotedRegion_parent_eq_regular_iff
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (child region : Fin (vacuousRegionDomain input bubble).count)
    (regular : region ≠ trace.targetIndex wellFormed) :
    (trace.promotion.regions child).parent? = some region ↔
      (input.regions (trace.origin child)).parent? =
        some (trace.origin region) := by
  have result := trace.promotion.region_result child
  change promoteRegion? (vacuousRegionDomain input bubble) bubble trace.parent
      (input.regions (trace.origin child)) =
    some (trace.promotion.regions child) at result
  cases regionShape : input.regions (trace.origin child) with
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
          (if parent = bubble then
              Option.map CRegion.cut
                ((vacuousRegionDomain input bubble).index? trace.parent)
            else
              Option.map CRegion.cut
                ((vacuousRegionDomain input bubble).index? parent)) =
            Option.map CRegion.cut
              ((vacuousRegionDomain input bubble).index?
                (if parent = bubble then trace.parent else parent)) := by
        by_cases parentBubble : parent = bubble <;> simp [parentBubble]
      rw [normalized, Option.map_eq_some_iff] at result
      obtain ⟨mapped, mappedResult, regionResult⟩ := result
      change (trace.promotion.regions child).parent? = some region ↔
        some parent = some (trace.origin region)
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
          (if parent = bubble then
              Option.map (fun mapped => CRegion.bubble mapped arity)
                ((vacuousRegionDomain input bubble).index? trace.parent)
            else
              Option.map (fun mapped => CRegion.bubble mapped arity)
                ((vacuousRegionDomain input bubble).index? parent)) =
            Option.map (fun mapped => CRegion.bubble mapped arity)
              ((vacuousRegionDomain input bubble).index?
                (if parent = bubble then trace.parent else parent)) := by
        by_cases parentBubble : parent = bubble <;> simp [parentBubble]
      rw [normalized, Option.map_eq_some_iff] at result
      obtain ⟨mapped, mappedResult, regionResult⟩ := result
      change (trace.promotion.regions child).parent? = some region ↔
        some parent = some (trace.origin region)
      have parentResult := congrArg CRegion.parent? regionResult
      rw [← parentResult]
      simp only [CRegion.parent?, Option.some.injEq]
      exact (mappedOwner_eq_region_iff trace parent mapped region
        mappedResult).trans
          (trace.chosenOwner_eq_origin_regular_iff wellFormed parent region
            regular)

theorem regular_regionShape
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (parent : Fin (vacuousRegionDomain input bubble).count)
    (regular : parent ≠ trace.targetIndex wellFormed)
    (child : Fin (vacuousRegionDomain input bubble).count)
    (childParent : (trace.promotion.regions child).parent? = some parent) :
    input.regions (trace.origin child) =
      match trace.promotion.regions child with
      | .sheet => .sheet
      | .cut _ => .cut (trace.origin parent)
      | .bubble _ arity => .bubble (trace.origin parent) arity := by
  have targetParent :=
    (trace.promotedRegion_parent_eq_regular_iff
      wellFormed child parent regular).1 childParent
  have result := trace.promotion.region_result child
  change promoteRegion? (vacuousRegionDomain input bubble) bubble trace.parent
      (input.regions (trace.origin child)) =
    some (trace.promotion.regions child) at result
  cases originalShape : input.regions (trace.origin child) with
  | sheet =>
      rw [originalShape] at targetParent
      simp [CRegion.parent?] at targetParent
  | cut originalParent =>
      have originalParentEq : originalParent = trace.origin parent := by
        rw [originalShape] at targetParent
        exact Option.some.inj targetParent
      rw [originalShape] at result
      simp only [promoteRegion?] at result
      have normalized :
          (if originalParent = bubble then
              Option.map CRegion.cut
                ((vacuousRegionDomain input bubble).index? trace.parent)
            else
              Option.map CRegion.cut
                ((vacuousRegionDomain input bubble).index? originalParent)) =
            Option.map CRegion.cut
              ((vacuousRegionDomain input bubble).index?
                (if originalParent = bubble then trace.parent
                  else originalParent)) := by
        by_cases parentBubble : originalParent = bubble <;> simp [parentBubble]
      rw [normalized, Option.map_eq_some_iff] at result
      obtain ⟨mapped, mappedResult, regionResult⟩ := result
      rw [← regionResult]
      simp [originalParentEq]
  | bubble originalParent arity =>
      have originalParentEq : originalParent = trace.origin parent := by
        rw [originalShape] at targetParent
        exact Option.some.inj targetParent
      rw [originalShape] at result
      simp only [promoteRegion?] at result
      have normalized :
          (if originalParent = bubble then
              Option.map (fun mapped => CRegion.bubble mapped arity)
                ((vacuousRegionDomain input bubble).index? trace.parent)
            else
              Option.map (fun mapped => CRegion.bubble mapped arity)
                ((vacuousRegionDomain input bubble).index? originalParent)) =
            Option.map (fun mapped => CRegion.bubble mapped arity)
              ((vacuousRegionDomain input bubble).index?
                (if originalParent = bubble then trace.parent
                  else originalParent)) := by
        by_cases parentBubble : originalParent = bubble <;> simp [parentBubble]
      rw [normalized, Option.map_eq_some_iff] at result
      obtain ⟨mapped, mappedResult, regionResult⟩ := result
      rw [← regionResult]
      simp [originalParentEq]

theorem focused_regionShape
    (trace : VacuousElimTrace input bubble raw)
    (child : Fin (vacuousRegionDomain input bubble).count)
    (parent : Fin input.regionCount)
    (parentEq :
      (input.regions (trace.origin child)).parent? = some parent) :
    input.regions (trace.origin child) =
      match trace.promotion.regions child with
      | .sheet => .sheet
      | .cut _ => .cut parent
      | .bubble _ arity => .bubble parent arity := by
  have result := trace.promotion.region_result child
  change promoteRegion? (vacuousRegionDomain input bubble) bubble trace.parent
      (input.regions (trace.origin child)) =
    some (trace.promotion.regions child) at result
  cases originalShape : input.regions (trace.origin child) with
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
          (if originalParent = bubble then
              Option.map CRegion.cut
                ((vacuousRegionDomain input bubble).index? trace.parent)
            else
              Option.map CRegion.cut
                ((vacuousRegionDomain input bubble).index? originalParent)) =
            Option.map CRegion.cut
              ((vacuousRegionDomain input bubble).index?
                (if originalParent = bubble then trace.parent
                  else originalParent)) := by
        by_cases parentBubble : originalParent = bubble <;> simp [parentBubble]
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
          (if originalParent = bubble then
              Option.map (fun mapped => CRegion.bubble mapped arity)
                ((vacuousRegionDomain input bubble).index? trace.parent)
            else
              Option.map (fun mapped => CRegion.bubble mapped arity)
                ((vacuousRegionDomain input bubble).index? originalParent)) =
            Option.map (fun mapped => CRegion.bubble mapped arity)
              ((vacuousRegionDomain input bubble).index?
                (if originalParent = bubble then trace.parent
                  else originalParent)) := by
        by_cases parentBubble : originalParent = bubble <;> simp [parentBubble]
      rw [normalized, Option.map_eq_some_iff] at result
      obtain ⟨mapped, mappedResult, regionResult⟩ := result
      rw [← regionResult]
      simp [originalParentEq]

def wireIdentityRelation
    (trace : VacuousElimTrace input bubble raw)
    (sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input) :
    ConcreteElaboration.ContextIndexRelation
      sourceContext.length targetContext.length where
  Rel sourceIndex targetIndex :=
    sourceContext.get sourceIndex = targetContext.get targetIndex

structure PromotedBinderWitness
    (trace : VacuousElimTrace input bubble raw)
    {sourceRels targetRels : RelCtx}
    (sourceBinders : ConcreteElaboration.BinderContext
      trace.sourceDiagram sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext input targetRels) : Type
    where
  relationContexts_eq : sourceRels = targetRels
  binders_eq : ∀ region,
    HEq (sourceBinders region) (targetBinders (trace.origin region))

namespace PromotedBinderWitness

def relationMap
    (witness : PromotedBinderWitness trace
      (sourceRels := sourceRels) (targetRels := targetRels)
      sourceBinders targetBinders) :
    RelationRenaming sourceRels targetRels := by
  cases witness.relationContexts_eq
  exact ConcreteElaboration.identityRelationRenaming sourceRels

def push
    {input : ConcreteDiagram} {bubble : Fin input.regionCount}
    {raw : ConcreteDiagram}
    {trace : VacuousElimTrace input bubble raw}
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
  · have originNe : trace.origin region ≠ trace.origin child :=
      fun originEq => equality (trace.origin_injective originEq)
    rw [if_neg equality, if_neg originNe]
    apply heq_of_eq
    rw [eq_of_heq (witness.binders_eq region)]

theorem relationMap_push
    {input : ConcreteDiagram} {bubble : Fin input.regionCount}
    {raw : ConcreteDiagram}
    {trace : VacuousElimTrace input bubble raw}
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

def BindersMapped
    (trace : VacuousElimTrace input bubble raw)
    (sourceBinders : ConcreteElaboration.BinderContext
      trace.sourceDiagram sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext input targetRels)
    (relationMap : RelationRenaming sourceRels targetRels) : Prop :=
  ∀ region binderArity sourceRelation,
    sourceBinders region = some ⟨binderArity, sourceRelation⟩ →
    targetBinders (trace.origin region) =
      some ⟨binderArity, relationMap sourceRelation⟩

structure MappedBinderWitness
    (trace : VacuousElimTrace input bubble raw)
    {sourceRels targetRels : RelCtx}
    (sourceBinders : ConcreteElaboration.BinderContext
      trace.sourceDiagram sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext input targetRels) where
  relationMap : RelationRenaming sourceRels targetRels
  bindersMapped : BindersMapped trace sourceBinders targetBinders relationMap

namespace MappedBinderWitness

def ofPromoted
    (witness : PromotedBinderWitness trace sourceBinders targetBinders) :
    MappedBinderWitness trace sourceBinders targetBinders where
  relationMap := witness.relationMap
  bindersMapped := by
    intro region binderArity sourceRelation sourceLookup
    cases witness.relationContexts_eq
    simpa [PromotedBinderWitness.relationMap] using
      (eq_of_heq (witness.binders_eq region)).symm.trans sourceLookup

def push
    {input : ConcreteDiagram} {bubble : Fin input.regionCount}
    {raw : ConcreteDiagram}
    {trace : VacuousElimTrace input bubble raw}
    {sourceRels targetRels : RelCtx}
    {sourceBinders : ConcreteElaboration.BinderContext
      trace.sourceDiagram sourceRels}
    {targetBinders : ConcreteElaboration.BinderContext input targetRels}
    (witness : MappedBinderWitness trace sourceBinders targetBinders)
    (child : Fin trace.sourceDiagram.regionCount) (arity : Nat) :
    MappedBinderWitness trace
      (sourceBinders.push child arity)
      (targetBinders.push (trace.origin child) arity) where
  relationMap := RelationRenaming.lift witness.relationMap arity
  bindersMapped := by
    intro region binderArity sourceRelation sourceLookup
    by_cases equality : region = child
    · subst region
      simp only [ConcreteElaboration.BinderContext.push_self] at sourceLookup ⊢
      cases Option.some.inj sourceLookup
      rfl
    · have originNe : trace.origin region ≠ trace.origin child :=
        fun originEq => equality (trace.origin_injective originEq)
      rw [ConcreteElaboration.BinderContext.push_other _ arity equality]
        at sourceLookup
      rw [ConcreteElaboration.BinderContext.push_other _ arity originNe]
      cases sourceEq : sourceBinders region with
      | none => simp [sourceEq] at sourceLookup
      | some sourceValue =>
          rcases sourceValue with ⟨actualArity, actualRelation⟩
          simp [sourceEq] at sourceLookup
          rcases sourceLookup with ⟨arityEq, relationEq⟩
          subst binderArity
          have relationEq' := eq_of_heq relationEq
          subst sourceRelation
          rw [witness.bindersMapped region actualArity actualRelation sourceEq]
          rfl

theorem relationMap_push
    (witness : MappedBinderWitness trace
      (sourceRels := sourceRels) (targetRels := targetRels)
      sourceBinders targetBinders)
    (child : Fin trace.sourceDiagram.regionCount) (arity : Nat) :
    ((push witness child arity).relationMap :
      RelationRenaming (arity :: sourceRels) (arity :: targetRels)) =
      (RelationRenaming.lift witness.relationMap arity :
        RelationRenaming (arity :: sourceRels) (arity :: targetRels)) := rfl

def intoBubble
    {input : ConcreteDiagram} {bubble : Fin input.regionCount}
    {raw : ConcreteDiagram}
    {trace : VacuousElimTrace input bubble raw}
    {sourceRels targetRels : RelCtx}
    {sourceBinders : ConcreteElaboration.BinderContext
      trace.sourceDiagram sourceRels}
    {targetBinders : ConcreteElaboration.BinderContext input targetRels}
    (witness : MappedBinderWitness trace
      (sourceRels := sourceRels) (targetRels := targetRels)
      sourceBinders targetBinders)
    (arity : Nat) :
    MappedBinderWitness trace sourceBinders
      (targetBinders.push bubble arity) where
  relationMap := fun relation =>
    ConcreteElaboration.BinderContext.liftVar arity
      (witness.relationMap relation)
  bindersMapped := by
    intro region binderArity sourceRelation sourceLookup
    have originNe : trace.origin region ≠ bubble := by
      exact VacuousElimTrace.origin_ne_bubble trace region
    rw [ConcreteElaboration.BinderContext.push_other _ arity originNe]
    rw [witness.bindersMapped region binderArity sourceRelation sourceLookup]
    rfl

end MappedBinderWitness

/-- Environment-sensitive choice of the relation inserted when reconstructing
the eliminated bubble.  The selector receives both sides of the focused
compiler correspondence, including the exact pre-bubble target context; this
is the information needed by comprehension instantiation to choose its one
trace-wide relation witness. -/
def FreshRelationSelector
    (trace : VacuousElimTrace input bubble raw)
    (targetWellFormed : input.WellFormed signature)
    (model : Lambda.LambdaModel) :=
  ∀ {sourceRels targetRels : RelCtx}
    (sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input)
    (sourceBinders : ConcreteElaboration.BinderContext
      trace.sourceDiagram sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext input targetRels),
    sourceContext.Exact (trace.targetIndex targetWellFormed) →
    (targetContext.extend bubble).Exact bubble →
    sourceBinders.Covers (trace.targetIndex targetWellFormed) →
    targetBinders.Covers trace.parent →
    ConcreteElaboration.BinderContext.Enumeration trace.sourceDiagram
      sourceBinders (trace.targetIndex targetWellFormed) →
    ConcreteElaboration.BinderContext.Enumeration input targetBinders
      trace.parent →
    (binderWitness : MappedBinderWitness trace sourceBinders targetBinders) →
    (Fin sourceContext.length → model.Carrier) →
    (Fin targetContext.length → model.Carrier) →
    RelEnv model.Carrier sourceRels →
    RelEnv model.Carrier targetRels →
    Relation model.Carrier trace.arity

structure PromotedContextWitness
    (trace : VacuousElimTrace input bubble raw)
    (sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input) : Prop where
  target_subset_source : ∀ wire, wire ∈ targetContext → wire ∈ sourceContext
  source_subset_target_or_bubble : ∀ wire, wire ∈ sourceContext →
    wire ∈ targetContext ∨
      wire ∈ ConcreteElaboration.exactScopeWires input bubble

namespace PromotedContextWitness

def indexRelation
    (witness : PromotedContextWitness trace sourceContext targetContext) :
    ConcreteElaboration.ContextIndexRelation
      sourceContext.length targetContext.length :=
  trace.wireIdentityRelation sourceContext targetContext

def extendRegular
    {input : ConcreteDiagram} {bubble : Fin input.regionCount}
    {raw : ConcreteDiagram}
    {trace : VacuousElimTrace input bubble raw}
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
    · rcases witness.source_subset_target_or_bubble wire outerMember with
        targetMember | bubbleMember
      · exact Or.inl (List.mem_append_left _ targetMember)
      · exact Or.inr bubbleMember
    · exact Or.inl (List.mem_append_right targetContext (by
        change wire ∈ ConcreteElaboration.exactScopeWires input
          (trace.origin region)
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
    (trace : VacuousElimTrace input bubble raw)
    (wire : Fin input.wireCount)
    (endpoint : CEndpoint input.nodeCount) :
    trace.sourceDiagram.EndpointOccurs wire endpoint ↔
      input.EndpointOccurs wire endpoint := by
  simp only [ConcreteDiagram.EndpointOccurs]
  change endpoint ∈ (trace.promotion.wires wire).endpoints ↔
    endpoint ∈ (input.wires wire).endpoints
  rw [trace.promotedWire_endpoints wire]

theorem resolvedPorts_related
    (trace : VacuousElimTrace input bubble raw)
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
  have sourceOccursInput : input.EndpointOccurs sourceWire ⟨node, port⟩ :=
    (trace.promoted_endpointOccurs sourceWire ⟨node, port⟩).1 sourceOccurs
  have wireEq : sourceWire = targetWire :=
    ConcreteElaboration.endpoint_wire_unique
      wellFormed.wire_endpoints_are_disjoint sourceOccursInput targetOccurs
  exact sourceGet.trans (wireEq.trans targetGet.symm)

def occurrenceSelected
    (trace : VacuousElimTrace input bubble raw) :
    ConcreteElaboration.LocalOccurrence
        trace.sourceDiagram.regionCount trace.sourceDiagram.nodeCount → Bool
  | .node node => decide ((input.nodes node).region = bubble)
  | .child child =>
      decide ((input.regions (trace.origin child)).parent? = some bubble)

@[simp] theorem occurrenceMap_map_nodes
    (trace : VacuousElimTrace input bubble raw)
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
    (trace : VacuousElimTrace input bubble raw)
    (children : List (Fin (vacuousRegionDomain input bubble).count)) :
    (children.map ConcreteElaboration.LocalOccurrence.child).map
        trace.occurrenceMap =
      children.map (ConcreteElaboration.LocalOccurrence.child ∘ trace.origin) := by
  induction children with
  | nil => rfl
  | cons child rest induction =>
      change ConcreteElaboration.LocalOccurrence.child (trace.origin child) ::
          (rest.map ConcreteElaboration.LocalOccurrence.child).map
            trace.occurrenceMap =
        ConcreteElaboration.LocalOccurrence.child (trace.origin child) ::
          rest.map (ConcreteElaboration.LocalOccurrence.child ∘ trace.origin)
      rw [induction]

@[simp] theorem occurrenceMap_map_source_nodes
    (trace : VacuousElimTrace input bubble raw)
    (nodes : List (Fin trace.sourceDiagram.nodeCount)) :
    (nodes.map (ConcreteElaboration.LocalOccurrence.node
      (regions := trace.sourceDiagram.regionCount))).map trace.occurrenceMap =
      nodes.map ConcreteElaboration.LocalOccurrence.node := by
  induction nodes with
  | nil => rfl
  | cons node rest induction =>
      change ConcreteElaboration.LocalOccurrence.node node ::
          (rest.map (ConcreteElaboration.LocalOccurrence.node
            (regions := trace.sourceDiagram.regionCount))).map
              trace.occurrenceMap =
        ConcreteElaboration.LocalOccurrence.node node ::
          rest.map ConcreteElaboration.LocalOccurrence.node
      exact congrArg
        (List.cons (ConcreteElaboration.LocalOccurrence.node node)) induction

@[simp] theorem occurrenceMap_map_source_children
    (trace : VacuousElimTrace input bubble raw)
    (children : List (Fin trace.sourceDiagram.regionCount)) :
    (children.map (ConcreteElaboration.LocalOccurrence.child
      (nodes := trace.sourceDiagram.nodeCount))).map trace.occurrenceMap =
      children.map (ConcreteElaboration.LocalOccurrence.child ∘ trace.origin) := by
  induction children with
  | nil => rfl
  | cons child rest induction =>
      change ConcreteElaboration.LocalOccurrence.child (trace.origin child) ::
          (rest.map (ConcreteElaboration.LocalOccurrence.child
            (nodes := trace.sourceDiagram.nodeCount))).map
              trace.occurrenceMap =
        ConcreteElaboration.LocalOccurrence.child (trace.origin child) ::
          rest.map (ConcreteElaboration.LocalOccurrence.child ∘ trace.origin)
      exact congrArg
        (List.cons (ConcreteElaboration.LocalOccurrence.child
          (trace.origin child))) induction

def selectedOccurrences
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature) :
    List (ConcreteElaboration.LocalOccurrence
      trace.sourceDiagram.regionCount trace.sourceDiagram.nodeCount) :=
  (ConcreteElaboration.localOccurrences trace.sourceDiagram
      (trace.targetIndex wellFormed)).filter trace.occurrenceSelected

def keptOccurrences
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature) :
    List (ConcreteElaboration.LocalOccurrence
      trace.sourceDiagram.regionCount trace.sourceDiagram.nodeCount) :=
  (ConcreteElaboration.localOccurrences trace.sourceDiagram
      (trace.targetIndex wellFormed)).filter
        (fun occurrence => !trace.occurrenceSelected occurrence)

theorem kept_node_region
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (node : Fin input.nodeCount)
    (member : ConcreteElaboration.LocalOccurrence.node node ∈
      trace.keptOccurrences wellFormed) :
    (input.nodes node).region = trace.parent := by
  have filtered := List.mem_filter.mp member
  have atFocus :=
    (ConcreteElaboration.mem_localOccurrences_node trace.sourceDiagram
      (trace.targetIndex wellFormed) node).mp filtered.1
  have notBubble : (input.nodes node).region ≠ bubble := by
    simpa [occurrenceSelected] using filtered.2
  rcases (trace.promotedNode_region_eq_targetIndex_iff
    wellFormed node).1 atFocus with atParent | atBubble
  · exact atParent
  · exact False.elim (notBubble atBubble)

theorem selected_node_region
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (node : Fin input.nodeCount)
    (member : ConcreteElaboration.LocalOccurrence.node node ∈
      trace.selectedOccurrences wellFormed) :
    (input.nodes node).region = bubble := by
  exact of_decide_eq_true (List.mem_filter.mp member).2

theorem kept_child_parent
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (child : Fin trace.sourceDiagram.regionCount)
    (member : ConcreteElaboration.LocalOccurrence.child child ∈
      trace.keptOccurrences wellFormed) :
    (input.regions (trace.origin child)).parent? = some trace.parent := by
  have filtered := List.mem_filter.mp member
  have atFocus :=
    (ConcreteElaboration.mem_localOccurrences_child trace.sourceDiagram
      (trace.targetIndex wellFormed) child).mp filtered.1
  have notBubble :
      (input.regions (trace.origin child)).parent? ≠ some bubble := by
    simpa [occurrenceSelected] using filtered.2
  rcases (trace.promotedRegion_parent_eq_targetIndex_iff
    wellFormed child).1 atFocus with atParent | atBubble
  · exact atParent
  · exact False.elim (notBubble atBubble)

theorem selected_child_parent
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (child : Fin trace.sourceDiagram.regionCount)
    (member : ConcreteElaboration.LocalOccurrence.child child ∈
      trace.selectedOccurrences wellFormed) :
    (input.regions (trace.origin child)).parent? = some bubble := by
  simpa [occurrenceSelected] using
    (of_decide_eq_true (List.mem_filter.mp member).2)

theorem focusOccurrences_perm_partition
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature) :
    List.Perm
      (trace.keptOccurrences wellFormed ++ trace.selectedOccurrences wellFormed)
      (ConcreteElaboration.localOccurrences trace.sourceDiagram
        (trace.targetIndex wellFormed)) := by
  simpa only [keptOccurrences, selectedOccurrences, Bool.not_not] using
    (List.filter_append_perm
      (fun occurrence => !trace.occurrenceSelected occurrence)
      (ConcreteElaboration.localOccurrences trace.sourceDiagram
        (trace.targetIndex wellFormed)))

def targetKeptOccurrences
    (trace : VacuousElimTrace input bubble raw) :
    List (ConcreteElaboration.LocalOccurrence input.regionCount
      input.nodeCount) :=
  (ConcreteElaboration.localOccurrences input trace.parent).filter
    (fun occurrence => decide
      (occurrence ≠ ConcreteElaboration.LocalOccurrence.child bubble))

private def canonicalSelectedOccurrences
    (trace : VacuousElimTrace input bubble raw) :
    List (ConcreteElaboration.LocalOccurrence
      trace.sourceDiagram.regionCount trace.sourceDiagram.nodeCount) :=
  (filterFin fun node =>
      decide ((input.nodes node).region = bubble)).map
        ConcreteElaboration.LocalOccurrence.node ++
    (filterFin fun child =>
      decide ((input.regions (trace.origin child)).parent? = some bubble)).map
        ConcreteElaboration.LocalOccurrence.child

private def canonicalKeptOccurrences
    (trace : VacuousElimTrace input bubble raw) :
    List (ConcreteElaboration.LocalOccurrence
      trace.sourceDiagram.regionCount trace.sourceDiagram.nodeCount) :=
  (filterFin fun node =>
      decide ((input.nodes node).region = trace.parent)).map
        ConcreteElaboration.LocalOccurrence.node ++
    (filterFin fun child =>
      decide ((input.regions (trace.origin child)).parent? =
        some trace.parent)).map ConcreteElaboration.LocalOccurrence.child

private def canonicalTargetKeptOccurrences
    (trace : VacuousElimTrace input bubble raw) :
    List (ConcreteElaboration.LocalOccurrence input.regionCount
      input.nodeCount) :=
  (filterFin fun node =>
      decide ((input.nodes node).region = trace.parent)).map
        ConcreteElaboration.LocalOccurrence.node ++
    (filterFin fun child =>
      decide ((input.regions child).parent? = some trace.parent ∧
        child ≠ bubble)).map ConcreteElaboration.LocalOccurrence.child

private theorem selectedOccurrences_eq_canonical
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature) :
    trace.selectedOccurrences wellFormed =
      trace.canonicalSelectedOccurrences := by
  unfold selectedOccurrences canonicalSelectedOccurrences
    ConcreteElaboration.localOccurrences occurrenceSelected filterFin
    sourceDiagram PromoteDiagramTrace.diagram
  simp only [List.filter_append, List.filter_map, List.filter_filter]
  congr 1
  · apply congrArg (List.map ConcreteElaboration.LocalOccurrence.node)
    apply congrArg (fun predicate =>
      List.filter predicate (allFin input.nodeCount))
    funext node
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · exact And.left
    · intro atBubble
      exact ⟨atBubble,
        (trace.promotedNode_region_eq_targetIndex_iff wellFormed node).2
          (Or.inr atBubble)⟩
  · apply congrArg (List.map ConcreteElaboration.LocalOccurrence.child)
    apply congrArg (fun predicate =>
      List.filter predicate (allFin (vacuousRegionDomain input bubble).count))
    funext child
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · exact And.left
    · intro atBubble
      exact ⟨atBubble,
        (trace.promotedRegion_parent_eq_targetIndex_iff
          wellFormed child).2 (Or.inr atBubble)⟩

private theorem keptOccurrences_eq_canonical
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature) :
    trace.keptOccurrences wellFormed = trace.canonicalKeptOccurrences := by
  unfold keptOccurrences canonicalKeptOccurrences
    ConcreteElaboration.localOccurrences occurrenceSelected filterFin
    sourceDiagram PromoteDiagramTrace.diagram
  simp only [List.filter_append, List.filter_map, List.filter_filter]
  congr 1
  · apply congrArg (List.map ConcreteElaboration.LocalOccurrence.node)
    apply congrArg (fun predicate =>
      List.filter predicate (allFin input.nodeCount))
    funext node
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨notBubbleBool, atFocus⟩
      have notBubble : (input.nodes node).region ≠ bubble := by
        simpa using notBubbleBool
      rcases (trace.promotedNode_region_eq_targetIndex_iff
        wellFormed node).1 atFocus with atParent | atBubble
      · exact atParent
      · exact False.elim (notBubble atBubble)
    · intro atParent
      have notBubble : (input.nodes node).region ≠ bubble := by
        intro atBubble
        exact trace.parent_ne_bubble wellFormed (atParent.symm.trans atBubble)
      exact ⟨by simpa using notBubble,
        (trace.promotedNode_region_eq_targetIndex_iff
          wellFormed node).2 (Or.inl atParent)⟩
  · apply congrArg (List.map ConcreteElaboration.LocalOccurrence.child)
    apply congrArg (fun predicate =>
      List.filter predicate (allFin (vacuousRegionDomain input bubble).count))
    funext child
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨notBubbleBool, atFocus⟩
      have notBubble :
          (input.regions (trace.origin child)).parent? ≠ some bubble := by
        simpa using notBubbleBool
      rcases (trace.promotedRegion_parent_eq_targetIndex_iff
        wellFormed child).1 atFocus with atParent | atBubble
      · exact atParent
      · exact False.elim (notBubble atBubble)
    · intro atParent
      have notBubble :
          (input.regions (trace.origin child)).parent? ≠ some bubble := by
        intro atBubble
        exact trace.parent_ne_bubble wellFormed
          (Option.some.inj (atParent.symm.trans atBubble))
      exact ⟨by simpa using notBubble,
        (trace.promotedRegion_parent_eq_targetIndex_iff
          wellFormed child).2 (Or.inl atParent)⟩

private theorem targetKeptOccurrences_eq_canonical
    (trace : VacuousElimTrace input bubble raw) :
    trace.targetKeptOccurrences = trace.canonicalTargetKeptOccurrences := by
  unfold targetKeptOccurrences canonicalTargetKeptOccurrences
    ConcreteElaboration.localOccurrences filterFin
  simp only [List.filter_append, List.filter_map, List.filter_filter]
  congr 1
  apply congrArg (List.map ConcreteElaboration.LocalOccurrence.child)
  apply congrArg (fun predicate =>
    List.filter predicate (allFin input.regionCount))
  funext child
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨different, parent⟩
    exact ⟨parent, fun equality => different
      (congrArg ConcreteElaboration.LocalOccurrence.child equality)⟩
  · rintro ⟨parent, different⟩
    exact ⟨fun equality => different
      (ConcreteElaboration.LocalOccurrence.child.inj equality), parent⟩

private theorem allFin_map_domain_origin
    (trace : VacuousElimTrace input bubble raw) :
    (allFin (vacuousRegionDomain input bubble).count).map
        (vacuousRegionDomain input bubble).origin =
      (vacuousRegionDomain input bubble).enumeration := by
  rw [allFin_eq_finRange, List.finRange, List.map_ofFn]
  change List.ofFn (fun index =>
    (vacuousRegionDomain input bubble).enumeration.get index) =
      (vacuousRegionDomain input bubble).enumeration
  exact List.ofFn_getElem

private theorem allFin_map_origin
    (trace : VacuousElimTrace input bubble raw) :
    (allFin trace.sourceDiagram.regionCount).map trace.origin =
      (vacuousRegionDomain input bubble).enumeration := by
  change (allFin (vacuousRegionDomain input bubble).count).map
      (vacuousRegionDomain input bubble).origin =
    (vacuousRegionDomain input bubble).enumeration
  exact allFin_map_domain_origin trace

private theorem allFin_domain_count_map_origin
    (trace : VacuousElimTrace input bubble raw) :
    (allFin (vacuousRegionDomain input bubble).count).map trace.origin =
      (vacuousRegionDomain input bubble).enumeration := by
  change (allFin (vacuousRegionDomain input bubble).count).map
      (vacuousRegionDomain input bubble).origin =
    (vacuousRegionDomain input bubble).enumeration
  exact allFin_map_domain_origin trace

theorem child_of_bubble_survives
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (child : Fin input.regionCount)
    (parentEq : (input.regions child).parent? = some bubble) :
    (vacuousRegionDomain input bubble).survives child = true := by
  have childNeBubble : child ≠ bubble := by
    intro equality
    apply ConcreteElaboration.checked_direct_child_not_encloses_parent
      wellFormed parentEq
    rw [equality]
    exact ConcreteDiagram.Encloses.refl input bubble
  simp [vacuousRegionDomain, childNeBubble]

theorem child_of_regular_survives
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (region : Fin (vacuousRegionDomain input bubble).count)
    (regular : region ≠ trace.targetIndex wellFormed)
    (child : Fin input.regionCount)
    (parentEq :
      (input.regions child).parent? = some (trace.origin region)) :
    (vacuousRegionDomain input bubble).survives child = true := by
  have childNeBubble : child ≠ bubble := by
    intro equality
    subst child
    have parentOrigin : trace.parent = trace.origin region :=
      Option.some.inj (by simpa [trace.bubble_eq, CRegion.parent?] using parentEq)
    apply regular
    apply trace.origin_injective
    change trace.origin region = trace.origin (trace.targetIndex wellFormed)
    change (vacuousRegionDomain input bubble).origin region =
      (vacuousRegionDomain input bubble).origin (trace.targetIndex wellFormed)
    rw [trace.targetIndex_origin]
    exact parentOrigin.symm
  simp [vacuousRegionDomain, childNeBubble]

theorem child_of_parent_ne_bubble_survives
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (child : Fin input.regionCount)
    (parentEq : (input.regions child).parent? = some trace.parent)
    (childNeBubble : child ≠ bubble) :
    (vacuousRegionDomain input bubble).survives child = true := by
  simp [vacuousRegionDomain, childNeBubble]

theorem targetKeptOccurrences_eq_mapped
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature) :
    trace.targetKeptOccurrences =
      (trace.keptOccurrences wellFormed).map trace.occurrenceMap := by
  rw [trace.targetKeptOccurrences_eq_canonical,
    trace.keptOccurrences_eq_canonical wellFormed]
  unfold canonicalTargetKeptOccurrences canonicalKeptOccurrences filterFin
  change
    (List.filter (fun node => decide ((input.nodes node).region = trace.parent))
        (allFin input.nodeCount)).map
          ConcreteElaboration.LocalOccurrence.node ++
      (List.filter (fun child => decide
        ((input.regions child).parent? = some trace.parent ∧ child ≠ bubble))
        (allFin input.regionCount)).map
          ConcreteElaboration.LocalOccurrence.child =
    (((List.filter (fun node => decide
        ((input.nodes node).region = trace.parent))
        (allFin input.nodeCount)).map
          (ConcreteElaboration.LocalOccurrence.node
            (regions := trace.sourceDiagram.regionCount)
            (nodes := trace.sourceDiagram.nodeCount))) ++
      ((List.filter (fun child => decide
        ((input.regions (trace.origin child)).parent? = some trace.parent))
        (allFin trace.sourceDiagram.regionCount)).map
          (ConcreteElaboration.LocalOccurrence.child
            (nodes := trace.sourceDiagram.nodeCount)))).map trace.occurrenceMap
  rw [map_append_vacuous]
  simp only [List.map_map, occurrenceMap, Function.comp_apply]
  dsimp only [sourceDiagram, PromoteDiagramTrace.diagram] at *
  congr 1
  change
    List.map ConcreteElaboration.LocalOccurrence.child
        (List.filter (fun child => decide
          ((input.regions child).parent? = some trace.parent ∧ child ≠ bubble))
          (allFin input.regionCount)) =
      List.map (ConcreteElaboration.LocalOccurrence.child ∘ trace.origin)
        (List.filter (fun child => decide
          ((input.regions (trace.origin child)).parent? = some trace.parent))
          (allFin (vacuousRegionDomain input bubble).count))
  rw [← List.map_map]
  apply congrArg (List.map ConcreteElaboration.LocalOccurrence.child)
  change
    List.filter (fun child => decide
      ((input.regions child).parent? = some trace.parent ∧ child ≠ bubble))
        (allFin input.regionCount) =
      List.map trace.origin
        (List.filter ((fun child => decide
          ((input.regions child).parent? = some trace.parent)) ∘ trace.origin)
          (allFin (vacuousRegionDomain input bubble).count))
  rw [← List.filter_map]
  conv =>
    rhs
    arg 2
    rw [allFin_domain_count_map_origin trace]
  unfold SurvivorDomain.enumeration filterFin
  rw [List.filter_filter]
  apply congrArg (fun predicate =>
    List.filter predicate (allFin input.regionCount))
  funext child
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨parentEq, childNeBubble⟩
    exact ⟨parentEq, trace.child_of_parent_ne_bubble_survives
      wellFormed child parentEq childNeBubble⟩
  · rintro ⟨parentEq, survives⟩
    exact ⟨parentEq,
      (vacuousRegionDomain_survives input bubble child).1 survives⟩

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
          exact False.elim ((List.nodup_cons.mp nodup).1 (by simp))

theorem targetBubbleComplement
    (trace : VacuousElimTrace input bubble raw) :
    (ConcreteElaboration.localOccurrences input trace.parent).filter
        (fun occurrence => !decide (occurrence ≠
          ConcreteElaboration.LocalOccurrence.child bubble)) =
      [ConcreteElaboration.LocalOccurrence.child bubble] := by
  apply eq_singleton_of_nodup_mem_unique
  · exact (ConcreteElaboration.localOccurrences_nodup input trace.parent).filter _
  · apply List.mem_filter.mpr
    refine ⟨?_, by simp⟩
    exact (ConcreteElaboration.mem_localOccurrences_child input trace.parent
      bubble).mpr (by simpa [trace.bubble_eq, CRegion.parent?])
  · intro occurrence member
    simpa using (List.mem_filter.mp member).2

theorem targetFocusOccurrences_perm
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature) :
    List.Perm
      ((trace.keptOccurrences wellFormed).map trace.occurrenceMap ++
        [ConcreteElaboration.LocalOccurrence.child bubble])
      (ConcreteElaboration.localOccurrences input trace.parent) := by
  have partition := List.filter_append_perm
    (fun occurrence : ConcreteElaboration.LocalOccurrence
      input.regionCount input.nodeCount =>
      decide (occurrence ≠ ConcreteElaboration.LocalOccurrence.child bubble))
    (ConcreteElaboration.localOccurrences input trace.parent)
  change List.Perm
    (trace.targetKeptOccurrences ++
      (ConcreteElaboration.localOccurrences input trace.parent).filter
        (fun occurrence => !decide (occurrence ≠
          ConcreteElaboration.LocalOccurrence.child bubble)))
    (ConcreteElaboration.localOccurrences input trace.parent) at partition
  rw [trace.targetKeptOccurrences_eq_mapped wellFormed,
    trace.targetBubbleComplement] at partition
  exact partition

theorem parentWire_mem_focusExact
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (wire : Fin input.wireCount)
    (member : wire ∈
      ConcreteElaboration.exactScopeWires input trace.parent) :
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

theorem bubbleWire_mem_focusExact
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (wire : Fin input.wireCount)
    (member : wire ∈ ConcreteElaboration.exactScopeWires input bubble) :
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
    {input : ConcreteDiagram} {bubble : Fin input.regionCount}
    {raw : ConcreteDiagram}
    {trace : VacuousElimTrace input bubble raw}
    {sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram}
    {targetContext : ConcreteElaboration.WireContext input}
    (witness : PromotedContextWitness trace sourceContext targetContext)
    (wellFormed : input.WellFormed signature) :
    PromotedContextWitness trace
      (sourceContext.extend (trace.targetIndex wellFormed))
      (targetContext.extend trace.parent) := by
  refine ⟨?_, ?_⟩
  · intro wire member
    rcases List.mem_append.mp member with outerMember | localMember
    · exact List.mem_append_left _
        (witness.target_subset_source wire outerMember)
    · exact List.mem_append_right sourceContext
        (trace.parentWire_mem_focusExact wellFormed wire localMember)
  · intro wire member
    rcases List.mem_append.mp member with outerMember | localMember
    · rcases witness.source_subset_target_or_bubble wire outerMember with
        targetMember | bubbleMember
      · exact Or.inl (List.mem_append_left _ targetMember)
      · exact Or.inr bubbleMember
    · rw [ConcreteElaboration.mem_exactScopeWires] at localMember
      rcases (trace.promotedWire_scope_eq_targetIndex_iff
        wellFormed wire).1 localMember with parentScope | bubbleScope
      · exact Or.inl (List.mem_append_right targetContext (by
          rw [ConcreteElaboration.mem_exactScopeWires]
          exact parentScope))
      · exact Or.inr
          ((ConcreteElaboration.mem_exactScopeWires input bubble wire).2
            bubbleScope)

def PromotedContextWitness.extendSelected
    {input : ConcreteDiagram} {bubble : Fin input.regionCount}
    {raw : ConcreteDiagram}
    {trace : VacuousElimTrace input bubble raw}
    {sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram}
    {targetContext : ConcreteElaboration.WireContext input}
    (witness : PromotedContextWitness trace sourceContext targetContext)
    (wellFormed : input.WellFormed signature) :
    PromotedContextWitness trace
      (sourceContext.extend (trace.targetIndex wellFormed))
      ((targetContext.extend trace.parent).extend bubble) := by
  refine ⟨?_, ?_⟩
  · intro wire member
    rcases List.mem_append.mp member with beforeBubble | bubbleLocal
    · rcases List.mem_append.mp beforeBubble with base | parentLocal
      · exact List.mem_append_left _
          (witness.target_subset_source wire base)
      · exact List.mem_append_right sourceContext
          (trace.parentWire_mem_focusExact wellFormed wire parentLocal)
    · exact List.mem_append_right sourceContext
        (trace.bubbleWire_mem_focusExact wellFormed wire bubbleLocal)
  · intro wire member
    rcases List.mem_append.mp member with base | focusLocal
    · rcases witness.source_subset_target_or_bubble wire base with
        targetMember | bubbleMember
      · exact Or.inl (List.mem_append_left _
          (List.mem_append_left _ targetMember))
      · exact Or.inl (List.mem_append_right _ bubbleMember)
    · rw [ConcreteElaboration.mem_exactScopeWires] at focusLocal
      rcases (trace.promotedWire_scope_eq_targetIndex_iff
        wellFormed wire).1 focusLocal with parentScope | bubbleScope
      · exact Or.inl (List.mem_append_left _
          (List.mem_append_right targetContext (by
            rw [ConcreteElaboration.mem_exactScopeWires]
            exact parentScope)))
      · exact Or.inl (List.mem_append_right _
          ((ConcreteElaboration.mem_exactScopeWires input bubble wire).2
            bubbleScope))

theorem PromotedContextWitness.extendSelected_source_subset_target
    {input : ConcreteDiagram} {bubble : Fin input.regionCount}
    {raw : ConcreteDiagram}
    {trace : VacuousElimTrace input bubble raw}
    {sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram}
    {targetContext : ConcreteElaboration.WireContext input}
    (witness : PromotedContextWitness trace sourceContext targetContext)
    (wellFormed : input.WellFormed signature) :
    ∀ wire, wire ∈ sourceContext.extend (trace.targetIndex wellFormed) →
      wire ∈ (targetContext.extend trace.parent).extend bubble := by
  intro wire member
  let extended := witness.extendSelected wellFormed
  rcases extended.source_subset_target_or_bubble wire member with
    targetMember | bubbleMember
  · exact targetMember
  · exact List.mem_append_right _ bubbleMember

theorem bubble_localOccurrences
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature) :
    ConcreteElaboration.localOccurrences input bubble =
      (trace.selectedOccurrences wellFormed).map trace.occurrenceMap := by
  rw [trace.selectedOccurrences_eq_canonical wellFormed]
  unfold canonicalSelectedOccurrences
    ConcreteElaboration.localOccurrences filterFin
  change
    (List.filter (fun node => decide ((input.nodes node).region = bubble))
        (allFin input.nodeCount)).map
          ConcreteElaboration.LocalOccurrence.node ++
      (List.filter (fun child => decide
        ((input.regions child).parent? = some bubble))
        (allFin input.regionCount)).map
          ConcreteElaboration.LocalOccurrence.child =
    (((List.filter (fun node => decide
        ((input.nodes node).region = bubble))
        (allFin input.nodeCount)).map
          (ConcreteElaboration.LocalOccurrence.node
            (regions := trace.sourceDiagram.regionCount)
            (nodes := trace.sourceDiagram.nodeCount))) ++
      ((List.filter (fun child => decide
        ((input.regions (trace.origin child)).parent? = some bubble))
        (allFin trace.sourceDiagram.regionCount)).map
          (ConcreteElaboration.LocalOccurrence.child
            (nodes := trace.sourceDiagram.nodeCount)))).map trace.occurrenceMap
  rw [map_append_vacuous]
  simp only [occurrenceMap_map_source_nodes,
    occurrenceMap_map_source_children]
  congr 1
  rw [← List.map_map]
  apply congrArg (List.map ConcreteElaboration.LocalOccurrence.child)
  change
    List.filter (fun child => decide
      ((input.regions child).parent? = some bubble))
        (allFin input.regionCount) =
      List.map trace.origin
        (List.filter ((fun child => decide
          ((input.regions child).parent? = some bubble)) ∘ trace.origin)
          (allFin trace.sourceDiagram.regionCount))
  rw [← List.filter_map]
  conv =>
    rhs
    arg 2
    rw [allFin_map_origin trace]
  unfold SurvivorDomain.enumeration filterFin
  rw [List.filter_filter]
  apply congrArg (fun predicate =>
    List.filter predicate (allFin input.regionCount))
  funext child
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro parentEq
    exact ⟨parentEq, trace.child_of_bubble_survives
      wellFormed child parentEq⟩
  · exact And.left

theorem regular_localOccurrences
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (region : Fin (vacuousRegionDomain input bubble).count)
    (regular : region ≠ trace.targetIndex wellFormed) :
    ConcreteElaboration.localOccurrences input (trace.origin region) =
      (ConcreteElaboration.localOccurrences trace.sourceDiagram region).map
        trace.occurrenceMap := by
  unfold ConcreteElaboration.localOccurrences filterFin
  rw [List.map_append]
  simp only [List.map_map, occurrenceMap, Function.comp_apply]
  congr 1
  · apply congrArg (List.map ConcreteElaboration.LocalOccurrence.node)
    apply congrArg (fun predicate =>
      List.filter predicate (allFin input.nodeCount))
    funext node
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact (trace.promotedNode_region_eq_regular_iff
      wellFormed node region regular).symm
  · have sourceChildren :
        List.filter (fun child : Fin trace.sourceDiagram.regionCount => decide
          ((trace.promotion.regions child).parent? = some region))
          (allFin trace.sourceDiagram.regionCount) =
        List.filter ((fun child => decide
          ((input.regions child).parent? = some (trace.origin region))) ∘
            trace.origin)
          (allFin trace.sourceDiagram.regionCount) := by
      apply congrArg (fun predicate =>
        List.filter predicate (allFin
          trace.sourceDiagram.regionCount))
      funext child
      apply Bool.eq_iff_iff.mpr
      simp only [Function.comp_apply, decide_eq_true_eq]
      exact trace.promotedRegion_parent_eq_regular_iff
        wellFormed child region regular
    change
      List.map ConcreteElaboration.LocalOccurrence.child
          (List.filter (fun child => decide
            ((input.regions child).parent? = some (trace.origin region)))
            (allFin input.regionCount)) =
        List.map (ConcreteElaboration.LocalOccurrence.child ∘ trace.origin)
          (List.filter (fun child => decide
            ((trace.promotion.regions child).parent? = some region))
            (allFin trace.sourceDiagram.regionCount))
    conv =>
      rhs
      arg 2
      rw [sourceChildren]
    rw [← List.map_map]
    apply congrArg (List.map ConcreteElaboration.LocalOccurrence.child)
    change
      List.filter (fun child => decide
        ((input.regions child).parent? = some (trace.origin region)))
          (allFin input.regionCount) =
        List.map trace.origin
          (List.filter ((fun child => decide
            ((input.regions child).parent? = some (trace.origin region))) ∘
              trace.origin)
            (allFin trace.sourceDiagram.regionCount))
    rw [← List.filter_map]
    conv =>
      rhs
      arg 2
      rw [allFin_map_origin trace]
    unfold SurvivorDomain.enumeration filterFin
    rw [List.filter_filter]
    apply congrArg (fun predicate =>
      List.filter predicate (allFin input.regionCount))
    funext child
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · intro parentEq
      exact ⟨parentEq, trace.child_of_regular_survives
        wellFormed region regular child parentEq⟩
    · exact And.left

theorem compileNode_itemSimulation
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input)
    (sourceBinders : ConcreteElaboration.BinderContext
      trace.sourceDiagram sourceRels)
    (targetBinders : ConcreteElaboration.BinderContext input targetRels)
    (binderWitness : MappedBinderWitness trace sourceBinders targetBinders)
    (node : Fin input.nodeCount)
    (regionMap : Fin (vacuousRegionDomain input bubble).count →
      Fin input.regionCount)
    (nodeShape : input.nodes node =
      match trace.sourceDiagram.nodes node with
      | .term owner freePorts term => .term (regionMap owner) freePorts term
      | .atom owner binder => .atom (regionMap owner) (trace.origin binder)
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
    regionMap trace.origin
  · cases sourceShape : trace.sourceDiagram.nodes node <;>
      simpa [sourceShape] using nodeShape
  · intro port sourceIndex targetIndex sourceResolved targetResolved
    exact trace.resolvedPorts_related wellFormed sourceContext targetContext
      node port sourceIndex targetIndex sourceResolved targetResolved
  · intro nodeOwner binder arity sourceRelation sourceAtom sourceLookup
    exact binderWitness.bindersMapped binder arity sourceRelation sourceLookup
  · exact sourceCompiled
  · exact targetCompiled

end VisualProof.Rule.VacuousElimTrace
