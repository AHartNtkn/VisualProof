import VisualProof.Concrete.Step

namespace VisualProof.Refinement.Implementation.DoubleCutElimTransport

open VisualProof
open VisualProof.Concrete
open VisualProof.Data.Finite
open VisualProof.Diagram

abbrev Domain (input : Concrete.Diagram)
    (outer inner : Fin input.regionCount) :=
  Concrete.doubleCutRegionDomain input outer inner

@[simp] theorem domain_survives_iff
    (input : Concrete.Diagram) (outer inner region : Fin input.regionCount) :
    (Domain input outer inner).survives region = true ↔
      region ≠ outer ∧ region ≠ inner := by
  simp [Domain, Concrete.doubleCutRegionDomain]

theorem outer_ne_inner
    (input : Concrete.Diagram) (wellFormed : input.WellFormed)
    {outer inner : Fin input.regionCount}
    (innerEq : input.regions inner = .cut outer) :
    outer ≠ inner := by
  intro equality
  subst inner
  have parent : (input.regions outer).parent? = some outer := by
    rw [innerEq]
    rfl
  exact Concrete.Elaboration.checked_direct_child_not_encloses_parent
    wellFormed parent (Concrete.Diagram.Encloses.refl input outer)

theorem target_ne_outer
    (input : Concrete.Diagram) (wellFormed : input.WellFormed)
    {outer target : Fin input.regionCount}
    (outerEq : input.regions outer = .cut target) :
    target ≠ outer := by
  intro equality
  subst target
  have parent : (input.regions outer).parent? = some outer := by
    rw [outerEq]
    rfl
  exact Concrete.Elaboration.checked_direct_child_not_encloses_parent
    wellFormed parent (Concrete.Diagram.Encloses.refl input outer)

theorem target_ne_inner
    (input : Concrete.Diagram) (wellFormed : input.WellFormed)
    {outer inner target : Fin input.regionCount}
    (outerEq : input.regions outer = .cut target)
    (innerEq : input.regions inner = .cut outer) :
    target ≠ inner := by
  intro equality
  subst target
  have innerParent : (input.regions inner).parent? = some outer := by
    rw [innerEq]
    rfl
  have outerParent : (input.regions outer).parent? = some inner := by
    rw [outerEq]
    rfl
  have innerEnclosesOuter : input.Encloses inner outer := by
    refine ⟨⟨1, by have := outer.isLt; omega⟩, ?_⟩
    simp [Concrete.Diagram.climb, outerParent]
  exact Concrete.Elaboration.checked_direct_child_not_encloses_parent
    wellFormed innerParent innerEnclosesOuter

theorem target_survives
    (input : Concrete.Diagram) (wellFormed : input.WellFormed)
    {outer inner target : Fin input.regionCount}
    (outerEq : input.regions outer = .cut target)
    (innerEq : input.regions inner = .cut outer) :
    (Domain input outer inner).survives target = true := by
  exact (domain_survives_iff input outer inner target).2
    ⟨target_ne_outer input wellFormed outerEq,
      target_ne_inner input wellFormed outerEq innerEq⟩

/-- Restore the two eliminated region identifiers after the compact survivor
carrier.  This is the exact carrier comparison used by elimination proofs. -/
noncomputable def restoreRegionEquiv
    (input : Concrete.Diagram) (wellFormed : input.WellFormed)
    {outer inner target : Fin input.regionCount}
    (_outerEq : input.regions outer = .cut target)
    (innerEq : input.regions inner = .cut outer) :
    FiniteEquiv (Fin ((Domain input outer inner).count + 2))
      (Fin input.regionCount) where
  toFun := Fin.addCases (Domain input outer inner).origin
    (Fin.cases outer (fun _ => inner))
  invFun := fun region =>
    if outerCase : region = outer then
      Fin.natAdd (Domain input outer inner).count (0 : Fin 2)
    else if innerCase : region = inner then
      Fin.natAdd (Domain input outer inner).count (1 : Fin 2)
    else
      Fin.castAdd 2 ((Domain input outer inner).index region (by
        exact (domain_survives_iff input outer inner region).2
          ⟨outerCase, innerCase⟩))
  left_inv := by
    intro region
    refine Fin.addCases (fun survivor => ?_) (fun removed => ?_) region
    · have survives := (Domain input outer inner).origin_survives survivor
      have outerNe : (Domain input outer inner).origin survivor ≠ outer :=
        (domain_survives_iff input outer inner _).1 survives |>.1
      have innerNe : (Domain input outer inner).origin survivor ≠ inner :=
        (domain_survives_iff input outer inner _).1 survives |>.2
      simp only [Fin.addCases_left]
      rw [dif_neg outerNe, dif_neg innerNe]
      exact congrArg (Fin.castAdd 2)
        ((Domain input outer inner).index_origin survivor)
    · refine Fin.cases ?_ (fun one => ?_) removed
      · simp only [Fin.addCases_right, Fin.cases_zero]
        simp
      · have oneEq : one = 0 := by
          apply Fin.ext
          omega
        subst one
        simp only [Fin.addCases_right, Fin.cases_succ]
        rw [dif_neg (outer_ne_inner input wellFormed innerEq).symm]
        simp
  right_inv := by
    intro region
    by_cases outerCase : region = outer
    · subst region
      rw [dif_pos rfl]
      simp only [Fin.addCases_right, Fin.cases_zero]
    · rw [dif_neg outerCase]
      by_cases innerCase : region = inner
      · subst region
        rw [dif_pos rfl]
        simp only [Fin.addCases_right]
        have one : (1 : Fin 2) = Fin.succ (0 : Fin 1) := by
          apply Fin.ext
          rfl
        rw [one, Fin.cases_succ]
      · rw [dif_neg innerCase]
        simp only [Fin.addCases_left]
        exact (Domain input outer inner).origin_index region
          ((domain_survives_iff input outer inner region).2
            ⟨outerCase, innerCase⟩)

@[simp] theorem restoreRegionEquiv_survivor
    (input : Concrete.Diagram) (wellFormed : input.WellFormed)
    {outer inner target : Fin input.regionCount}
    (outerEq : input.regions outer = .cut target)
    (innerEq : input.regions inner = .cut outer)
    (region : Fin (Domain input outer inner).count) :
    restoreRegionEquiv input wellFormed outerEq innerEq
        (Fin.castAdd 2 region) =
      (Domain input outer inner).origin region := by
  simp [restoreRegionEquiv]

@[simp] theorem restoreRegionEquiv_outer
    (input : Concrete.Diagram) (wellFormed : input.WellFormed)
    {outer inner target : Fin input.regionCount}
    (outerEq : input.regions outer = .cut target)
    (innerEq : input.regions inner = .cut outer) :
    restoreRegionEquiv input wellFormed outerEq innerEq
        (Fin.natAdd (Domain input outer inner).count (0 : Fin 2)) = outer := by
  simp [restoreRegionEquiv]

@[simp] theorem restoreRegionEquiv_inner
    (input : Concrete.Diagram) (wellFormed : input.WellFormed)
    {outer inner target : Fin input.regionCount}
    (outerEq : input.regions outer = .cut target)
    (innerEq : input.regions inner = .cut outer) :
    restoreRegionEquiv input wellFormed outerEq innerEq
        (Fin.natAdd (Domain input outer inner).count (1 : Fin 2)) = inner := by
  simp only [restoreRegionEquiv, Fin.addCases_right]
  have one : (1 : Fin 2) = Fin.succ (0 : Fin 1) := by
    apply Fin.ext
    rfl
  rw [one, Fin.cases_succ]

/-- Compact identifier of the region that receives the promoted inner body. -/
def promotedTarget
    (input : Concrete.Diagram) (wellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw) :
    Fin (Domain input outer trace.inner).count :=
  (Domain input outer trace.inner).index trace.target
    (target_survives input wellFormed trace.outer_eq trace.inner_eq)

@[simp] theorem promotedTarget_origin
    (input : Concrete.Diagram) (wellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw) :
    (Domain input outer trace.inner).origin
        (promotedTarget input wellFormed trace) = trace.target := by
  exact (Domain input outer trace.inner).origin_index trace.target
    (target_survives input wellFormed trace.outer_eq trace.inner_eq)

theorem origin_ne_outer
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (region : Fin (Domain input outer trace.inner).count) :
    (Domain input outer trace.inner).origin region ≠ outer := by
  exact (domain_survives_iff input outer trace.inner _).1
    ((Domain input outer trace.inner).origin_survives region) |>.1

theorem origin_ne_inner
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (region : Fin (Domain input outer trace.inner).count) :
    (Domain input outer trace.inner).origin region ≠ trace.inner := by
  exact (domain_survives_iff input outer trace.inner _).1
    ((Domain input outer trace.inner).origin_survives region) |>.2

theorem child_of_outer_eq_inner
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (region : Fin input.regionCount)
    (parent : (input.regions region).parent? = some outer) :
    region = trace.inner := by
  have member : region ∈ filterFin (fun candidate =>
      decide ((input.regions candidate).parent? = some outer)) := by
    rw [mem_filterFin]
    exact decide_eq_true parent
  rw [trace.children_eq] at member
  simpa using member

theorem node_region_ne_outer
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (node : Fin input.nodeCount) :
    (input.nodes node).region ≠ outer := by
  intro equality
  have empty : (filterFin fun candidate =>
      decide ((input.nodes candidate).region = outer)) = [] :=
    List.isEmpty_iff.mp trace.outer_nodes_empty
  have member : node ∈ filterFin (fun candidate =>
      decide ((input.nodes candidate).region = outer)) := by
    rw [mem_filterFin]
    exact decide_eq_true equality
  rw [empty] at member
  exact List.not_mem_nil member

theorem wire_scope_ne_outer
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (wire : Fin input.wireCount) :
    (input.wires wire).scope ≠ outer := by
  intro equality
  have empty : (filterFin fun candidate =>
      decide ((input.wires candidate).scope = outer)) = [] :=
    List.isEmpty_iff.mp trace.outer_wires_empty
  have member : wire ∈ filterFin (fun candidate =>
      decide ((input.wires candidate).scope = outer)) := by
    rw [mem_filterFin]
    exact decide_eq_true equality
  rw [empty] at member
  exact List.not_mem_nil member

def promoteRegionIndex
    (input : Concrete.Diagram) (wellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (region : Fin input.regionCount) (outerNe : region ≠ outer) :
    Fin (Domain input outer trace.inner).count :=
  if innerCase : region = trace.inner then
    promotedTarget input wellFormed trace
  else
    (Domain input outer trace.inner).index region
      ((domain_survives_iff input outer trace.inner region).2
        ⟨outerNe, innerCase⟩)

theorem promoteRegionIndex_origin
    (input : Concrete.Diagram) (wellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (region : Fin input.regionCount) (outerNe : region ≠ outer) :
    (Domain input outer trace.inner).origin
        (promoteRegionIndex input wellFormed trace region outerNe) =
      if region = trace.inner then trace.target else region := by
  by_cases innerCase : region = trace.inner
  · subst region
    simp only [promoteRegionIndex]
    exact promotedTarget_origin input wellFormed trace
  · simp only [promoteRegionIndex, dif_neg innerCase, if_neg innerCase]
    exact (Domain input outer trace.inner).origin_index region _

def promotedWireValue
    (input : Concrete.Diagram) (wellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (wire : Fin input.wireCount) :
    Concrete.CWire (Domain input outer trace.inner).count input.nodeCount := {
  scope := promoteRegionIndex input wellFormed trace
    (input.wires wire).scope (wire_scope_ne_outer trace wire)
  endpoints := (input.wires wire).endpoints
}

theorem promotion_wire
    (input : Concrete.Diagram) (wellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (wire : Fin input.wireCount) :
    trace.promotion.wires wire =
      promotedWireValue input wellFormed trace wire := by
  have result := trace.promotion.wire_result wire
  apply Option.some.inj
  rw [← result]
  unfold Concrete.promoteWire? promotedWireValue promoteRegionIndex
  by_cases innerCase : (input.wires wire).scope = trace.inner
  · simp only [if_pos innerCase]
    rw [(Domain input outer trace.inner).index?_index trace.target
      (target_survives input wellFormed trace.outer_eq trace.inner_eq)]
    simp [promotedTarget, innerCase]
  · simp only [if_neg innerCase]
    rw [(Domain input outer trace.inner).index?_index
      (input.wires wire).scope
      ((domain_survives_iff input outer trace.inner _).2
        ⟨wire_scope_ne_outer trace wire, innerCase⟩)]
    simp [innerCase]

theorem survivor_parent_ne_outer
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (region : Fin (Domain input outer trace.inner).count)
    (parent : Fin input.regionCount)
    (parentEq : (input.regions
      ((Domain input outer trace.inner).origin region)).parent? = some parent) :
    parent ≠ outer := by
  intro equality
  subst parent
  exact origin_ne_inner trace region
    (child_of_outer_eq_inner trace _ parentEq)

def promotedRegionValue
    (input : Concrete.Diagram) (wellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (region : Fin (Domain input outer trace.inner).count) :
    Concrete.CRegion (Domain input outer trace.inner).count :=
  match regionEq : input.regions
      ((Domain input outer trace.inner).origin region) with
  | .sheet => .sheet
  | .cut parent =>
      .cut (promoteRegionIndex input wellFormed trace parent
        (survivor_parent_ne_outer trace region parent (by
          rw [regionEq]
          rfl)))
  | .bubble parent arity =>
      .bubble (promoteRegionIndex input wellFormed trace parent
        (survivor_parent_ne_outer trace region parent (by
          rw [regionEq]
          rfl))) arity

theorem promotion_region
    (input : Concrete.Diagram) (wellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (region : Fin (Domain input outer trace.inner).count) :
    trace.promotion.regions region =
      promotedRegionValue input wellFormed trace region := by
  have result := trace.promotion.region_result region
  apply Option.some.inj
  rw [← result]
  unfold promotedRegionValue
  split
  · rename_i regionEq
    simp only [regionEq, Concrete.promoteRegion?]
  · rename_i parent regionEq
    simp only [regionEq, Concrete.promoteRegion?]
    unfold promoteRegionIndex
    by_cases innerCase : parent = trace.inner
    · simp only [if_pos innerCase]
      rw [(Domain input outer trace.inner).index?_index trace.target
        (target_survives input wellFormed trace.outer_eq trace.inner_eq)]
      simp [promotedTarget, innerCase]
      congr
    · simp only [if_neg innerCase]
      rw [(Domain input outer trace.inner).index?_index parent
        ((domain_survives_iff input outer trace.inner parent).2
          ⟨survivor_parent_ne_outer trace region parent (by
              rw [regionEq]
              rfl), innerCase⟩)]
      simp [innerCase]
      congr
  · rename_i parent arity regionEq
    simp only [regionEq, Concrete.promoteRegion?]
    unfold promoteRegionIndex
    by_cases innerCase : parent = trace.inner
    · simp only [if_pos innerCase]
      rw [(Domain input outer trace.inner).index?_index trace.target
        (target_survives input wellFormed trace.outer_eq trace.inner_eq)]
      simp [promotedTarget, innerCase]
      congr
    · simp only [if_neg innerCase]
      rw [(Domain input outer trace.inner).index?_index parent
        ((domain_survives_iff input outer trace.inner parent).2
          ⟨survivor_parent_ne_outer trace region parent (by
              rw [regionEq]
              rfl), innerCase⟩)]
      simp [innerCase]
      congr

theorem atom_binder_ne_outer
    (input : Concrete.Diagram) (wellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (node : Fin input.nodeCount) (owner binder : Fin input.regionCount)
    (nodeEq : input.nodes node = .atom owner binder) :
    binder ≠ outer := by
  obtain ⟨parent, arity, bubbleEq⟩ := by
    simpa [Concrete.Diagram.AtomBindersAreBubbles, nodeEq] using
      wellFormed.atom_binders_are_bubbles node
  intro equality
  subst binder
  rw [trace.outer_eq] at bubbleEq
  cases bubbleEq

theorem atom_binder_ne_inner
    (input : Concrete.Diagram) (wellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (node : Fin input.nodeCount) (owner binder : Fin input.regionCount)
    (nodeEq : input.nodes node = .atom owner binder) :
    binder ≠ trace.inner := by
  obtain ⟨parent, arity, bubbleEq⟩ := by
    simpa [Concrete.Diagram.AtomBindersAreBubbles, nodeEq] using
      wellFormed.atom_binders_are_bubbles node
  intro equality
  subst binder
  rw [trace.inner_eq] at bubbleEq
  cases bubbleEq

def promotedNodeValue
    (input : Concrete.Diagram) (wellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (node : Fin input.nodeCount) :
    Concrete.CNode (Domain input outer trace.inner).count :=
  match nodeEq : input.nodes node with
  | .identity owner arity =>
      .identity (promoteRegionIndex input wellFormed trace owner
        (by simpa [nodeEq] using node_region_ne_outer trace node)) arity
  | .atom owner binder =>
      .atom (promoteRegionIndex input wellFormed trace owner
          (by simpa [nodeEq] using node_region_ne_outer trace node))
        ((Domain input outer trace.inner).index binder
          ((domain_survives_iff input outer trace.inner binder).2
            ⟨atom_binder_ne_outer input wellFormed trace node owner binder
                nodeEq,
              atom_binder_ne_inner input wellFormed trace node owner binder
                nodeEq⟩))

theorem promotion_node
    (input : Concrete.Diagram) (wellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (node : Fin input.nodeCount) :
    trace.promotion.nodes node =
      promotedNodeValue input wellFormed trace node := by
  have result := trace.promotion.node_result node
  apply Option.some.inj
  rw [← result]
  unfold promotedNodeValue
  split
  · rename_i owner arity nodeEq
    have ownerNe : owner ≠ outer := by
      simpa [nodeEq] using node_region_ne_outer trace node
    simp only [nodeEq, Concrete.promoteNode?]
    unfold promoteRegionIndex
    by_cases innerCase : owner = trace.inner
    · simp only [if_pos innerCase]
      rw [(Domain input outer trace.inner).index?_index trace.target
        (target_survives input wellFormed trace.outer_eq trace.inner_eq)]
      simp [promotedTarget, innerCase]
      congr
    · simp only [if_neg innerCase]
      rw [(Domain input outer trace.inner).index?_index owner
        ((domain_survives_iff input outer trace.inner owner).2
          ⟨ownerNe, innerCase⟩)]
      simp [innerCase]
      congr
  · rename_i owner binder nodeEq
    have ownerNe : owner ≠ outer := by
      simpa [nodeEq] using node_region_ne_outer trace node
    simp only [nodeEq, Concrete.promoteNode?]
    unfold promoteRegionIndex
    by_cases innerCase : owner = trace.inner
    · simp only [if_pos innerCase]
      rw [(Domain input outer trace.inner).index?_index trace.target
        (target_survives input wellFormed trace.outer_eq trace.inner_eq)]
      rw [(Domain input outer trace.inner).index?_index binder
        ((domain_survives_iff input outer trace.inner binder).2
          ⟨atom_binder_ne_outer input wellFormed trace node owner binder nodeEq,
            atom_binder_ne_inner input wellFormed trace node owner binder nodeEq⟩)]
      simp [promotedTarget, innerCase]
    · simp only [if_neg innerCase]
      rw [(Domain input outer trace.inner).index?_index owner
        ((domain_survives_iff input outer trace.inner owner).2
          ⟨ownerNe, innerCase⟩)]
      rw [(Domain input outer trace.inner).index?_index binder
        ((domain_survives_iff input outer trace.inner binder).2
          ⟨atom_binder_ne_outer input wellFormed trace node owner binder nodeEq,
            atom_binder_ne_inner input wellFormed trace node owner binder nodeEq⟩)]
      simp [innerCase]

abbrev Target
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw) : Concrete.Diagram :=
  trace.promotion.diagram

@[simp] theorem target_regionCount
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw) :
    (Target trace).regionCount = (Domain input outer trace.inner).count := rfl

@[simp] theorem target_nodeCount
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw) :
    (Target trace).nodeCount = input.nodeCount := rfl

@[simp] theorem target_wireCount
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw) :
    (Target trace).wireCount = input.wireCount := rfl

@[simp] theorem target_wire
    (input : Concrete.Diagram) (wellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (wire : Fin input.wireCount) :
    (Target trace).wires wire =
      promotedWireValue input wellFormed trace wire := by
  exact promotion_wire input wellFormed trace wire

theorem target_wire_scope
    (input : Concrete.Diagram) (wellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (wire : Fin input.wireCount) :
    ((Target trace).wires wire).scope =
      promoteRegionIndex input wellFormed trace
        (input.wires wire).scope (wire_scope_ne_outer trace wire) := by
  rw [target_wire]
  rfl

theorem target_scope_iff
    (input : Concrete.Diagram) (wellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (wire : Fin input.wireCount) :
    ((Target trace).wires wire).scope =
        promotedTarget input wellFormed trace ↔
      (input.wires wire).scope = trace.target ∨
        (input.wires wire).scope = trace.inner := by
  rw [target_wire_scope input wellFormed trace wire]
  constructor
  · intro equality
    have origins := congrArg (Domain input outer trace.inner).origin equality
    rw [promoteRegionIndex_origin, promotedTarget_origin] at origins
    by_cases innerCase : (input.wires wire).scope = trace.inner
    · exact Or.inr innerCase
    · exact Or.inl (by simpa [innerCase] using origins)
  · intro cases
    rcases cases with targetCase | innerCase
    · have targetNeInner : trace.target ≠ trace.inner :=
        target_ne_inner input wellFormed trace.outer_eq trace.inner_eq
      unfold promoteRegionIndex
      have scopeNeInner : (input.wires wire).scope ≠ trace.inner := by
        intro equality
        exact targetNeInner (targetCase.symm.trans equality)
      rw [dif_neg scopeNeInner]
      apply (Domain input outer trace.inner).origin_injective
      rw [(Domain input outer trace.inner).origin_index,
        promotedTarget_origin, targetCase]
    ·
      unfold promoteRegionIndex
      rw [dif_pos innerCase]

def targetExactWires
    (input : Concrete.Diagram) (wellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw) :
    Concrete.Elaboration.WireContext (Target trace) :=
  Concrete.Elaboration.exactScopeWires (Target trace)
    (promotedTarget input wellFormed trace)

def sourceHostWires
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw) :
    Concrete.Elaboration.WireContext input :=
  Concrete.Elaboration.exactScopeWires input trace.target

def sourceInnerWires
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw) :
    Concrete.Elaboration.WireContext input :=
  Concrete.Elaboration.exactScopeWires input trace.inner

theorem mem_targetExactWires_iff
    (input : Concrete.Diagram) (wellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (wire : Fin input.wireCount) :
    wire ∈ targetExactWires input wellFormed trace ↔
      wire ∈ sourceHostWires trace ∨ wire ∈ sourceInnerWires trace := by
  have targetMem : wire ∈ targetExactWires input wellFormed trace ↔
      ((Target trace).wires wire).scope =
        promotedTarget input wellFormed trace := by
    simpa [targetExactWires] using
      (Concrete.Elaboration.mem_exactScopeWires (Target trace)
        (promotedTarget input wellFormed trace) wire)
  have hostMem : wire ∈ sourceHostWires trace ↔
      (input.wires wire).scope = trace.target := by
    simp [sourceHostWires]
  have innerMem : wire ∈ sourceInnerWires trace ↔
      (input.wires wire).scope = trace.inner := by
    simp [sourceInnerWires]
  rw [targetMem, hostMem, innerMem]
  exact target_scope_iff input wellFormed trace wire

theorem source_exact_wires_disjoint
    (input : Concrete.Diagram) (wellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw) :
    List.Pairwise (fun left right => left ≠ right)
      (sourceHostWires trace ++ sourceInnerWires trace) := by
  exact Concrete.Elaboration.WireContext.exactScopeWires_disjoint
    (target_ne_inner input wellFormed trace.outer_eq trace.inner_eq)

noncomputable def exactWireEquiv
    (input : Concrete.Diagram) (wellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw) :
    FiniteEquiv
      (Fin (sourceHostWires trace ++ sourceInnerWires trace).length)
      (Fin (targetExactWires input wellFormed trace).length) :=
  FiniteEquiv.restrictLists (FiniteEquiv.refl (Fin input.wireCount))
    (sourceHostWires trace ++ sourceInnerWires trace)
    (targetExactWires input wellFormed trace)
    (source_exact_wires_disjoint input wellFormed trace)
    (Concrete.Elaboration.exactScopeWires_nodup (Target trace)
      (promotedTarget input wellFormed trace)) (by
        intro wire
        simp only [FiniteEquiv.refl_apply, List.mem_append]
        exact mem_targetExactWires_iff input wellFormed trace wire)

theorem exactWireEquiv_spec
    (input : Concrete.Diagram) (wellFormed : input.WellFormed)
    {outer : Fin input.regionCount} {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (index : Fin (sourceHostWires trace ++ sourceInnerWires trace).length) :
    (targetExactWires input wellFormed trace).get
        (exactWireEquiv input wellFormed trace index) =
      (sourceHostWires trace ++ sourceInnerWires trace).get index := by
  exact FiniteEquiv.restrictLists_spec
    (FiniteEquiv.refl (Fin input.wireCount))
    (sourceHostWires trace ++ sourceInnerWires trace)
    (targetExactWires input wellFormed trace)
    (source_exact_wires_disjoint input wellFormed trace)
    (Concrete.Elaboration.exactScopeWires_nodup (Target trace)
      (promotedTarget input wellFormed trace)) (by
        intro wire
        simp only [FiniteEquiv.refl_apply, List.mem_append]
        exact mem_targetExactWires_iff input wellFormed trace wire) index

def rawRegion
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (region : Fin (Domain input outer trace.inner).count) :
    Fin raw.regionCount :=
  Fin.cast trace.promotion.raw_regionCount.symm region

def rawNode
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (node : Fin input.nodeCount) : Fin raw.nodeCount :=
  Fin.cast trace.promotion.raw_nodeCount.symm node

def rawWire
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (wire : Fin input.wireCount) : Fin raw.wireCount :=
  Fin.cast trace.promotion.raw_wireCount.symm wire

theorem rawRegion_injective
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw) :
    Function.Injective (rawRegion trace) := by
  intro left right equality
  apply Fin.ext
  exact congrArg (fun value : Fin raw.regionCount => value.val) equality

theorem rawNode_injective
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw) :
    Function.Injective (rawNode trace) := by
  intro left right equality
  apply Fin.ext
  exact congrArg (fun value : Fin raw.nodeCount => value.val) equality

theorem rawWire_injective
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw) :
    Function.Injective (rawWire trace) := by
  intro left right equality
  apply Fin.ext
  exact congrArg (fun value : Fin raw.wireCount => value.val) equality

@[simp] theorem rawRegion_val
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (region : Fin (Domain input outer trace.inner).count) :
    (rawRegion trace region).val = region.val := rfl

@[simp] theorem rawNode_val
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (node : Fin input.nodeCount) :
    (rawNode trace node).val = node.val := rfl

@[simp] theorem rawWire_val
    {input : Concrete.Diagram} {outer : Fin input.regionCount}
    {raw : Concrete.Diagram}
    (trace : Concrete.DoubleCutElimTrace input outer raw)
    (wire : Fin input.wireCount) :
    (rawWire trace wire).val = wire.val := rfl

end VisualProof.Refinement.Implementation.DoubleCutElimTransport
