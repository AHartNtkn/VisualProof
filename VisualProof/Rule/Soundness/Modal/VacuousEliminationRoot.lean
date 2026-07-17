import VisualProof.Rule.Soundness.Modal.VacuousEliminationSimulation

namespace VisualProof.Rule.VacuousElimTrace

open VisualProof
open VisualProof.Theory
open VisualProof.Diagram
open VisualProof.Rule.DoubleCutElimTrace

def sourceOpen
    (trace : VacuousElimTrace input bubble raw)
    (boundary : List (Fin input.wireCount)) : OpenConcreteDiagram where
  diagram := trace.sourceDiagram
  boundary := boundary

def targetOpen (input : ConcreteDiagram)
    (boundary : List (Fin input.wireCount)) : OpenConcreteDiagram where
  diagram := input
  boundary := boundary

@[simp] theorem sourceOpen_exposedWires
    (trace : VacuousElimTrace input bubble raw)
    (boundary : List (Fin input.wireCount)) :
    (trace.sourceOpen boundary).exposedWires =
      (targetOpen input boundary).exposedWires := rfl

theorem targetRoot_scope_promoted
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (wire : Fin input.wireCount)
    (scope : (input.wires wire).scope = input.root) :
    (trace.sourceDiagram.wires wire).scope = trace.sourceDiagram.root := by
  by_cases focused : trace.sourceDiagram.root =
      trace.targetIndex wellFormed
  · have parentRoot : trace.parent = input.root := by
      calc
        trace.parent = trace.origin (trace.targetIndex wellFormed) :=
          (trace.targetIndex_origin wellFormed).symm
        _ = trace.origin trace.sourceDiagram.root :=
          congrArg trace.origin focused.symm
        _ = input.root := trace.promotion.root_origin
    rw [focused]
    exact (trace.promotedWire_scope_eq_targetIndex_iff wellFormed wire).2
      (Or.inl (scope.trans parentRoot.symm))
  · exact (trace.promotedWire_scope_eq_regular_iff wellFormed wire
      trace.sourceDiagram.root focused).2
      (scope.trans trace.promotion.root_origin.symm)

theorem promotedRoot_scope_parent_or_bubble
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (wire : Fin input.wireCount)
    (scope :
      (trace.sourceDiagram.wires wire).scope = trace.sourceDiagram.root) :
    (input.wires wire).scope = input.root ∨
      (input.wires wire).scope = bubble := by
  by_cases focused : trace.sourceDiagram.root =
      trace.targetIndex wellFormed
  · have parentRoot : trace.parent = input.root := by
      calc
        trace.parent = trace.origin (trace.targetIndex wellFormed) :=
          (trace.targetIndex_origin wellFormed).symm
        _ = trace.origin trace.sourceDiagram.root :=
          congrArg trace.origin focused.symm
        _ = input.root := trace.promotion.root_origin
    have atFocus :=
      (trace.promotedWire_scope_eq_targetIndex_iff wellFormed wire).1
        (scope.trans focused)
    exact atFocus.imp (fun atParent => atParent.trans parentRoot)
      (fun atBubble => atBubble)
  · exact Or.inl ((trace.promotedWire_scope_eq_regular_iff wellFormed wire
      trace.sourceDiagram.root focused).1 scope |>.trans
        trace.promotion.root_origin)

theorem sourceOpen_wellFormed
    (trace : VacuousElimTrace input bubble raw)
    (sourceWellFormed : trace.sourceDiagram.WellFormed signature)
    (targetWellFormed : input.WellFormed signature)
    (boundary : List (Fin input.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.wires wire).scope = input.root) :
    (trace.sourceOpen boundary).WellFormed signature := by
  refine ⟨sourceWellFormed, ?_⟩
  intro wire member
  exact trace.targetRoot_scope_promoted targetWellFormed wire
    (boundaryRoot wire member)

theorem targetOpen_wellFormed
    (wellFormed : input.WellFormed signature)
    (boundary : List (Fin input.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.wires wire).scope = input.root) :
    (targetOpen input boundary).WellFormed signature :=
  ⟨wellFormed, boundaryRoot⟩

def rootContextWitness
    (trace : VacuousElimTrace input bubble raw)
    (sourceWellFormed : trace.sourceDiagram.WellFormed signature)
    (targetWellFormed : input.WellFormed signature)
    (boundary : List (Fin input.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.wires wire).scope = input.root) :
    PromotedContextWitness trace
      (trace.sourceOpen boundary).rootWires
      (targetOpen input boundary).rootWires := by
  let source : CheckedOpenDiagram signature :=
    ⟨trace.sourceOpen boundary,
      trace.sourceOpen_wellFormed sourceWellFormed targetWellFormed boundary
        boundaryRoot⟩
  let target : CheckedOpenDiagram signature :=
    ⟨targetOpen input boundary,
      targetOpen_wellFormed targetWellFormed boundary boundaryRoot⟩
  refine ⟨?_, ?_⟩
  · intro wire member
    have targetScope :=
      (OpenConcreteDiagram.mem_rootWires_iff target.val target.property wire).1
        member
    have sourceScope := trace.targetRoot_scope_promoted targetWellFormed wire
      targetScope
    exact (OpenConcreteDiagram.mem_rootWires_iff source.val source.property
      wire).2 sourceScope
  · intro wire member
    have sourceScope :=
      (OpenConcreteDiagram.mem_rootWires_iff source.val source.property wire).1
        member
    rcases trace.promotedRoot_scope_parent_or_bubble targetWellFormed wire
      sourceScope with targetScope | bubbleScope
    · exact Or.inl ((OpenConcreteDiagram.mem_rootWires_iff target.val
        target.property wire).2 targetScope)
    · exact Or.inr ((ConcreteElaboration.mem_exactScopeWires input bubble
        wire).2 bubbleScope)

theorem sourceOpen_hiddenWires_eq_of_regular
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (boundary : List (Fin input.wireCount))
    (regular : trace.sourceDiagram.root ≠ trace.targetIndex wellFormed) :
    (trace.sourceOpen boundary).hiddenWires =
      (targetOpen input boundary).hiddenWires := by
  unfold OpenConcreteDiagram.hiddenWires sourceOpen targetOpen
  rw [trace.regular_exactScopeWires wellFormed trace.sourceDiagram.root
    regular]
  have rootOrigin : trace.origin trace.sourceDiagram.root = input.root :=
    trace.promotion.root_origin
  rw [rootOrigin]
  rfl

def PromotedContextWitness.extendRootSelected
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input)
    (context : PromotedContextWitness trace sourceContext targetContext)
    (sourceExact : sourceContext.Exact (trace.targetIndex wellFormed)) :
    PromotedContextWitness trace sourceContext
      (targetContext.extend bubble) := by
  refine ⟨?_, ?_⟩
  · intro wire member
    rcases List.mem_append.mp member with targetMember | bubbleMember
    · exact context.target_subset_source wire targetMember
    · have focusMember := trace.bubbleWire_mem_focusExact wellFormed wire
          bubbleMember
      have scope := (ConcreteElaboration.mem_exactScopeWires
        trace.sourceDiagram (trace.targetIndex wellFormed) wire).1 focusMember
      exact (sourceExact.mem_iff wire).2 (by
        rw [scope]
        exact ConcreteDiagram.Encloses.refl _ _)
  · intro wire member
    rcases context.source_subset_target_or_bubble wire member with
      targetMember | bubbleMember
    · exact Or.inl (List.mem_append_left _ targetMember)
    · exact Or.inl (List.mem_append_right _ bubbleMember)

theorem PromotedContextWitness.extendRootSelected_source_subset_target
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input)
    (context : PromotedContextWitness trace sourceContext targetContext)
    (sourceExact : sourceContext.Exact (trace.targetIndex wellFormed)) :
    ∀ wire, wire ∈ sourceContext → wire ∈ targetContext.extend bubble := by
  intro wire member
  exact (context.extendRootSelected trace wellFormed sourceContext
    targetContext sourceExact).source_subset_target_or_bubble wire member |>.elim
      id (fun bubbleMember => List.mem_append_right _ bubbleMember)

theorem targetRootSelected_exact
    (trace : VacuousElimTrace input bubble raw)
    (wellFormed : input.WellFormed signature)
    (targetContext : ConcreteElaboration.WireContext input)
    (targetExact : targetContext.Exact trace.parent) :
    (targetContext.extend bubble).Exact bubble := by
  exact targetExact.extend_child wellFormed (by
    simpa [trace.bubble_eq, CRegion.parent?])

end VisualProof.Rule.VacuousElimTrace
