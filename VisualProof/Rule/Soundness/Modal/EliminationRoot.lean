import VisualProof.Rule.Soundness.Modal.EliminationSimulation

namespace VisualProof.Rule.DoubleCutElimTrace

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram

def sourceOpen
    (trace : DoubleCutElimTrace input outer raw)
    (boundary : List (Fin input.wireCount)) : OpenConcreteDiagram where
  diagram := trace.sourceDiagram
  boundary := boundary

def targetOpen (input : ConcreteDiagram)
    (boundary : List (Fin input.wireCount)) : OpenConcreteDiagram where
  diagram := input
  boundary := boundary

@[simp] theorem sourceOpen_exposedWires
    (trace : DoubleCutElimTrace input outer raw)
    (boundary : List (Fin input.wireCount)) :
    (trace.sourceOpen boundary).exposedWires =
      (targetOpen input boundary).exposedWires := rfl

theorem targetRoot_scope_promoted
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (wire : Fin input.wireCount)
    (scope : (input.wires wire).scope = input.root) :
    (trace.sourceDiagram.wires wire).scope = trace.sourceDiagram.root := by
  by_cases focused : trace.sourceDiagram.root =
      trace.targetIndex wellFormed
  · have targetRoot : trace.target = input.root := by
      calc
        trace.target = trace.origin (trace.targetIndex wellFormed) :=
          (trace.targetIndex_origin wellFormed).symm
        _ = trace.origin trace.sourceDiagram.root :=
          congrArg trace.origin focused.symm
        _ = input.root := trace.promotion.root_origin
    rw [focused]
    exact (trace.promotedWire_scope_eq_targetIndex_iff wellFormed wire).2
      (Or.inl (scope.trans targetRoot.symm))
  · exact (trace.promotedWire_scope_eq_regular_iff wellFormed wire
      trace.sourceDiagram.root focused).2
      (scope.trans trace.promotion.root_origin.symm)

theorem promotedRoot_scope_target_or_inner
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (wire : Fin input.wireCount)
    (scope :
      (trace.sourceDiagram.wires wire).scope = trace.sourceDiagram.root) :
    (input.wires wire).scope = input.root ∨
      (input.wires wire).scope = trace.inner := by
  by_cases focused : trace.sourceDiagram.root =
      trace.targetIndex wellFormed
  · have targetRoot : trace.target = input.root := by
      calc
        trace.target = trace.origin (trace.targetIndex wellFormed) :=
          (trace.targetIndex_origin wellFormed).symm
        _ = trace.origin trace.sourceDiagram.root :=
          congrArg trace.origin focused.symm
        _ = input.root := trace.promotion.root_origin
    have atFocus :=
      (trace.promotedWire_scope_eq_targetIndex_iff wellFormed wire).1
        (scope.trans focused)
    exact atFocus.imp (fun atTarget => atTarget.trans targetRoot)
      (fun atInner => atInner)
  · exact Or.inl ((trace.promotedWire_scope_eq_regular_iff wellFormed wire
      trace.sourceDiagram.root focused).1 scope |>.trans
        trace.promotion.root_origin)

theorem sourceOpen_wellFormed
    (trace : DoubleCutElimTrace input outer raw)
    (sourceWellFormed : trace.sourceDiagram.WellFormed signature)
    (targetWellFormed : input.WellFormed signature)
    (boundary : List (Fin input.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.wires wire).scope = input.root) :
    (trace.sourceOpen boundary).WellFormed signature := by
  refine {
    diagram_well_formed := sourceWellFormed
    boundary_is_root_scoped := ?_
  }
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
    (trace : DoubleCutElimTrace input outer raw)
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
    rcases trace.promotedRoot_scope_target_or_inner targetWellFormed wire
      sourceScope with targetScope | innerScope
    · exact Or.inl ((OpenConcreteDiagram.mem_rootWires_iff target.val
        target.property wire).2 targetScope)
    · exact Or.inr ((ConcreteElaboration.mem_exactScopeWires input trace.inner
        wire).2 innerScope)

theorem sourceOpen_hiddenWires_eq_of_regular
    (trace : DoubleCutElimTrace input outer raw)
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
  have rootOrigin' :
      (doubleCutRegionDomain input outer trace.inner).origin
          trace.sourceDiagram.root = input.root := by
    simpa [origin] using rootOrigin
  rw [rootOrigin']
  rfl

def rootOuterIndex (ambient locals : List α)
    (index : Fin ambient.length) : Fin (ambient ++ locals).length :=
  Fin.cast (by simp)
    (Fin.castAdd locals.length index)

def rootLocalIndex (ambient locals : List α)
    (index : Fin locals.length) : Fin (ambient ++ locals).length :=
  Fin.cast (by simp)
    (Fin.natAdd ambient.length index)

def rootLocalPart (ambient locals : List α)
    (environment : Fin (ambient ++ locals).length → D) :
    Fin locals.length → D :=
  fun index => environment (rootLocalIndex ambient locals index)

theorem rootEnvironment_of_parts
    (ambient locals : ConcreteElaboration.WireContext diagram)
    (outerEnvironment : Fin ambient.length → D)
    (environment : Fin (ambient ++ locals).length → D)
    (outerValues : ∀ index,
      environment (rootOuterIndex ambient locals index) =
        outerEnvironment index) :
    ConcreteElaboration.rootEnvironment ambient locals outerEnvironment
        (rootLocalPart ambient locals environment) = environment := by
  funext index
  let splitIndex : Fin (ambient.length + locals.length) :=
    Fin.cast (by simp) index
  change extendWireEnv outerEnvironment (rootLocalPart ambient locals
      environment) splitIndex =
    environment (Fin.cast
      (show ambient.length + locals.length = (ambient ++ locals).length by simp)
      splitIndex)
  refine Fin.addCases ?_ ?_ splitIndex
  · intro outerIndex
    rw [extendWireEnv, Fin.addCases_left]
    exact (outerValues outerIndex).symm
  · intro localIndex
    rw [extendWireEnv, Fin.addCases_right]
    rfl

@[simp] theorem rootEnvironment_outer
    (ambient locals : ConcreteElaboration.WireContext diagram)
    (outerEnvironment : Fin ambient.length → D)
    (localEnvironment : Fin locals.length → D)
    (index : Fin ambient.length) :
    ConcreteElaboration.rootEnvironment ambient locals outerEnvironment
        localEnvironment (rootOuterIndex ambient locals index) =
      outerEnvironment index := by
  simp [ConcreteElaboration.rootEnvironment, rootOuterIndex, extendWireEnv,
    Fin.addCases_left]

@[simp] theorem rootEnvironment_local
    (ambient locals : ConcreteElaboration.WireContext diagram)
    (outerEnvironment : Fin ambient.length → D)
    (localEnvironment : Fin locals.length → D)
    (index : Fin locals.length) :
    ConcreteElaboration.rootEnvironment ambient locals outerEnvironment
        localEnvironment (rootLocalIndex ambient locals index) =
      localEnvironment index := by
  simp [ConcreteElaboration.rootEnvironment, rootLocalIndex, extendWireEnv,
    Fin.addCases_right]

@[simp] theorem rootOuterIndex_get
    (ambient locals : List α) (index : Fin ambient.length) :
    (ambient ++ locals).get (rootOuterIndex ambient locals index) =
      ambient.get index := by
  simp [rootOuterIndex, List.get_eq_getElem, List.getElem_append_left]

@[simp] theorem rootLocalIndex_get
    (ambient locals : List α) (index : Fin locals.length) :
    (ambient ++ locals).get (rootLocalIndex ambient locals index) =
      locals.get index := by
  simp [rootLocalIndex, List.get_eq_getElem, List.getElem_append_right]

def PromotedContextWitness.extendRootSelected
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input)
    (context : PromotedContextWitness trace sourceContext targetContext)
    (sourceExact : sourceContext.Exact (trace.targetIndex wellFormed)) :
    PromotedContextWitness trace sourceContext
      ((targetContext.extend outer).extend trace.inner) := by
  refine ⟨?_, ?_⟩
  · intro wire member
    rcases List.mem_append.mp member with beforeInner | innerMember
    · rcases List.mem_append.mp beforeInner with targetMember | outerMember
      · exact context.target_subset_source wire targetMember
      · rw [trace.outer_exactScopeWires] at outerMember
        exact False.elim (List.not_mem_nil outerMember)
    · have focusMember := trace.innerWire_mem_focusExact wellFormed wire
        innerMember
      have scope := (ConcreteElaboration.mem_exactScopeWires
        trace.sourceDiagram (trace.targetIndex wellFormed) wire).1 focusMember
      exact (sourceExact.mem_iff wire).2 (by
        rw [scope]
        exact ConcreteDiagram.Encloses.refl _ _)
  · intro wire member
    rcases context.source_subset_target_or_inner wire member with
      targetMember | innerMember
    · exact Or.inl (List.mem_append_left _
        (List.mem_append_left _ targetMember))
    · exact Or.inl (List.mem_append_right _ innerMember)

theorem PromotedContextWitness.extendRootSelected_source_subset_target
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (sourceContext : ConcreteElaboration.WireContext trace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input)
    (context : PromotedContextWitness trace sourceContext targetContext)
    (sourceExact : sourceContext.Exact (trace.targetIndex wellFormed)) :
    ∀ wire, wire ∈ sourceContext →
      wire ∈ ((targetContext.extend outer).extend trace.inner) := by
  intro wire member
  exact (context.extendRootSelected trace wellFormed sourceContext
    targetContext sourceExact).source_subset_target_or_inner wire member |>.elim
      id (fun innerMember => List.mem_append_right _ innerMember)

theorem targetRootSelected_exact
    (trace : DoubleCutElimTrace input outer raw)
    (wellFormed : input.WellFormed signature)
    (targetContext : ConcreteElaboration.WireContext input)
    (targetExact : targetContext.Exact trace.target) :
    ((targetContext.extend outer).extend trace.inner).Exact trace.inner := by
  have outerExact := targetExact.extend_child wellFormed trace.outer_parent
  exact outerExact.extend_child wellFormed trace.inner_parent

end VisualProof.Rule.DoubleCutElimTrace
