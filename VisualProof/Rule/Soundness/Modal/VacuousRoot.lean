import VisualProof.Rule.Soundness.Modal.VacuousSimulation

namespace VisualProof.Rule.VacuousSoundness

open VisualProof
open VisualProof.Theory
open VisualProof.Diagram

def vacuousIntroRawOpen
    (source : OpenConcreteDiagram)
    (selection : CheckedSelection source.diagram) (arity : Nat) :
    OpenConcreteDiagram where
  diagram := vacuousIntroRaw source.diagram selection arity
  boundary := source.boundary

@[simp] theorem vacuousIntroRawOpen_exposedWires
    (source : OpenConcreteDiagram)
    (selection : CheckedSelection source.diagram) (arity : Nat) :
    (vacuousIntroRawOpen source selection arity).exposedWires =
      source.exposedWires := rfl

@[simp] theorem vacuousIntroRawOpen_hiddenWires
    (source : OpenConcreteDiagram)
    (selection : CheckedSelection source.diagram) (arity : Nat) :
    (vacuousIntroRawOpen source selection arity).hiddenWires =
      source.hiddenWires := by
  unfold OpenConcreteDiagram.hiddenWires
  change
    (ConcreteElaboration.exactScopeWires
      (vacuousIntroRaw source.diagram selection arity)
      (vacuousIntroRaw source.diagram selection arity).root).filter
        (fun wire => decide (wire ∉ source.exposedWires)) =
      (ConcreteElaboration.exactScopeWires source.diagram
        source.diagram.root).filter
          (fun wire => decide (wire ∉ source.exposedWires))
  rw [vacuousIntroRaw_root, vacuousIntroRaw_exactScopeWires]

@[simp] theorem vacuousIntroRawOpen_rootWires
    (source : OpenConcreteDiagram)
    (selection : CheckedSelection source.diagram) (arity : Nat) :
    (vacuousIntroRawOpen source selection arity).rootWires =
      source.rootWires := by
  unfold OpenConcreteDiagram.rootWires
  rw [vacuousIntroRawOpen_exposedWires,
    vacuousIntroRawOpen_hiddenWires]
  rfl

theorem vacuousIntroRawOpen_wellFormed
    (source : CheckedOpenDiagram signature)
    (selection : CheckedSelection source.val.diagram) (arity : Nat)
    (targetWellFormed :
      (vacuousIntroRaw source.val.diagram selection arity).WellFormed
        signature) :
    (vacuousIntroRawOpen source.val selection arity).WellFormed signature := by
  refine {
    diagram_well_formed := targetWellFormed
    boundary_is_root_scoped := ?_
  }
  intro wire member
  have sourceScoped := source.property.boundary_is_root_scoped wire member
  change Fin.castAdd 1 (source.val.diagram.wires wire).scope =
    source.val.diagram.root.castSucc
  apply Fin.ext
  exact congrArg
    (fun value : Fin source.val.diagram.regionCount => value.val)
    sourceScoped

theorem rootTransport_of_itemSimulation
    (source : CheckedOpenDiagram signature)
    (selection : CheckedSelection source.val.diagram) (arity : Nat)
    (targetWellFormed :
      (vacuousIntroRaw source.val.diagram selection arity).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (sourceItems : ItemSeq signature source.val.rootWires.length [])
    (targetItems : ItemSeq signature
      (vacuousIntroRawOpen source.val selection arity).rootWires.length [])
    (itemSimulation : ConcreteElaboration.ItemSeqSimulation model named
      direction
      (LiftedContextWitness.indexRelation
        (⟨by
          rw [vacuousIntroRawOpen_rootWires]
        ⟩ : LiftedContextWitness source.val.diagram selection arity
          source.val.rootWires
          (vacuousIntroRawOpen source.val selection arity).rootWires))
      sourceItems targetItems) :
    ConcreteElaboration.DirectionalRootTransport direction
      source.val.exposedWires source.val.hiddenWires
      (vacuousIntroRawOpen source.val selection arity).exposedWires
      (vacuousIntroRawOpen source.val selection arity).hiddenWires
      (ConcreteElaboration.ContextIndexRelation.forwardMap id)
      model named sourceItems targetItems := by
  let target : CheckedOpenDiagram signature :=
    ⟨vacuousIntroRawOpen source.val selection arity,
      vacuousIntroRawOpen_wellFormed source selection arity targetWellFormed⟩
  have exposedEq : target.val.exposedWires = source.val.exposedWires :=
    vacuousIntroRawOpen_exposedWires source.val selection arity
  have hiddenEq : target.val.hiddenWires = source.val.hiddenWires :=
    vacuousIntroRawOpen_hiddenWires source.val selection arity
  let combinedContext : LiftedContextWitness source.val.diagram selection arity
      source.val.rootWires target.val.rootWires :=
    ⟨by rw [show target.val.rootWires = source.val.rootWires by
      exact vacuousIntroRawOpen_rootWires source.val selection arity]⟩
  apply ConcreteElaboration.directionalRootTransport_of_agreement
    direction source.val.exposedWires source.val.hiddenWires
    target.val.exposedWires target.val.hiddenWires
    (ConcreteElaboration.ContextIndexRelation.forwardMap id)
    combinedContext.indexRelation model named sourceItems targetItems
  · intro sourceOuter targetOuter outerAgrees
    have outerEq : sourceOuter = targetOuter := by
      simpa only [
        ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap,
        Function.comp_id] using outerAgrees
    subst targetOuter
    cases direction with
    | forward =>
        intro sourceLocal
        let targetLocal : Fin target.val.hiddenWires.length → model.Carrier :=
          fun index => sourceLocal (Fin.cast
            (congrArg List.length hiddenEq) index)
        refine ⟨targetLocal, ?_⟩
        unfold LiftedContextWitness.indexRelation
          ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
          ConcreteElaboration.ContextIndexRelation.forwardMap
        intro sourceIndex targetIndex related
        subst targetIndex
        unfold ConcreteElaboration.rootEnvironment
        simp only [Function.comp_apply]
        apply ModalSoundness.extendWireEnv_transport
          (countEq := congrArg List.length hiddenEq)
          (sourceLocal := sourceLocal) (targetLocal := targetLocal)
        · intro index
          rfl
        · rfl
    | backward =>
        intro targetLocal
        let sourceLocal : Fin source.val.hiddenWires.length → model.Carrier :=
          fun index => targetLocal (Fin.cast
            (congrArg List.length hiddenEq).symm index)
        refine ⟨sourceLocal, ?_⟩
        unfold LiftedContextWitness.indexRelation
          ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
          ConcreteElaboration.ContextIndexRelation.forwardMap
        intro sourceIndex targetIndex related
        subst targetIndex
        unfold ConcreteElaboration.rootEnvironment
        simp only [Function.comp_apply]
        apply ModalSoundness.extendWireEnv_transport
          (countEq := congrArg List.length hiddenEq)
          (sourceLocal := sourceLocal) (targetLocal := targetLocal)
        · intro index
          apply congrArg targetLocal
          apply Fin.ext
          rfl
        · rfl
  · simpa [combinedContext, target] using itemSimulation

noncomputable def vacuousIntroRootContext
    (source : CheckedOpenDiagram signature)
    (selection : CheckedSelection source.val.diagram) (arity : Nat)
    (targetWellFormed :
      (vacuousIntroRaw source.val.diagram selection arity).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection) :
    let input : CheckedDiagram signature :=
      ⟨source.val.diagram, source.property.diagram_well_formed⟩
    let simulation := vacuousIntroSimulation input selection arity
      targetWellFormed model named
    ConcreteElaboration.ConcreteSemanticSimulation.RootContextSimulation
      simulation direction source.val.exposedWires source.val.hiddenWires
      (vacuousIntroRawOpen source.val selection arity).exposedWires
      (vacuousIntroRawOpen source.val selection arity).hiddenWires := by
  let input : CheckedDiagram signature :=
    ⟨source.val.diagram, source.property.diagram_well_formed⟩
  let simulation := vacuousIntroSimulation input selection arity
    targetWellFormed model named
  let target : CheckedOpenDiagram signature :=
    ⟨vacuousIntroRawOpen source.val selection arity,
      vacuousIntroRawOpen_wellFormed source selection arity targetWellFormed⟩
  change ConcreteElaboration.ConcreteSemanticSimulation.RootContextSimulation
    simulation direction source.val.exposedWires source.val.hiddenWires
      target.val.exposedWires target.val.hiddenWires
  have exposedEq : target.val.exposedWires = source.val.exposedWires :=
    vacuousIntroRawOpen_exposedWires source.val selection arity
  have hiddenEq : target.val.hiddenWires = source.val.hiddenWires :=
    vacuousIntroRawOpen_hiddenWires source.val selection arity
  let combinedContext : LiftedContextWitness input.val selection arity
      source.val.rootWires target.val.rootWires :=
    ⟨by rw [show target.val.rootWires = source.val.rootWires by
      exact vacuousIntroRawOpen_rootWires source.val selection arity]⟩
  let outerRelation :=
    ConcreteElaboration.ContextIndexRelation.forwardMap
      (id : Fin source.val.exposedWires.length →
        Fin target.val.exposedWires.length)
  refine {
    outer := outerRelation
    context := combinedContext
    atRoot := True.intro
    atRootChild := by intros; trivial
    atFocusedRootChild := by intros; trivial
    transport := ?_
    focusedRootKernel := ?_
  }
  · intro regular allowed sourceItems targetItems sourceCompiled targetCompiled
      itemSemantics
    exact rootTransport_of_itemSimulation source selection arity
      targetWellFormed model named direction
      (sourceItems.renameRelations
        (simulation.relationMap simulation.binders_empty))
      targetItems itemSemantics
  · intro atRoot focused allowed recurse recurseAt sourceItems targetItems
      sourceCompiled targetCompiled
    have sourceExact :
        ConcreteElaboration.WireContext.Exact source.val.rootWires
          source.val.diagram.root := by
      simpa only [OpenConcreteDiagram.rootWires] using
        ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
          source
    have targetExact :
        @ConcreteElaboration.WireContext.Exact target.val.diagram
          target.val.rootWires target.val.diagram.root := by
      simpa only [OpenConcreteDiagram.rootWires] using
        ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
          target
    change input.val.root = selection.val.anchor at focused
    have itemSimulation := focusedItems input selection arity targetWellFormed
      model named direction input.val.regionCount
      (vacuousIntroRaw input.val selection arity).regionCount
      source.val.rootWires target.val.rootWires combinedContext
      ConcreteElaboration.BinderContext.empty
      ConcreteElaboration.BinderContext.empty simulation.binders_empty
      (by simpa only [← focused] using sourceExact)
      (by simpa only [simulation.root_eq, ← focused] using targetExact)
      (by
        simpa only [← focused] using
          ConcreteElaboration.BinderContext.empty_covers_root
            source.property.diagram_well_formed)
      (by
        simpa only [simulation.root_eq, ← focused] using
          ConcreteElaboration.BinderContext.empty_covers_root
            target.property.diagram_well_formed)
      (by
        simpa only [← focused] using
          ConcreteElaboration.BinderContext.Enumeration.empty
            source.val.diagram)
      (by
        simpa only [simulation.root_eq, ← focused] using
          ConcreteElaboration.BinderContext.Enumeration.empty
            target.val.diagram)
      recurseAt sourceItems targetItems
      (by simpa only [← focused] using sourceCompiled)
      (by
        change ConcreteElaboration.compileOccurrencesWith? signature
          (vacuousIntroRaw input.val selection arity)
          (ConcreteElaboration.compileRegion? signature
            (vacuousIntroRaw input.val selection arity)
            (vacuousIntroRaw input.val selection arity).regionCount)
          target.val.rootWires ConcreteElaboration.BinderContext.empty
          (ConcreteElaboration.localOccurrences
            (vacuousIntroRaw input.val selection arity)
            selection.val.anchor.castSucc) = some targetItems
        simpa only [← focused] using targetCompiled)
    have relationMapEq :
        (simulation.relationMap simulation.binders_empty :
          RelationRenaming [] []) =
            (fun {binderArity} (relation : RelVar [] binderArity) =>
              relation) := by
      apply @funext
      intro binderArity
      funext relation
      exact Fin.elim0 relation.index
    rw [relationMapEq, Region.renameRelations_id]
    apply ConcreteElaboration.finishRoot_denote direction
      source.val.exposedWires source.val.hiddenWires
      target.val.exposedWires target.val.hiddenWires outerRelation model named
    change ConcreteElaboration.ItemSeqSimulation model named direction
      combinedContext.indexRelation
      (sourceItems.renameRelations simulation.binders_empty.relationMap)
      targetItems at itemSimulation
    have emptyMapEq :
        (simulation.binders_empty.relationMap : RelationRenaming [] []) =
          (fun {binderArity} (relation : RelVar [] binderArity) =>
            relation) := relationMapEq
    rw [emptyMapEq, ItemSeq.renameRelations_id] at itemSimulation
    exact rootTransport_of_itemSimulation source selection arity
      targetWellFormed model named direction sourceItems targetItems
      itemSimulation

theorem vacuousIntroBoundaryWitness
    (source : CheckedOpenDiagram signature)
    (selection : CheckedSelection source.val.diagram) (arity : Nat)
    (targetWellFormed :
      (vacuousIntroRaw source.val.diagram selection arity).WellFormed signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin source.val.boundary.length → model.Carrier) :
    let input : CheckedDiagram signature :=
      ⟨source.val.diagram, source.property.diagram_well_formed⟩
    let simulation := vacuousIntroSimulation input selection arity
      targetWellFormed model named
    let target : CheckedOpenDiagram signature :=
      ⟨vacuousIntroRawOpen source.val selection arity,
        vacuousIntroRawOpen_wellFormed source selection arity targetWellFormed⟩
    ConcreteElaboration.ConcreteSemanticSimulation.DirectionalBoundaryWitness
      direction source.elaborate target.elaborate
      (vacuousIntroRootContext source selection arity targetWellFormed model
        named direction).outer model named args args := by
  let target : CheckedOpenDiagram signature :=
    ⟨vacuousIntroRawOpen source.val selection arity,
      vacuousIntroRawOpen_wellFormed source selection arity targetWellFormed⟩
  dsimp only
  unfold
    ConcreteElaboration.ConcreteSemanticSimulation.DirectionalBoundaryWitness
  cases direction with
  | forward =>
      intro sourceAssignment sourceArgsEq sourceDenotes
      let targetAssignment : BoundaryAssignment target.elaborate model.Carrier := {
        args := args
        classes := sourceAssignment.classes
        agrees := by
          intro position
          change sourceAssignment.classes
              (target.val.boundaryClass position) = args position
          have classEq : target.val.boundaryClass position =
              source.val.boundaryClass position := by
            apply Fin.ext
            rfl
          rw [classEq, ← sourceArgsEq]
          exact sourceAssignment.agrees position
      }
      refine ⟨targetAssignment, rfl, ?_⟩
      unfold ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
      intro sourceIndex targetIndex related
      simp [vacuousIntroRootContext,
        ConcreteElaboration.ContextIndexRelation.forwardMap] at related
      subst targetIndex
      rfl
  | backward =>
      intro targetAssignment targetArgsEq targetDenotes
      let sourceAssignment : BoundaryAssignment source.elaborate model.Carrier := {
        args := args
        classes := targetAssignment.classes
        agrees := by
          intro position
          change targetAssignment.classes
              (source.val.boundaryClass position) = args position
          have classEq : target.val.boundaryClass position =
              source.val.boundaryClass position := by
            apply Fin.ext
            rfl
          rw [← classEq, ← targetArgsEq]
          exact targetAssignment.agrees position
      }
      refine ⟨sourceAssignment, rfl, ?_⟩
      unfold ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
      intro sourceIndex targetIndex related
      simp [vacuousIntroRootContext,
        ConcreteElaboration.ContextIndexRelation.forwardMap] at related
      subst targetIndex
      rfl

theorem vacuousIntroInterfaceTransport_transportBoundary
    (source : ConcreteDiagram) (selection : CheckedSelection source)
    (arity : Nat) (boundary : List (Fin source.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (source.wires wire).scope = source.root) :
    (vacuousIntroInterfaceTransport source selection arity).transportBoundary
        boundary = some boundary := by
  calc
    _ = some (boundary.map id) := by
      apply InterfaceTransport.transportBoundary_eq_map
      intro wire member
      have targetRoot :
          ((vacuousIntroRaw source selection arity).wires wire).scope =
            (vacuousIntroRaw source selection arity).root := by
        change Fin.castAdd 1 (source.wires wire).scope = source.root.castSucc
        apply Fin.ext
        exact congrArg (fun value : Fin source.regionCount => value.val)
          (sourceRoot wire member)
      change
        (if ((vacuousIntroRaw source selection arity).wires wire).scope =
              (vacuousIntroRaw source selection arity).root then some wire
          else none) = some (id wire)
      rw [if_pos targetRoot]
      rfl
    _ = some boundary := by simp

end VisualProof.Rule.VacuousSoundness
