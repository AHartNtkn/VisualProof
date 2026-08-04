import VisualProof.Rule.Soundness.Modal.FocusedItems

namespace VisualProof.Rule.ModalSoundness

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram

def doubleCutIntroRawOpen
    (source : OpenConcreteDiagram)
    (selection : CheckedSelection source.diagram) :
    OpenConcreteDiagram where
  diagram := doubleCutIntroRaw source.diagram selection
  boundary := source.boundary

@[simp] theorem doubleCutIntroRawOpen_exposedWires
    (source : OpenConcreteDiagram)
    (selection : CheckedSelection source.diagram) :
    (doubleCutIntroRawOpen source selection).exposedWires =
      source.exposedWires := by
  rfl

@[simp] theorem doubleCutIntroRawOpen_hiddenWires
    (source : OpenConcreteDiagram)
    (selection : CheckedSelection source.diagram) :
    (doubleCutIntroRawOpen source selection).hiddenWires =
      source.hiddenWires := by
  unfold OpenConcreteDiagram.hiddenWires
  change
    (ConcreteElaboration.exactScopeWires
      (doubleCutIntroRaw source.diagram selection)
      (doubleCutIntroRaw source.diagram selection).root).filter
        (fun wire => decide (wire ∉ source.exposedWires)) =
      (ConcreteElaboration.exactScopeWires source.diagram
        source.diagram.root).filter
          (fun wire => decide (wire ∉ source.exposedWires))
  rw [doubleCutIntroRaw_root,
    doubleCutIntroRaw_exactScopeWires]

@[simp] theorem doubleCutIntroRawOpen_rootWires
    (source : OpenConcreteDiagram)
    (selection : CheckedSelection source.diagram) :
    (doubleCutIntroRawOpen source selection).rootWires =
      source.rootWires := by
  unfold OpenConcreteDiagram.rootWires
  rw [doubleCutIntroRawOpen_exposedWires,
    doubleCutIntroRawOpen_hiddenWires]
  rfl

theorem doubleCutIntroRawOpen_wellFormed
    (source : CheckedOpenDiagram signature)
    (selection : CheckedSelection source.val.diagram)
    (targetWellFormed :
      (doubleCutIntroRaw source.val.diagram selection).WellFormed signature) :
    (doubleCutIntroRawOpen source.val selection).WellFormed signature := by
  refine {
    diagram_well_formed := targetWellFormed
    boundary_is_root_scoped := ?_
  }
  intro wire member
  have sourceScoped := source.property.boundary_is_root_scoped wire member
  simpa [doubleCutIntroRawOpen, doubleCutIntroRaw_wire,
    doubleCutIntroRaw_root, liftCWireRegions, sourceScoped]

noncomputable def doubleCutIntroRootContext
    (source : CheckedOpenDiagram signature)
    (selection : CheckedSelection source.val.diagram)
    (targetWellFormed :
      (doubleCutIntroRaw source.val.diagram selection).WellFormed signature)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection) :
    let simulation := doubleCutIntroSimulation
      ⟨source.val.diagram, source.property.diagram_well_formed⟩ selection
      targetWellFormed model named
    ConcreteElaboration.ConcreteSemanticSimulation.RootContextSimulation
      simulation direction
      source.val.exposedWires source.val.hiddenWires
      (doubleCutIntroRawOpen source.val selection).exposedWires
      (doubleCutIntroRawOpen source.val selection).hiddenWires := by
  let input : CheckedDiagram signature :=
    ⟨source.val.diagram, source.property.diagram_well_formed⟩
  let simulation := doubleCutIntroSimulation input selection targetWellFormed
    model named
  let target : CheckedOpenDiagram signature :=
    ⟨doubleCutIntroRawOpen source.val selection,
      doubleCutIntroRawOpen_wellFormed source selection targetWellFormed⟩
  change ConcreteElaboration.ConcreteSemanticSimulation.RootContextSimulation
    simulation direction source.val.exposedWires source.val.hiddenWires
      target.val.exposedWires target.val.hiddenWires
  have exposedEq : target.val.exposedWires = source.val.exposedWires :=
    doubleCutIntroRawOpen_exposedWires source.val selection
  have hiddenEq : target.val.hiddenWires = source.val.hiddenWires :=
    doubleCutIntroRawOpen_hiddenWires source.val selection
  let combinedContext :
      LiftedContextWitness input.val selection
        (source.val.exposedWires ++ source.val.hiddenWires)
        (target.val.exposedWires ++ target.val.hiddenWires) :=
    ⟨by rw [exposedEq, hiddenEq]; rfl⟩
  let outerMap :=
    Fin.cast (congrArg List.length exposedEq.symm)
  let outerRelation :=
    ConcreteElaboration.ContextIndexRelation.forwardMap outerMap
  refine {
    outer := outerRelation
    context := combinedContext
    atRoot := True.intro
    atRootChild := by
      intro regular child parent
      trivial
    atFocusedRootChild := by
      intro focused child sourceParent targetParent
      trivial
    transport := ?_
    focusedRootKernel := ?_
  }
  · intro regular allowed sourceItems targetItems sourceCompiled targetCompiled
      itemSemantics
    apply ConcreteElaboration.directionalRootTransport_of_agreement
      direction source.val.exposedWires source.val.hiddenWires
      target.val.exposedWires target.val.hiddenWires outerRelation
      combinedContext.indexRelation model named
      (sourceItems.renameRelations
        (simulation.relationMap simulation.binders_empty))
      targetItems
    · intro sourceOuter targetOuter outerAgrees
      cases exposedEq
      have outerEq : sourceOuter = targetOuter := by
        have outerMapIdentity :
            outerMap =
              (id : Fin source.val.exposedWires.length →
                Fin source.val.exposedWires.length) := by
          funext index
          apply Fin.ext
          rfl
        have outerFunctional :=
          (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
            outerMap sourceOuter targetOuter).mp (by
              simpa only [outerRelation] using outerAgrees)
        rw [outerMapIdentity] at outerFunctional
        simpa [Function.comp_def] using outerFunctional
      subst targetOuter
      cases direction with
      | forward =>
          intro sourceLocal
          let targetLocal : Fin target.val.hiddenWires.length → model.Carrier :=
            fun index =>
              sourceLocal (Fin.cast (congrArg List.length hiddenEq) index)
          refine ⟨targetLocal, ?_⟩
          unfold LiftedContextWitness.indexRelation
            ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
            ConcreteElaboration.ContextIndexRelation.forwardMap
          intro sourceIndex targetIndex related
          subst targetIndex
          unfold ConcreteElaboration.rootEnvironment
          simp only [Function.comp_apply]
          apply extendWireEnv_transport
            (countEq := congrArg List.length hiddenEq)
            (sourceLocal := sourceLocal) (targetLocal := targetLocal)
          · intro index
            rfl
          · rfl
      | backward =>
          intro targetLocal
          let sourceLocal : Fin source.val.hiddenWires.length → model.Carrier :=
            fun index =>
              targetLocal (Fin.cast (congrArg List.length hiddenEq).symm index)
          refine ⟨sourceLocal, ?_⟩
          unfold LiftedContextWitness.indexRelation
            ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
            ConcreteElaboration.ContextIndexRelation.forwardMap
          intro sourceIndex targetIndex related
          subst targetIndex
          unfold ConcreteElaboration.rootEnvironment
          simp only [Function.comp_apply]
          apply extendWireEnv_transport
            (countEq := congrArg List.length hiddenEq)
            (sourceLocal := sourceLocal) (targetLocal := targetLocal)
          · intro index
            apply congrArg targetLocal
            apply Fin.ext
            rfl
          · rfl
    · exact itemSemantics
  · intro atRoot focused allowed recurse recurseAt sourceItems targetItems
      sourceCompiled targetCompiled
    have sourceExact :
        ConcreteElaboration.WireContext.Exact
          (source.val.exposedWires ++ source.val.hiddenWires)
          source.val.diagram.root := by
      simpa only [OpenConcreteDiagram.rootWires] using
        ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
          source
    have targetExact :
        @ConcreteElaboration.WireContext.Exact target.val.diagram
          (target.val.exposedWires ++ target.val.hiddenWires :
            ConcreteElaboration.WireContext target.val.diagram)
          target.val.diagram.root := by
      simpa only [OpenConcreteDiagram.rootWires] using
        ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
          target
    change input.val.root = selection.val.anchor at focused
    have itemSimulation :=
      doubleCutIntroFocusedItems input selection targetWellFormed model named
        direction input.val.regionCount
        (doubleCutIntroRaw input.val selection).regionCount
        (source.val.exposedWires ++ source.val.hiddenWires)
        (target.val.exposedWires ++ target.val.hiddenWires)
        combinedContext
        ConcreteElaboration.BinderContext.empty
        ConcreteElaboration.BinderContext.empty
        simulation.binders_empty (by simpa only [← focused] using sourceExact)
        (by
          simpa only [simulation.root_eq, ← focused] using targetExact)
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
          change
            ConcreteElaboration.compileOccurrencesWith? signature
              (doubleCutIntroRaw input.val selection)
              (ConcreteElaboration.compileRegion? signature
                (doubleCutIntroRaw input.val selection)
                (doubleCutIntroRaw input.val selection).regionCount)
              (target.val.exposedWires ++ target.val.hiddenWires)
              ConcreteElaboration.BinderContext.empty
              (ConcreteElaboration.localOccurrences
                (doubleCutIntroRaw input.val selection)
                (Fin.castAdd 2 selection.val.anchor)) =
              some targetItems
          simpa only [← focused] using targetCompiled)
    have relationMapEq :
        (simulation.relationMap simulation.binders_empty :
          RelationRenaming [] []) =
            (fun {arity} (relation : RelVar [] arity) => relation) := by
      apply @funext
      intro arity
      funext relation
      exact Fin.elim0 relation.index
    rw [relationMapEq, Region.renameRelations_id]
    apply ConcreteElaboration.finishRoot_denote direction
      source.val.exposedWires source.val.hiddenWires
      target.val.exposedWires target.val.hiddenWires outerRelation model named
    apply ConcreteElaboration.directionalRootTransport_of_agreement
      direction source.val.exposedWires source.val.hiddenWires
      target.val.exposedWires target.val.hiddenWires outerRelation
      combinedContext.indexRelation model named sourceItems targetItems
    · intro sourceOuter targetOuter outerAgrees
      cases exposedEq
      have outerEq : sourceOuter = targetOuter := by
        have outerMapIdentity :
            outerMap =
              (id : Fin source.val.exposedWires.length →
                Fin source.val.exposedWires.length) := by
          funext index
          apply Fin.ext
          rfl
        have outerFunctional :=
          (ConcreteElaboration.ContextIndexRelation.environmentsAgree_forwardMap
            outerMap sourceOuter targetOuter).mp (by
              simpa only [outerRelation] using outerAgrees)
        rw [outerMapIdentity] at outerFunctional
        simpa [Function.comp_def] using outerFunctional
      subst targetOuter
      cases direction with
      | forward =>
          intro sourceLocal
          let targetLocal : Fin target.val.hiddenWires.length → model.Carrier :=
            fun index =>
              sourceLocal (Fin.cast (congrArg List.length hiddenEq) index)
          refine ⟨targetLocal, ?_⟩
          unfold LiftedContextWitness.indexRelation
            ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
            ConcreteElaboration.ContextIndexRelation.forwardMap
          intro sourceIndex targetIndex related
          subst targetIndex
          unfold ConcreteElaboration.rootEnvironment
          simp only [Function.comp_apply]
          apply extendWireEnv_transport
            (countEq := congrArg List.length hiddenEq)
            (sourceLocal := sourceLocal) (targetLocal := targetLocal)
          · intro index
            rfl
          · rfl
      | backward =>
          intro targetLocal
          let sourceLocal : Fin source.val.hiddenWires.length → model.Carrier :=
            fun index =>
              targetLocal (Fin.cast (congrArg List.length hiddenEq).symm index)
          refine ⟨sourceLocal, ?_⟩
          unfold LiftedContextWitness.indexRelation
            ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
            ConcreteElaboration.ContextIndexRelation.forwardMap
          intro sourceIndex targetIndex related
          subst targetIndex
          unfold ConcreteElaboration.rootEnvironment
          simp only [Function.comp_apply]
          apply extendWireEnv_transport
            (countEq := congrArg List.length hiddenEq)
            (sourceLocal := sourceLocal) (targetLocal := targetLocal)
          · intro index
            apply congrArg targetLocal
            apply Fin.ext
            rfl
          · rfl
    · have liftedRelationMapEq :
          (LiftedBinderWitness.relationMap simulation.binders_empty :
            RelationRenaming [] []) =
              (fun {arity} (relation : RelVar [] arity) => relation) := by
        rfl
      rw [liftedRelationMapEq, ItemSeq.renameRelations_id] at itemSimulation
      exact itemSimulation

theorem doubleCutIntroBoundaryWitness
    (source : CheckedOpenDiagram signature)
    (selection : CheckedSelection source.val.diagram)
    (targetWellFormed :
      (doubleCutIntroRaw source.val.diagram selection).WellFormed signature)
    (direction : ConcreteElaboration.SimulationDirection)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin source.val.boundary.length → model.Carrier) :
    let target : CheckedOpenDiagram signature :=
      ⟨doubleCutIntroRawOpen source.val selection,
        doubleCutIntroRawOpen_wellFormed source selection targetWellFormed⟩
    ConcreteElaboration.ConcreteSemanticSimulation.DirectionalBoundaryWitness
      direction source.elaborate target.elaborate
      (doubleCutIntroRootContext source selection targetWellFormed model named
        direction).outer
      model named args args := by
  let target : CheckedOpenDiagram signature :=
    ⟨doubleCutIntroRawOpen source.val selection,
      doubleCutIntroRawOpen_wellFormed source selection targetWellFormed⟩
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
          have classEq :
              target.val.boundaryClass position =
                source.val.boundaryClass position := by
            apply Fin.ext
            rfl
          rw [classEq, ← sourceArgsEq]
          exact sourceAssignment.agrees position
      }
      refine ⟨targetAssignment, rfl, ?_⟩
      unfold ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
      intro sourceIndex targetIndex related
      simp [doubleCutIntroRootContext,
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
          have classEq :
              target.val.boundaryClass position =
                source.val.boundaryClass position := by
            apply Fin.ext
            rfl
          rw [← classEq, ← targetArgsEq]
          exact targetAssignment.agrees position
      }
      refine ⟨sourceAssignment, rfl, ?_⟩
      unfold ConcreteElaboration.ContextIndexRelation.EnvironmentsAgree
      intro sourceIndex targetIndex related
      simp [doubleCutIntroRootContext,
        ConcreteElaboration.ContextIndexRelation.forwardMap] at related
      subst targetIndex
      rfl

theorem doubleCutIntroInterfaceTransport_transportBoundary
    (source : ConcreteDiagram)
    (selection : CheckedSelection source)
    (boundary : List (Fin source.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (source.wires wire).scope = source.root) :
    (doubleCutIntroInterfaceTransport source selection).transportBoundary
        boundary =
      some boundary := by
  calc
    _ = some (boundary.map id) := by
      apply InterfaceTransport.transportBoundary_eq_map
      intro wire member
      have targetRoot :
          ((doubleCutIntroRaw source selection).wires wire).scope =
            (doubleCutIntroRaw source selection).root := by
        simpa [doubleCutIntroRaw_wire, doubleCutIntroRaw_root,
          liftCWireRegions] using congrArg (Fin.castAdd 2)
            (sourceRoot wire member)
      change
        (if ((doubleCutIntroRaw source selection).wires wire).scope =
              (doubleCutIntroRaw source selection).root then
            some wire
          else none) =
          some (id wire)
      rw [if_pos targetRoot]
      rfl
    _ = some boundary := by simp

end VisualProof.Rule.ModalSoundness
