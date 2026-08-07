import VisualProof.Rule.Soundness.Modal.FocusedItems

namespace VisualProof.Rule.ModalSoundness

open VisualProof.Concrete

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Theory
open VisualProof.Diagram

def doubleCutIntroRawOpen
    (source : Concrete.OpenDiagram)
    (selection : CheckedSelection source.diagram) :
    Concrete.OpenDiagram where
  diagram := doubleCutIntroRaw source.diagram selection
  boundary := source.boundary

@[simp] theorem doubleCutIntroRawOpen_exposedWires
    (source : Concrete.OpenDiagram)
    (selection : CheckedSelection source.diagram) :
    (doubleCutIntroRawOpen source selection).exposedWires =
      source.exposedWires := by
  rfl

@[simp] theorem doubleCutIntroRawOpen_hiddenWires
    (source : Concrete.OpenDiagram)
    (selection : CheckedSelection source.diagram) :
    (doubleCutIntroRawOpen source selection).hiddenWires =
      source.hiddenWires := by
  unfold Concrete.OpenDiagram.hiddenWires
  change
    (Concrete.Elaboration.exactScopeWires
      (doubleCutIntroRaw source.diagram selection)
      (doubleCutIntroRaw source.diagram selection).root).filter
        (fun wire => decide (wire ∉ source.exposedWires)) =
      (Concrete.Elaboration.exactScopeWires source.diagram
        source.diagram.root).filter
          (fun wire => decide (wire ∉ source.exposedWires))
  rw [doubleCutIntroRaw_root,
    doubleCutIntroRaw_exactScopeWires]

@[simp] theorem doubleCutIntroRawOpen_rootWires
    (source : Concrete.OpenDiagram)
    (selection : CheckedSelection source.diagram) :
    (doubleCutIntroRawOpen source selection).rootWires =
      source.rootWires := by
  unfold Concrete.OpenDiagram.rootWires
  rw [doubleCutIntroRawOpen_exposedWires,
    doubleCutIntroRawOpen_hiddenWires]
  rfl

theorem doubleCutIntroRawOpen_wellFormed
    (source : Concrete.CheckedOpen )
    (selection : CheckedSelection source.val.diagram)
    (targetWellFormed :
      (doubleCutIntroRaw source.val.diagram selection).WellFormed ) :
    (doubleCutIntroRawOpen source.val selection).WellFormed  := by
  refine {
    diagram_well_formed := targetWellFormed
    boundary_is_root_scoped := ?_
  }
  intro wire member
  have sourceScoped := source.property.boundary_is_root_scoped wire member
  simpa [doubleCutIntroRawOpen, doubleCutIntroRaw_wire,
    doubleCutIntroRaw_root, liftCWireRegions, sourceScoped]

noncomputable def doubleCutIntroRootContext
    (source : Concrete.CheckedOpen )
    (selection : CheckedSelection source.val.diagram)
    (targetWellFormed :
      (doubleCutIntroRaw source.val.diagram selection).WellFormed )
    (model : Model)
    (direction : Concrete.Elaboration.SimulationDirection) :
    let simulation := doubleCutIntroSimulation
      ⟨source.val.diagram, source.property.diagram_well_formed⟩ selection
      targetWellFormed model
    Concrete.Elaboration.ConcreteSemanticSimulation.RootContextSimulation
      simulation direction
      source.val.exposedWires source.val.hiddenWires
      (doubleCutIntroRawOpen source.val selection).exposedWires
      (doubleCutIntroRawOpen source.val selection).hiddenWires := by
  let input : Concrete.Checked  :=
    ⟨source.val.diagram, source.property.diagram_well_formed⟩
  let simulation := doubleCutIntroSimulation input selection targetWellFormed
    model
  let target : Concrete.CheckedOpen  :=
    ⟨doubleCutIntroRawOpen source.val selection,
      doubleCutIntroRawOpen_wellFormed source selection targetWellFormed⟩
  change Concrete.Elaboration.ConcreteSemanticSimulation.RootContextSimulation
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
    Concrete.Elaboration.ContextIndexRelation.forwardMap outerMap
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
    apply Concrete.Elaboration.directionalRootTransport_of_agreement
      direction source.val.exposedWires source.val.hiddenWires
      target.val.exposedWires target.val.hiddenWires outerRelation
      combinedContext.indexRelation model
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
          (Concrete.Elaboration.ContextIndexRelation.environmentsAgree_forwardMap
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
            Concrete.Elaboration.ContextIndexRelation.EnvironmentsAgree
            Concrete.Elaboration.ContextIndexRelation.forwardMap
          intro sourceIndex targetIndex related
          subst targetIndex
          unfold Concrete.Elaboration.rootEnvironment
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
            Concrete.Elaboration.ContextIndexRelation.EnvironmentsAgree
            Concrete.Elaboration.ContextIndexRelation.forwardMap
          intro sourceIndex targetIndex related
          subst targetIndex
          unfold Concrete.Elaboration.rootEnvironment
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
        Concrete.Elaboration.WireContext.Exact
          (source.val.exposedWires ++ source.val.hiddenWires)
          source.val.diagram.root := by
      simpa only [Concrete.OpenDiagram.rootWires] using
        Concrete.Elaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
          source
    have targetExact :
        @Concrete.Elaboration.WireContext.Exact target.val.diagram
          (target.val.exposedWires ++ target.val.hiddenWires :
            Concrete.Elaboration.WireContext target.val.diagram)
          target.val.diagram.root := by
      simpa only [Concrete.OpenDiagram.rootWires] using
        Concrete.Elaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
          target
    change input.val.root = selection.val.anchor at focused
    have itemSimulation :=
      doubleCutIntroFocusedItems input selection targetWellFormed model
        direction input.val.regionCount
        (doubleCutIntroRaw input.val selection).regionCount
        (source.val.exposedWires ++ source.val.hiddenWires)
        (target.val.exposedWires ++ target.val.hiddenWires)
        combinedContext
        Concrete.Elaboration.BinderContext.empty
        Concrete.Elaboration.BinderContext.empty
        simulation.binders_empty (by simpa only [← focused] using sourceExact)
        (by
          simpa only [simulation.root_eq, ← focused] using targetExact)
        (by
          simpa only [← focused] using
            Concrete.Elaboration.BinderContext.empty_covers_root
              source.property.diagram_well_formed)
        (by
          simpa only [simulation.root_eq, ← focused] using
            Concrete.Elaboration.BinderContext.empty_covers_root
              target.property.diagram_well_formed)
        (by
          simpa only [← focused] using
            Concrete.Elaboration.BinderContext.Enumeration.empty
              source.val.diagram)
        (by
          simpa only [simulation.root_eq, ← focused] using
            Concrete.Elaboration.BinderContext.Enumeration.empty
              target.val.diagram)
        recurseAt sourceItems targetItems
        (by simpa only [← focused] using sourceCompiled)
        (by
          change
            Concrete.Elaboration.compileOccurrencesWith?
              (doubleCutIntroRaw input.val selection)
              (Concrete.Elaboration.compileRegion?
                (doubleCutIntroRaw input.val selection)
                (doubleCutIntroRaw input.val selection).regionCount)
              (target.val.exposedWires ++ target.val.hiddenWires)
              Concrete.Elaboration.BinderContext.empty
              (Concrete.Elaboration.localOccurrences
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
    apply Concrete.Elaboration.finishRoot_denote direction
      source.val.exposedWires source.val.hiddenWires
      target.val.exposedWires target.val.hiddenWires outerRelation model
    apply Concrete.Elaboration.directionalRootTransport_of_agreement
      direction source.val.exposedWires source.val.hiddenWires
      target.val.exposedWires target.val.hiddenWires outerRelation
      combinedContext.indexRelation model  sourceItems targetItems
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
          (Concrete.Elaboration.ContextIndexRelation.environmentsAgree_forwardMap
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
            Concrete.Elaboration.ContextIndexRelation.EnvironmentsAgree
            Concrete.Elaboration.ContextIndexRelation.forwardMap
          intro sourceIndex targetIndex related
          subst targetIndex
          unfold Concrete.Elaboration.rootEnvironment
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
            Concrete.Elaboration.ContextIndexRelation.EnvironmentsAgree
            Concrete.Elaboration.ContextIndexRelation.forwardMap
          intro sourceIndex targetIndex related
          subst targetIndex
          unfold Concrete.Elaboration.rootEnvironment
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
    (source : Concrete.CheckedOpen )
    (selection : CheckedSelection source.val.diagram)
    (targetWellFormed :
      (doubleCutIntroRaw source.val.diagram selection).WellFormed )
    (direction : Concrete.Elaboration.SimulationDirection)
    (model : Model)
    (args : Fin source.val.boundary.length → model.Carrier) :
    let target : Concrete.CheckedOpen  :=
      ⟨doubleCutIntroRawOpen source.val selection,
        doubleCutIntroRawOpen_wellFormed source selection targetWellFormed⟩
    Concrete.Elaboration.ConcreteSemanticSimulation.DirectionalBoundaryWitness
      direction source.elaborate target.elaborate
      (doubleCutIntroRootContext source selection targetWellFormed model
        direction).outer
      model  args args := by
  let target : Concrete.CheckedOpen  :=
    ⟨doubleCutIntroRawOpen source.val selection,
      doubleCutIntroRawOpen_wellFormed source selection targetWellFormed⟩
  dsimp only
  unfold
    Concrete.Elaboration.ConcreteSemanticSimulation.DirectionalBoundaryWitness
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
      unfold Concrete.Elaboration.ContextIndexRelation.EnvironmentsAgree
      intro sourceIndex targetIndex related
      simp [doubleCutIntroRootContext,
        Concrete.Elaboration.ContextIndexRelation.forwardMap] at related
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
      unfold Concrete.Elaboration.ContextIndexRelation.EnvironmentsAgree
      intro sourceIndex targetIndex related
      simp [doubleCutIntroRootContext,
        Concrete.Elaboration.ContextIndexRelation.forwardMap] at related
      subst targetIndex
      rfl

theorem doubleCutIntroWireTransport_transportBoundary
    (source : Concrete.Diagram)
    (selection : CheckedSelection source)
    (boundary : List (Fin source.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (source.wires wire).scope = source.root) :
    (doubleCutIntroWireTransport source selection).transportBoundary
        boundary =
      some boundary := by
  calc
    _ = some (boundary.map id) := by
      apply WireTransport.transportBoundary_eq_map
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
