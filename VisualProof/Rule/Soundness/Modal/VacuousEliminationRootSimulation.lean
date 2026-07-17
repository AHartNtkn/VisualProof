import VisualProof.Rule.Soundness.Modal.VacuousEliminationRootCompiler

namespace VisualProof.Rule.VacuousElimTrace

open VisualProof
open VisualProof.Theory
open VisualProof.Diagram

theorem WireContext.index_eq_of_get_eq
    (context : ConcreteElaboration.WireContext diagram)
    (nodup : context.Nodup)
    (first second : Fin context.length)
    (equal : context.get first = context.get second) :
    first = second := by
  obtain ⟨index, lookup⟩ :=
    ConcreteElaboration.WireContext.lookup?_complete
      (List.get_mem context second)
  have firstEq : first = index :=
    ConcreteElaboration.WireContext.lookup?_unique nodup lookup equal
  have secondEq : second = index :=
    ConcreteElaboration.WireContext.lookup?_unique nodup lookup rfl
  exact firstEq.trans secondEq.symm

theorem WireContext.index_val_eq_of_context_eq
    {first second : ConcreteElaboration.WireContext diagram}
    (contextEq : first = second)
    (nodup : first.Nodup)
    (firstIndex : Fin first.length)
    (secondIndex : Fin second.length)
    (equal : first.get firstIndex = second.get secondIndex) :
    firstIndex.val = secondIndex.val := by
  subst second
  exact congrArg Fin.val
    (WireContext.index_eq_of_get_eq first nodup firstIndex secondIndex equal)

theorem rootScope_transport
    {first second : ConcreteDiagram}
    (diagramEq : first = second)
    (wire : Fin first.wireCount)
    (rootScope : (first.wires wire).scope = first.root) :
    (second.wires
      (Fin.cast (congrArg ConcreteDiagram.wireCount diagramEq) wire)).scope =
        second.root := by
  subst second
  exact rootScope

def concreteIsoOfEq {first second : ConcreteDiagram}
    (diagramEq : first = second) : ConcreteIso first second := by
  subst second
  exact ConcreteIso.refl first

theorem concreteIsoOfEq_wires_val
    {first second : ConcreteDiagram}
    (diagramEq : first = second)
    (wire : Fin first.wireCount) :
    ((concreteIsoOfEq diagramEq).wires wire).val = wire.val := by
  subst second
  rfl

noncomputable def rootContextSimulation
    (trace : VacuousElimTrace input outer raw)
    (sourceWellFormed : trace.sourceDiagram.WellFormed signature)
    (targetWellFormed : input.WellFormed signature)
    (boundary : List (Fin input.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.wires wire).scope = input.root)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (direction : ConcreteElaboration.SimulationDirection) :
    let source : CheckedOpenDiagram signature :=
      ⟨trace.sourceOpen boundary,
        trace.sourceOpen_wellFormed sourceWellFormed targetWellFormed boundary
          boundaryRoot⟩
    let target : CheckedOpenDiagram signature :=
      ⟨targetOpen input boundary,
        targetOpen_wellFormed targetWellFormed boundary boundaryRoot⟩
    let simulation := trace.semanticSimulation sourceWellFormed
      targetWellFormed model named
    ConcreteElaboration.ConcreteSemanticSimulation.RootContextSimulation
      simulation direction source.val.exposedWires source.val.hiddenWires
      target.val.exposedWires target.val.hiddenWires := by
  let source : CheckedOpenDiagram signature :=
    ⟨trace.sourceOpen boundary,
      trace.sourceOpen_wellFormed sourceWellFormed targetWellFormed boundary
        boundaryRoot⟩
  let target : CheckedOpenDiagram signature :=
    ⟨targetOpen input boundary,
      targetOpen_wellFormed targetWellFormed boundary boundaryRoot⟩
  let simulation := trace.semanticSimulation sourceWellFormed
    targetWellFormed model named
  let promoted := trace.rootContextWitness sourceWellFormed targetWellFormed
    boundary boundaryRoot
  let outerRelation := trace.wireIdentityRelation source.val.exposedWires
    target.val.exposedWires
  have exposedEq : source.val.exposedWires = target.val.exposedWires := rfl
  have sourceRootExact :
      ConcreteElaboration.WireContext.Exact
        (source.val.exposedWires ++ source.val.hiddenWires)
        trace.sourceDiagram.root := by
    simpa only [OpenConcreteDiagram.rootWires] using
      ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
        source
  have targetRootExact :
      ConcreteElaboration.WireContext.Exact
        (target.val.exposedWires ++ target.val.hiddenWires) input.root := by
    simpa only [OpenConcreteDiagram.rootWires] using
      ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
        target
  refine {
    outer := outerRelation
    context := PLift.up promoted
    atRoot := True.intro
    atRootChild := by intro; intros; trivial
    atFocusedRootChild := by intro; intros; trivial
    transport := ?_
    focusedRootKernel := ?_
  }
  · intro regular allowed sourceItems targetItems sourceCompiled
      targetCompiled itemSemantics
    have hiddenEq : source.val.hiddenWires = target.val.hiddenWires :=
      trace.sourceOpen_hiddenWires_eq_of_regular targetWellFormed boundary
        regular
    have relationMapEq :
        (simulation.relationMap simulation.binders_empty :
          RelationRenaming [] []) =
          (fun {arity} (relation : RelVar [] arity) => relation) := rfl
    rw [relationMapEq, ItemSeq.renameRelations_id] at itemSemantics ⊢
    apply ConcreteElaboration.directionalRootTransport_of_agreement direction
      source.val.exposedWires source.val.hiddenWires
      target.val.exposedWires target.val.hiddenWires outerRelation
      promoted.indexRelation model named sourceItems targetItems
    · intro sourceOuter targetOuter outerAgreement
      have outerEq : sourceOuter = targetOuter := by
        funext index
        exact outerAgreement index index rfl
      subst targetOuter
      let countEq : target.val.hiddenWires.length =
          source.val.hiddenWires.length := congrArg List.length hiddenEq.symm
      have rootContextEq :
          source.val.exposedWires ++ source.val.hiddenWires =
            target.val.exposedWires ++ target.val.hiddenWires := by
        rw [exposedEq, hiddenEq]
        rfl
      cases direction with
      | forward =>
          intro sourceLocal
          let targetLocal : Fin target.val.hiddenWires.length → model.Carrier :=
            fun index => sourceLocal (Fin.cast countEq index)
          refine ⟨targetLocal, ?_⟩
          intro sourceIndex targetIndex related
          have indexValue := WireContext.index_val_eq_of_context_eq
            rootContextEq sourceRootExact.nodup sourceIndex targetIndex related
          unfold ConcreteElaboration.rootEnvironment
          simp only [Function.comp_apply]
          apply VisualProof.Rule.ModalSoundness.extendWireEnv_transport
            countEq sourceLocal targetLocal
          · intro index
            rfl
          · exact indexValue
      | backward =>
          intro targetLocal
          let sourceLocal : Fin source.val.hiddenWires.length → model.Carrier :=
            fun index => targetLocal (Fin.cast countEq.symm index)
          refine ⟨sourceLocal, ?_⟩
          intro sourceIndex targetIndex related
          have indexValue := WireContext.index_val_eq_of_context_eq
            rootContextEq sourceRootExact.nodup sourceIndex targetIndex related
          unfold ConcreteElaboration.rootEnvironment
          simp only [Function.comp_apply]
          apply VisualProof.Rule.ModalSoundness.extendWireEnv_transport
            countEq sourceLocal targetLocal
          · intro index
            apply congrArg targetLocal
            apply Fin.ext
            rfl
          · exact indexValue
    · exact itemSemantics
  · intro atRoot focused allowed recurse recurseAt sourceItems targetItems
      sourceCompiled targetCompiled
    change trace.sourceDiagram.root = trace.targetIndex targetWellFormed
      at focused
    have targetAtRoot : trace.parent = input.root := by
      calc
        trace.parent = trace.origin (trace.targetIndex targetWellFormed) :=
          (trace.targetIndex_origin targetWellFormed).symm
        _ = trace.origin trace.sourceDiagram.root :=
          congrArg trace.origin focused.symm
        _ = input.root := trace.promotion.root_origin
    have rootOrigin : trace.origin trace.sourceDiagram.root = input.root :=
      trace.promotion.root_origin
    have sourceExact :
        ConcreteElaboration.WireContext.Exact
          (source.val.exposedWires ++ source.val.hiddenWires)
          (trace.targetIndex targetWellFormed) := by
      simpa only [focused] using sourceRootExact
    have targetExact :
        ConcreteElaboration.WireContext.Exact
          (target.val.exposedWires ++ target.val.hiddenWires)
          trace.parent := by
      simpa only [targetAtRoot] using targetRootExact
    have sourceCover :=
      ConcreteElaboration.BinderContext.empty_covers_root sourceWellFormed
    have targetCover :=
      ConcreteElaboration.BinderContext.empty_covers_root targetWellFormed
    have sourceEnumeration :=
      ConcreteElaboration.BinderContext.Enumeration.empty trace.sourceDiagram
    have targetEnumeration :=
      ConcreteElaboration.BinderContext.Enumeration.empty input
    have transport := trace.focusedRootItems_transport sourceWellFormed
      targetWellFormed model named direction trace.sourceDiagram.regionCount
      input.regionCount source.val.exposedWires source.val.hiddenWires
      target.val.exposedWires target.val.hiddenWires promoted
      ConcreteElaboration.BinderContext.empty
      ConcreteElaboration.BinderContext.empty simulation.binders_empty
      sourceExact targetExact
      (by simpa only [focused] using sourceCover)
      (by simpa only [targetAtRoot] using targetCover)
      (by simpa only [focused] using sourceEnumeration)
      (by simpa only [targetAtRoot] using targetEnumeration)
      (by
        intro wire member
        simpa only [exposedEq] using member)
      (by
        intro wire member
        simpa only [exposedEq] using member)
      (fun childFuelTarget childSourceContext childTargetContext childContext =>
        recurseAt childFuelTarget childSourceContext childTargetContext
          (PLift.up childContext))
      sourceItems targetItems
      (by simpa only [focused] using sourceCompiled)
      (by
        simpa only [simulation, semanticSimulation,
          rootOrigin, targetAtRoot] using targetCompiled)
    have relationMapEq :
        (simulation.relationMap simulation.binders_empty :
          RelationRenaming [] []) =
          (fun {arity} (relation : RelVar [] arity) => relation) := rfl
    rw [relationMapEq, Region.renameRelations_id]
    exact ConcreteElaboration.finishRoot_denote direction
      source.val.exposedWires source.val.hiddenWires
      target.val.exposedWires target.val.hiddenWires outerRelation model named
      sourceItems targetItems transport

theorem boundaryWitness
    (trace : VacuousElimTrace input outer raw)
    (sourceWellFormed : trace.sourceDiagram.WellFormed signature)
    (targetWellFormed : input.WellFormed signature)
    (boundary : List (Fin input.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.wires wire).scope = input.root)
    (direction : ConcreteElaboration.SimulationDirection)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin boundary.length → model.Carrier) :
    let source : CheckedOpenDiagram signature :=
      ⟨trace.sourceOpen boundary,
        trace.sourceOpen_wellFormed sourceWellFormed targetWellFormed boundary
          boundaryRoot⟩
    let target : CheckedOpenDiagram signature :=
      ⟨targetOpen input boundary,
        targetOpen_wellFormed targetWellFormed boundary boundaryRoot⟩
    let root := trace.rootContextSimulation sourceWellFormed targetWellFormed
      boundary boundaryRoot model named direction
    ConcreteElaboration.ConcreteSemanticSimulation.DirectionalBoundaryWitness
      direction source.elaborate target.elaborate root.outer model named
      args args := by
  let source : CheckedOpenDiagram signature :=
    ⟨trace.sourceOpen boundary,
      trace.sourceOpen_wellFormed sourceWellFormed targetWellFormed boundary
        boundaryRoot⟩
  let target : CheckedOpenDiagram signature :=
    ⟨targetOpen input boundary,
      targetOpen_wellFormed targetWellFormed boundary boundaryRoot⟩
  let root := trace.rootContextSimulation sourceWellFormed targetWellFormed
    boundary boundaryRoot model named direction
  have exposedEq : source.val.exposedWires = target.val.exposedWires := rfl
  have sourceRootExact :
      ConcreteElaboration.WireContext.Exact
        (source.val.exposedWires ++ source.val.hiddenWires)
        trace.sourceDiagram.root := by
    simpa only [OpenConcreteDiagram.rootWires] using
      ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
        source
  have sourceExposedNodup : source.val.exposedWires.Nodup :=
    (List.nodup_append.mp sourceRootExact.nodup).1
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
      intro sourceIndex targetIndex related
      have indexEq := WireContext.index_eq_of_get_eq
        source.val.exposedWires sourceExposedNodup sourceIndex targetIndex
        (by simpa only [exposedEq] using related)
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
      intro sourceIndex targetIndex related
      have indexEq := WireContext.index_eq_of_get_eq
        source.val.exposedWires sourceExposedNodup sourceIndex targetIndex
        (by simpa only [exposedEq] using related)
      subst targetIndex
      rfl

theorem interfaceTransport_transportBoundary
    (hraw : vacuousElimRaw? input outer = some raw)
    (wellFormed : input.WellFormed signature)
    (boundary : List (Fin input.wireCount))
    (sourceRoot : ∀ wire, wire ∈ boundary →
      (input.wires wire).scope = input.root) :
    (vacuousElimInterfaceTransport hraw).transportBoundary boundary =
      some (boundary.map
        (Fin.cast (vacuousElimRaw?_wireCount hraw).symm)) := by
  let trace := vacuousElimTrace hraw
  have rawEq : raw = trace.sourceDiagram := trace.promotion.raw_eq_diagram
  let wireCountEq : input.wireCount = raw.wireCount :=
    (vacuousElimRaw?_wireCount hraw).symm
  apply InterfaceTransport.transportBoundary_eq_map
  intro wire member
  unfold vacuousElimInterfaceTransport InterfaceTransport.byWireCount
    InterfaceTransport.rootFiltered
  dsimp only
  have promotedRoot :
      (raw.wires (Fin.cast wireCountEq wire)).scope = raw.root := by
    have promoted := trace.targetRoot_scope_promoted
      (signature := signature) wellFormed wire (sourceRoot wire member)
    have transported := rootScope_transport rawEq.symm wire promoted
    have castEq :
        Fin.cast (congrArg ConcreteDiagram.wireCount rawEq.symm) wire =
          Fin.cast wireCountEq wire := by
      apply Fin.ext
      rfl
    rwa [castEq] at transported
  change
    (if (raw.wires (Fin.cast wireCountEq wire)).scope = raw.root then
        some (Fin.cast wireCountEq wire)
      else none) = some (Fin.cast wireCountEq wire)
  rw [if_pos promotedRoot]

end VisualProof.Rule.VacuousElimTrace
