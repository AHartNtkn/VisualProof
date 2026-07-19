import VisualProof.Rule.Soundness.Comprehension.InstantiationFinalOpen
import VisualProof.Rule.Soundness.Modal.EliminationRoot

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram
open VisualProof.Theory
open DoubleCutElimTrace

namespace InstantiationTrace
namespace FinalContextWitness

theorem sourceIndex_injective
    (witness : FinalContextWitness copyTrace elimTrace sourceContext
      targetContext)
    (sourceNodup : sourceContext.Nodup)
    (targetNodup : targetContext.Nodup)
    (wireInjective : Function.Injective
      (copyTrace.finalWireMap elimTrace)) :
    Function.Injective witness.sourceIndex := by
  intro first second equal
  have mappedWiresEqual :
      copyTrace.finalWireMap elimTrace (targetContext.get first) =
        copyTrace.finalWireMap elimTrace (targetContext.get second) := by
    rw [← witness.sourceIndex_get first, ← witness.sourceIndex_get second,
      equal]
  have wiresEqual := wireInjective mappedWiresEqual
  apply Fin.ext
  exact (List.getElem_inj targetNodup).mp (by
    simpa only [List.get_eq_getElem] using wiresEqual)

/-- Extend an original complete-root valuation across executor-created final
root wires, fixing every certified image and using an arbitrary fallback only
on genuinely new wires. -/
noncomputable def sourceEnvironment
    (witness : FinalContextWitness copyTrace elimTrace sourceContext
      targetContext)
    (sourceNodup : sourceContext.Nodup)
    (targetNodup : targetContext.Nodup)
    (wireInjective : Function.Injective
      (copyTrace.finalWireMap elimTrace))
    (fallback : D)
    (targetEnvironment : Fin targetContext.length → D) :
    Fin sourceContext.length → D :=
  fun sourceIndex =>
    if preimage : ∃ targetIndex, witness.sourceIndex targetIndex = sourceIndex then
      targetEnvironment (Classical.choose preimage)
    else fallback

theorem sourceEnvironment_sourceIndex
    (witness : FinalContextWitness copyTrace elimTrace sourceContext
      targetContext)
    (sourceNodup : sourceContext.Nodup)
    (targetNodup : targetContext.Nodup)
    (wireInjective : Function.Injective
      (copyTrace.finalWireMap elimTrace))
    (fallback : D)
    (targetEnvironment : Fin targetContext.length → D)
    (targetIndex : Fin targetContext.length) :
    witness.sourceEnvironment sourceNodup targetNodup wireInjective fallback
        targetEnvironment (witness.sourceIndex targetIndex) =
      targetEnvironment targetIndex := by
  let preimage : ∃ candidate,
      witness.sourceIndex candidate = witness.sourceIndex targetIndex :=
    ⟨targetIndex, rfl⟩
  rw [sourceEnvironment, dif_pos preimage]
  exact congrArg targetEnvironment
    (witness.sourceIndex_injective sourceNodup targetNodup wireInjective
      (Classical.choose_spec preimage))

theorem sourceEnvironment_agrees
    (witness : FinalContextWitness copyTrace elimTrace sourceContext
      targetContext)
    (sourceNodup : sourceContext.Nodup)
    (targetNodup : targetContext.Nodup)
    (wireInjective : Function.Injective
      (copyTrace.finalWireMap elimTrace))
    (fallback : D)
    (targetEnvironment : Fin targetContext.length → D) :
    witness.indexRelation.EnvironmentsAgree
      (witness.sourceEnvironment sourceNodup targetNodup wireInjective fallback
        targetEnvironment)
      targetEnvironment := by
  apply (ConcreteElaboration.ContextIndexRelation.environmentsAgree_backwardMap
    _ _ _).2
  funext targetIndex
  exact witness.sourceEnvironment_sourceIndex sourceNodup targetNodup
    wireInjective fallback targetEnvironment targetIndex

end FinalContextWitness

variable {signature : List Nat}
  {input : CheckedDiagram signature}
  {bubble : Fin input.val.regionCount}
  {comprehension : CheckedOpenDiagram signature}
  {attachments : List (Fin input.val.wireCount)}
  {binders : List
    (Fin comprehension.val.diagram.regionCount × Fin input.val.regionCount)}
  {payload : ComprehensionInstantiatePayload input bubble comprehension
    attachments binders}
  {fuel : Nat}
  {result : InstantiationState input attachments.length
    payload.binderSpine.proxyCount}
  {raw : ConcreteDiagram}

/-- Root valuation selection for the exact mapped ordered boundary.  This is
the root analogue of `regularEnvironmentSelection`: target root wires embed
injectively in the final root, while any executor-created final root wires are
existentially filled. -/
theorem finalRootEnvironmentSelection
    (copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result)
    (elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw)
    (sourceWellFormed : elimTrace.sourceDiagram.WellFormed signature)
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (boundaryNodup : comprehension.val.boundary.Nodup)
    (boundary : List (Fin input.val.wireCount))
    (boundaryRoot : ∀ wire, wire ∈ boundary →
      (input.val.wires wire).scope = input.val.root)
    (direction : ConcreteElaboration.SimulationDirection)
    [Nonempty D] :
    let source : CheckedOpenDiagram signature :=
      ⟨copyTrace.finalSourceOpen elimTrace boundary,
        copyTrace.finalSourceOpen_wellFormed elimTrace sourceWellFormed
          finalWellFormed boundaryNodup boundary boundaryRoot⟩
    let target : CheckedOpenDiagram signature :=
      ⟨finalTargetOpen input boundary,
        finalTargetOpen_wellFormed input boundary boundaryRoot⟩
    let outer := copyTrace.finalOuterContextWitness elimTrace boundaryNodup
      boundary
    let combined := copyTrace.finalRootContextWitness elimTrace
      finalWellFormed boundaryNodup boundary boundaryRoot sourceWellFormed
    ∀ (sourceOuter : Fin source.val.exposedWires.length → D)
      (targetOuter : Fin target.val.exposedWires.length → D),
      outer.indexRelation.EnvironmentsAgree sourceOuter targetOuter →
        match direction with
        | .forward => ∀ sourceLocal,
            ∃ targetLocal,
              combined.indexRelation.EnvironmentsAgree
                (ConcreteElaboration.rootEnvironment source.val.exposedWires
                  source.val.hiddenWires sourceOuter sourceLocal)
                (ConcreteElaboration.rootEnvironment target.val.exposedWires
                  target.val.hiddenWires targetOuter targetLocal)
        | .backward => ∀ targetLocal,
            ∃ sourceLocal,
              combined.indexRelation.EnvironmentsAgree
                (ConcreteElaboration.rootEnvironment source.val.exposedWires
                  source.val.hiddenWires sourceOuter sourceLocal)
                (ConcreteElaboration.rootEnvironment target.val.exposedWires
                  target.val.hiddenWires targetOuter targetLocal) := by
  dsimp only
  let source : CheckedOpenDiagram signature :=
    ⟨copyTrace.finalSourceOpen elimTrace boundary,
      copyTrace.finalSourceOpen_wellFormed elimTrace sourceWellFormed
        finalWellFormed boundaryNodup boundary boundaryRoot⟩
  let target : CheckedOpenDiagram signature :=
    ⟨finalTargetOpen input boundary,
      finalTargetOpen_wellFormed input boundary boundaryRoot⟩
  let outer := copyTrace.finalOuterContextWitness elimTrace boundaryNodup
    boundary
  let combined := copyTrace.finalRootContextWitness elimTrace finalWellFormed
    boundaryNodup boundary boundaryRoot sourceWellFormed
  have sourceRootExact : ConcreteElaboration.WireContext.Exact
      source.val.rootWires source.val.diagram.root :=
    ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
      source
  have targetRootExact : ConcreteElaboration.WireContext.Exact
      target.val.rootWires target.val.diagram.root :=
    ConcreteElaboration.ConcreteSemanticSimulation.checkedOpen_rootContext_exact
      target
  have outerGet (targetIndex : Fin target.val.exposedWires.length) :
      combined.sourceIndex
          (rootOuterIndex target.val.exposedWires target.val.hiddenWires
            targetIndex) =
        rootOuterIndex source.val.exposedWires source.val.hiddenWires
          (outer.sourceIndex targetIndex) := by
    symm
    apply ConcreteElaboration.WireContext.lookup?_unique sourceRootExact.nodup
      (combined.sourceIndex_lookup
        (rootOuterIndex target.val.exposedWires target.val.hiddenWires
          targetIndex))
    calc
      source.val.rootWires.get
          (rootOuterIndex source.val.exposedWires source.val.hiddenWires
            (outer.sourceIndex targetIndex)) =
          source.val.exposedWires.get (outer.sourceIndex targetIndex) :=
        rootOuterIndex_get _ _ _
      _ = copyTrace.finalWireMap elimTrace
          (target.val.exposedWires.get targetIndex) :=
        outer.sourceIndex_get targetIndex
      _ = copyTrace.finalWireMap elimTrace
          (target.val.rootWires.get
            (rootOuterIndex target.val.exposedWires target.val.hiddenWires
              targetIndex)) := congrArg (copyTrace.finalWireMap elimTrace)
        (rootOuterIndex_get _ _ _).symm
  intro sourceOuter targetOuter outerAgreement
  cases direction with
  | forward =>
      intro sourceLocal
      let sourceEnvironment := ConcreteElaboration.rootEnvironment
        source.val.exposedWires source.val.hiddenWires sourceOuter sourceLocal
      let targetEnvironment := combined.targetEnvironment sourceEnvironment
      let targetLocal := rootLocalPart target.val.exposedWires
        target.val.hiddenWires targetEnvironment
      refine ⟨targetLocal, ?_⟩
      have targetEnvironmentEq :
          ConcreteElaboration.rootEnvironment target.val.exposedWires
              target.val.hiddenWires targetOuter targetLocal =
            targetEnvironment := by
        apply rootEnvironment_of_parts
        intro targetIndex
        change sourceEnvironment
            (combined.sourceIndex
              (rootOuterIndex target.val.exposedWires target.val.hiddenWires
                targetIndex)) = targetOuter targetIndex
        rw [outerGet targetIndex]
        dsimp only [sourceEnvironment]
        rw [rootEnvironment_outer]
        exact outerAgreement (outer.sourceIndex targetIndex) targetIndex rfl
      rw [targetEnvironmentEq]
      exact combined.targetEnvironment_agrees sourceEnvironment
  | backward =>
      intro targetLocal
      let targetEnvironment := ConcreteElaboration.rootEnvironment
        target.val.exposedWires target.val.hiddenWires targetOuter targetLocal
      let fallback : D := Classical.choice inferInstance
      let sourceEnvironment := combined.sourceEnvironment sourceRootExact.nodup
        targetRootExact.nodup
        (copyTrace.finalWireMap_injective elimTrace boundaryNodup) fallback
        targetEnvironment
      let sourceLocal := rootLocalPart source.val.exposedWires
        source.val.hiddenWires sourceEnvironment
      refine ⟨sourceLocal, ?_⟩
      have sourceEnvironmentEq :
          ConcreteElaboration.rootEnvironment source.val.exposedWires
              source.val.hiddenWires sourceOuter sourceLocal =
            sourceEnvironment := by
        apply rootEnvironment_of_parts
        intro sourceIndex
        have exposedEq := copyTrace.finalSourceOpen_exposedWires elimTrace
          boundaryNodup boundary
        have sourceLengthEq : source.val.exposedWires.length =
            target.val.exposedWires.length := by
          calc
            source.val.exposedWires.length =
                (target.val.exposedWires.map
                  (copyTrace.finalWireMap elimTrace)).length :=
              congrArg List.length exposedEq
            _ = target.val.exposedWires.length := List.length_map _
        let targetIndex : Fin target.val.exposedWires.length :=
          Fin.cast sourceLengthEq sourceIndex
        have mappedGet : source.val.exposedWires.get sourceIndex =
            copyTrace.finalWireMap elimTrace
              (target.val.exposedWires.get targetIndex) := by
          have transported := List.get_of_eq exposedEq sourceIndex
          rw [transported]
          have mappedValid : sourceIndex.val <
              (target.val.exposedWires.map
                (copyTrace.finalWireMap elimTrace)).length := by
            rw [List.length_map]
            exact targetIndex.isLt
          let mappedIndex : Fin (target.val.exposedWires.map
              (copyTrace.finalWireMap elimTrace)).length :=
            ⟨sourceIndex.val, mappedValid⟩
          change (target.val.exposedWires.map
              (copyTrace.finalWireMap elimTrace)).get mappedIndex =
            copyTrace.finalWireMap elimTrace
              (target.val.exposedWires.get targetIndex)
          simp only [List.get_eq_getElem]
          rw [List.getElem_map]
          rfl
        have combinedIndex : combined.sourceIndex
              (rootOuterIndex target.val.exposedWires target.val.hiddenWires
                targetIndex) =
            rootOuterIndex source.val.exposedWires source.val.hiddenWires
              sourceIndex := by
          symm
          apply ConcreteElaboration.WireContext.lookup?_unique
            sourceRootExact.nodup
            (combined.sourceIndex_lookup
              (rootOuterIndex target.val.exposedWires target.val.hiddenWires
                targetIndex))
          calc
            source.val.rootWires.get
                (rootOuterIndex source.val.exposedWires
                  source.val.hiddenWires sourceIndex) =
                source.val.exposedWires.get sourceIndex :=
              rootOuterIndex_get _ _ _
            _ = copyTrace.finalWireMap elimTrace
                (target.val.exposedWires.get targetIndex) := mappedGet
            _ = copyTrace.finalWireMap elimTrace
                (target.val.rootWires.get
                  (rootOuterIndex target.val.exposedWires
                    target.val.hiddenWires targetIndex)) :=
              congrArg (copyTrace.finalWireMap elimTrace)
                (rootOuterIndex_get _ _ _).symm
        change sourceEnvironment
            (rootOuterIndex source.val.exposedWires source.val.hiddenWires
              sourceIndex) = sourceOuter sourceIndex
        rw [← combinedIndex]
        have outerIndexEq : outer.sourceIndex targetIndex = sourceIndex := by
          symm
          apply ConcreteElaboration.WireContext.lookup?_unique
            (List.nodup_append.mp sourceRootExact.nodup).1
            (outer.sourceIndex_lookup targetIndex)
          exact mappedGet
        calc
          sourceEnvironment
              (combined.sourceIndex
                (rootOuterIndex target.val.exposedWires target.val.hiddenWires
                  targetIndex)) =
              targetEnvironment
                (rootOuterIndex target.val.exposedWires target.val.hiddenWires
                  targetIndex) :=
            combined.sourceEnvironment_sourceIndex sourceRootExact.nodup
              targetRootExact.nodup
              (copyTrace.finalWireMap_injective elimTrace boundaryNodup)
              fallback targetEnvironment _
          _ = targetOuter targetIndex := rootEnvironment_outer _ _ _ _ _
          _ = sourceOuter (outer.sourceIndex targetIndex) :=
            (outerAgreement (outer.sourceIndex targetIndex) targetIndex rfl).symm
          _ = sourceOuter sourceIndex := congrArg sourceOuter outerIndexEq
      rw [sourceEnvironmentEq]
      exact combined.sourceEnvironment_agrees sourceRootExact.nodup
        targetRootExact.nodup
        (copyTrace.finalWireMap_injective elimTrace boundaryNodup) fallback
        targetEnvironment

end InstantiationTrace

end VisualProof.Rule
