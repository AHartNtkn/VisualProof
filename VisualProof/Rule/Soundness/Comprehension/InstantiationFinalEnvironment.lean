import VisualProof.Rule.Soundness.Comprehension.InstantiationFinalBinder
import VisualProof.Rule.Soundness.Modal.EliminationFocusedItems

namespace VisualProof.Rule

open VisualProof
open VisualProof.Diagram

namespace InstantiationTrace
namespace FinalContextWitness

/-- Extend a target local valuation across executor-only source wires while
fixing every certified image of an original local wire. -/
noncomputable def sourceLocalEnvironment
    {signature : List Nat}
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
    {copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result}
    {raw : ConcreteDiagram}
    {elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw}
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (boundaryNodup : comprehension.val.boundary.Nodup)
    (finalRegion : Fin elimTrace.sourceDiagram.regionCount)
    (originalRegion : Fin input.val.regionCount)
    (mappedRegion : copyTrace.finalRegionMap elimTrace finalWellFormed
      originalRegion = finalRegion)
    [Nonempty D]
    (targetLocal : Fin (ConcreteElaboration.exactScopeWires input.val
      originalRegion).length → D) :
    Fin (ConcreteElaboration.exactScopeWires elimTrace.sourceDiagram
      finalRegion).length → D :=
  fun sourceIndex =>
    if preimage : ∃ targetIndex,
        localSourceIndex finalWellFormed boundaryNodup finalRegion
          originalRegion mappedRegion targetIndex = sourceIndex then
      targetLocal (Classical.choose preimage)
    else Classical.choice inferInstance

theorem sourceLocalEnvironment_image
    {signature : List Nat}
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
    {copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result}
    {raw : ConcreteDiagram}
    {elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw}
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (boundaryNodup : comprehension.val.boundary.Nodup)
    (finalRegion : Fin elimTrace.sourceDiagram.regionCount)
    (originalRegion : Fin input.val.regionCount)
    (mappedRegion : copyTrace.finalRegionMap elimTrace finalWellFormed
      originalRegion = finalRegion)
    [Nonempty D]
    (targetLocal : Fin (ConcreteElaboration.exactScopeWires input.val
      originalRegion).length → D)
    (targetIndex : Fin (ConcreteElaboration.exactScopeWires input.val
      originalRegion).length) :
    sourceLocalEnvironment finalWellFormed boundaryNodup finalRegion
        originalRegion mappedRegion targetLocal
        (localSourceIndex finalWellFormed boundaryNodup finalRegion
          originalRegion mappedRegion targetIndex) =
      targetLocal targetIndex := by
  let preimage : ∃ candidate,
      localSourceIndex finalWellFormed boundaryNodup finalRegion
          originalRegion mappedRegion candidate =
        localSourceIndex finalWellFormed boundaryNodup finalRegion
          originalRegion mappedRegion targetIndex := ⟨targetIndex, rfl⟩
  rw [sourceLocalEnvironment, dif_pos preimage]
  have chosenEq := localSourceIndex_injective finalWellFormed boundaryNodup
    finalRegion originalRegion mappedRegion (Classical.choose_spec preimage)
  rw [chosenEq]

theorem regularTargetEnvironment_outer
    {signature : List Nat}
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
    {copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result}
    {raw : ConcreteDiagram}
    {elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw}
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (boundaryNodup : comprehension.val.boundary.Nodup)
    (sourceContext : ConcreteElaboration.WireContext
      elimTrace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input.val)
    (context : FinalContextWitness copyTrace elimTrace sourceContext
      targetContext)
    (finalRegion : Fin elimTrace.sourceDiagram.regionCount)
    (regular : copyTrace.FinalRegularPreimage elimTrace finalWellFormed
      finalRegion)
    (sourceExact : (sourceContext.extend finalRegion).Exact finalRegion)
    (sourceOuter : Fin sourceContext.length → D)
    (targetOuter : Fin targetContext.length → D)
    (outerAgreement : context.indexRelation.EnvironmentsAgree sourceOuter
      targetOuter)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires
      elimTrace.sourceDiagram finalRegion).length → D)
    (targetIndex : Fin targetContext.length) :
    let originalRegion := copyTrace.reverseRegionMap elimTrace finalWellFormed
      finalRegion
    let extended := context.extendRegular finalWellFormed boundaryNodup
      finalRegion regular
    extended.targetEnvironment
        (ConcreteElaboration.extendedEnvironment sourceContext finalRegion
          sourceOuter sourceLocal)
        (DoubleCutElimTrace.extendedOuterIndex targetContext originalRegion
          targetIndex) =
      targetOuter targetIndex := by
  dsimp only
  let originalRegion := copyTrace.reverseRegionMap elimTrace finalWellFormed
    finalRegion
  let extended := context.extendRegular finalWellFormed boundaryNodup
    finalRegion regular
  let sourceIndex := context.sourceIndex targetIndex
  let sourceExtendedIndex := DoubleCutElimTrace.extendedOuterIndex
    sourceContext finalRegion sourceIndex
  let targetExtendedIndex := DoubleCutElimTrace.extendedOuterIndex
    targetContext originalRegion targetIndex
  have corresponding :
      (sourceContext.extend finalRegion).get sourceExtendedIndex =
        copyTrace.finalWireMap elimTrace
          ((targetContext.extend originalRegion).get targetExtendedIndex) := by
    calc
      _ = sourceContext.get sourceIndex :=
        DoubleCutElimTrace.extendedOuterIndex_get sourceContext finalRegion
          sourceIndex
      _ = copyTrace.finalWireMap elimTrace (targetContext.get targetIndex) :=
        context.sourceIndex_get targetIndex
      _ = _ := congrArg (copyTrace.finalWireMap elimTrace)
        (DoubleCutElimTrace.extendedOuterIndex_get targetContext
          originalRegion targetIndex).symm
  have sourceExtendedIndexEq : sourceExtendedIndex =
      extended.sourceIndex targetExtendedIndex :=
    ConcreteElaboration.WireContext.lookup?_unique sourceExact.nodup
      (extended.sourceIndex_lookup targetExtendedIndex) corresponding
  change extended.targetEnvironment
      (ConcreteElaboration.extendedEnvironment sourceContext finalRegion
        sourceOuter sourceLocal) targetExtendedIndex = targetOuter targetIndex
  unfold targetEnvironment
  simp only [Function.comp_apply]
  rw [← sourceExtendedIndexEq]
  rw [DoubleCutElimTrace.extendedEnvironment_outer]
  exact outerAgreement sourceIndex targetIndex rfl

theorem regularTargetEnvironment_local
    {signature : List Nat}
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
    {copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result}
    {raw : ConcreteDiagram}
    {elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw}
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (boundaryNodup : comprehension.val.boundary.Nodup)
    (sourceContext : ConcreteElaboration.WireContext
      elimTrace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input.val)
    (context : FinalContextWitness copyTrace elimTrace sourceContext
      targetContext)
    (finalRegion : Fin elimTrace.sourceDiagram.regionCount)
    (regular : copyTrace.FinalRegularPreimage elimTrace finalWellFormed
      finalRegion)
    (sourceExact : (sourceContext.extend finalRegion).Exact finalRegion)
    (sourceOuter : Fin sourceContext.length → D)
    (sourceLocal : Fin (ConcreteElaboration.exactScopeWires
      elimTrace.sourceDiagram finalRegion).length → D)
    (targetIndex : Fin (ConcreteElaboration.exactScopeWires input.val
      (copyTrace.reverseRegionMap elimTrace finalWellFormed finalRegion)).length) :
    let originalRegion := copyTrace.reverseRegionMap elimTrace finalWellFormed
      finalRegion
    let mappedRegion := copyTrace.finalRegionMap_reverseRegionMap elimTrace
      finalWellFormed finalRegion regular
    let extended := context.extendRegular finalWellFormed boundaryNodup
      finalRegion regular
    extended.targetEnvironment
        (ConcreteElaboration.extendedEnvironment sourceContext finalRegion
          sourceOuter sourceLocal)
        (DoubleCutElimTrace.extendedLocalIndex targetContext originalRegion
          targetIndex) =
      sourceLocal (localSourceIndex finalWellFormed boundaryNodup finalRegion
        originalRegion mappedRegion targetIndex) := by
  dsimp only
  let originalRegion := copyTrace.reverseRegionMap elimTrace finalWellFormed
    finalRegion
  let mappedRegion := copyTrace.finalRegionMap_reverseRegionMap elimTrace
    finalWellFormed finalRegion regular
  let extended := context.extendRegular finalWellFormed boundaryNodup
    finalRegion regular
  let sourceLocalIndex := localSourceIndex finalWellFormed boundaryNodup
    finalRegion originalRegion mappedRegion targetIndex
  let sourceExtendedIndex := DoubleCutElimTrace.extendedLocalIndex
    sourceContext finalRegion sourceLocalIndex
  let targetExtendedIndex := DoubleCutElimTrace.extendedLocalIndex
    targetContext originalRegion targetIndex
  have corresponding :
      (sourceContext.extend finalRegion).get sourceExtendedIndex =
        copyTrace.finalWireMap elimTrace
          ((targetContext.extend originalRegion).get targetExtendedIndex) := by
    calc
      _ = (ConcreteElaboration.exactScopeWires elimTrace.sourceDiagram
          finalRegion).get sourceLocalIndex :=
        DoubleCutElimTrace.extendedLocalIndex_get sourceContext finalRegion
          sourceLocalIndex
      _ = copyTrace.finalWireMap elimTrace
          ((ConcreteElaboration.exactScopeWires input.val originalRegion).get
            targetIndex) :=
        localSourceIndex_get finalWellFormed boundaryNodup finalRegion
          originalRegion mappedRegion targetIndex
      _ = _ := congrArg (copyTrace.finalWireMap elimTrace)
        (DoubleCutElimTrace.extendedLocalIndex_get targetContext
          originalRegion targetIndex).symm
  have sourceExtendedIndexEq : sourceExtendedIndex =
      extended.sourceIndex targetExtendedIndex :=
    ConcreteElaboration.WireContext.lookup?_unique sourceExact.nodup
      (extended.sourceIndex_lookup targetExtendedIndex) corresponding
  change extended.targetEnvironment
      (ConcreteElaboration.extendedEnvironment sourceContext finalRegion
        sourceOuter sourceLocal) targetExtendedIndex = sourceLocal sourceLocalIndex
  unfold targetEnvironment
  simp only [Function.comp_apply]
  rw [← sourceExtendedIndexEq]
  exact DoubleCutElimTrace.extendedEnvironment_local sourceContext finalRegion
    sourceOuter sourceLocal sourceLocalIndex

/-- The complete valuation-selection contract used by regular local compiler
transport in either semantic direction. -/
theorem regularEnvironmentSelection
    {signature : List Nat}
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
    {copyTrace : InstantiationTrace comprehension attachments binders payload
      fuel (initialInstantiationState payload) result}
    {raw : ConcreteDiagram}
    {elimTrace : VacuousElimTrace (dropInstantiationAtomsRaw result)
      result.bubble raw}
    (finalWellFormed :
      (dropInstantiationAtomsRaw result).WellFormed signature)
    (boundaryNodup : comprehension.val.boundary.Nodup)
    (direction : ConcreteElaboration.SimulationDirection)
    (sourceContext : ConcreteElaboration.WireContext
      elimTrace.sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext input.val)
    (context : FinalContextWitness copyTrace elimTrace sourceContext
      targetContext)
    (finalRegion : Fin elimTrace.sourceDiagram.regionCount)
    (regular : copyTrace.FinalRegularPreimage elimTrace finalWellFormed
      finalRegion)
    (sourceExact : (sourceContext.extend finalRegion).Exact finalRegion)
    [Nonempty D] :
    let originalRegion := copyTrace.reverseRegionMap elimTrace finalWellFormed
      finalRegion
    let extended := context.extendRegular finalWellFormed boundaryNodup
      finalRegion regular
    ∀ (sourceOuter : Fin sourceContext.length → D)
      (targetOuter : Fin targetContext.length → D),
      context.indexRelation.EnvironmentsAgree sourceOuter targetOuter →
        match direction with
        | .forward => ∀ sourceLocal,
            ∃ targetLocal,
              extended.indexRelation.EnvironmentsAgree
                (ConcreteElaboration.extendedEnvironment sourceContext
                  finalRegion sourceOuter sourceLocal)
                (ConcreteElaboration.extendedEnvironment targetContext
                  originalRegion targetOuter targetLocal)
        | .backward => ∀ targetLocal,
            ∃ sourceLocal,
              extended.indexRelation.EnvironmentsAgree
                (ConcreteElaboration.extendedEnvironment sourceContext
                  finalRegion sourceOuter sourceLocal)
                (ConcreteElaboration.extendedEnvironment targetContext
                  originalRegion targetOuter targetLocal) := by
  dsimp only
  let originalRegion := copyTrace.reverseRegionMap elimTrace finalWellFormed
    finalRegion
  let mappedRegion := copyTrace.finalRegionMap_reverseRegionMap elimTrace
    finalWellFormed finalRegion regular
  let extended := context.extendRegular finalWellFormed boundaryNodup
    finalRegion regular
  intro sourceOuter targetOuter outerAgreement
  cases direction with
  | forward =>
      intro sourceLocal
      let sourceEnvironment := ConcreteElaboration.extendedEnvironment
        sourceContext finalRegion sourceOuter sourceLocal
      let targetEnvironment := extended.targetEnvironment sourceEnvironment
      let targetLocal := DoubleCutElimTrace.localEnvironmentPart targetContext
        originalRegion targetEnvironment
      refine ⟨targetLocal, ?_⟩
      have targetOuterValues : ∀ index,
          targetEnvironment
              (DoubleCutElimTrace.extendedOuterIndex targetContext
                originalRegion index) = targetOuter index := by
        intro index
        exact regularTargetEnvironment_outer finalWellFormed boundaryNodup
          sourceContext targetContext context finalRegion regular sourceExact
          sourceOuter targetOuter outerAgreement sourceLocal index
      have targetEnvironmentEq :=
        DoubleCutElimTrace.extendedEnvironment_of_parts targetContext
          originalRegion targetOuter targetEnvironment targetOuterValues
      rw [targetEnvironmentEq]
      exact extended.targetEnvironment_agrees sourceEnvironment
  | backward =>
      intro targetLocal
      let sourceLocal := sourceLocalEnvironment finalWellFormed boundaryNodup
        finalRegion originalRegion mappedRegion targetLocal
      let sourceEnvironment := ConcreteElaboration.extendedEnvironment
        sourceContext finalRegion sourceOuter sourceLocal
      let targetEnvironment := extended.targetEnvironment sourceEnvironment
      refine ⟨sourceLocal, ?_⟩
      have targetOuterValues : ∀ index,
          targetEnvironment
              (DoubleCutElimTrace.extendedOuterIndex targetContext
                originalRegion index) = targetOuter index := by
        intro index
        exact regularTargetEnvironment_outer finalWellFormed boundaryNodup
          sourceContext targetContext context finalRegion regular sourceExact
          sourceOuter targetOuter outerAgreement sourceLocal index
      have targetLocalValues :
          DoubleCutElimTrace.localEnvironmentPart targetContext originalRegion
              targetEnvironment = targetLocal := by
        funext index
        change targetEnvironment
            (DoubleCutElimTrace.extendedLocalIndex targetContext originalRegion
              index) = targetLocal index
        have localValue := regularTargetEnvironment_local finalWellFormed
          boundaryNodup sourceContext targetContext context finalRegion regular
          sourceExact sourceOuter sourceLocal index
        change targetEnvironment
            (DoubleCutElimTrace.extendedLocalIndex targetContext originalRegion
              index) =
          sourceLocal (localSourceIndex finalWellFormed boundaryNodup
            finalRegion originalRegion mappedRegion index) at localValue
        rw [localValue]
        exact sourceLocalEnvironment_image finalWellFormed boundaryNodup
          finalRegion originalRegion mappedRegion targetLocal index
      have targetEnvironmentEq :=
        DoubleCutElimTrace.extendedEnvironment_of_parts targetContext
          originalRegion targetOuter targetEnvironment targetOuterValues
      rw [targetLocalValues] at targetEnvironmentEq
      rw [targetEnvironmentEq]
      exact extended.targetEnvironment_agrees sourceEnvironment

end FinalContextWitness
end InstantiationTrace

end VisualProof.Rule
