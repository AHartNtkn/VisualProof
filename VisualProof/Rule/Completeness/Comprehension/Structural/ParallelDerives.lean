import VisualProof.Rule.Completeness.Comprehension.Structural.Support
import VisualProof.Rule.Completeness.Comprehension.Structural.Parallel

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

namespace Structural

mutual
  theorem parallelRegionSites_nonempty
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result)
      (data : Content.Parallel.operation arguments |>.Data frame) :
      Nonempty (RegionSites (Content.Parallel.operation arguments) data
        evidence) := by
    cases evidence with
    | mk childEvidence =>
        obtain ⟨childSites⟩ := parallelItemsSites_nonempty childEvidence
          ((Content.Parallel.operation arguments).appendData frame data _)
        exact ⟨.mk childSites⟩
  termination_by sizeOf source

  theorem parallelItemsSites_nonempty
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {source : ItemSeq sourceWires} {result : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result)
      (data : Content.Parallel.operation arguments |>.Data frame) :
      Nonempty (ItemsSites (Content.Parallel.operation arguments) data
        evidence) := by
    cases evidence with
    | nil => exact ⟨.nil _⟩
    | cons itemEvidence tailEvidence =>
        obtain ⟨itemSites⟩ := parallelItemSites_nonempty itemEvidence data
        obtain ⟨tailSites⟩ := parallelItemsSites_nonempty tailEvidence data
        exact ⟨.cons itemSites tailSites⟩
  termination_by sizeOf source

  theorem parallelItemSites_nonempty
      {arguments common sourceWires targetWires : List Sig}
      {pattern : OpenDiagram arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {source : Item sourceWires} {result : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result)
      (data : Content.Parallel.operation arguments |>.Data frame) :
      Nonempty (ItemSites (Content.Parallel.operation arguments) data
        evidence) := by
    cases evidence with
    | atom head ports => exact ⟨.atom (pattern := pattern) head ports⟩
    | selectedAtom application =>
        exact ⟨.selectedAtom (pattern := pattern) application PUnit.unit⟩
    | identity signature arity ports =>
        exact ⟨.identity (pattern := pattern) signature arity ports⟩
    | cut childEvidence =>
        obtain ⟨childSites⟩ := parallelRegionSites_nonempty childEvidence data
        exact ⟨.cut childSites⟩
  termination_by sizeOf source
end

/-- A nonempty item sequence is derivable by recursively deriving its head
and tail and joining their support binders with ParallelShape. -/
theorem supportParallelDerives
    {wires : List Sig} (materialHead : Item wires)
    (materialTail : ItemSeq wires)
    (materialHeadIH : wires = [] →
      SupportDerives (Region.singleton materialHead))
    (materialTailIH : wires = [] →
      SupportDerives (Region.ofItems materialTail))
    (wiresEq : wires = []) :
    SupportDerives (Region.ofItems (.cons materialHead materialTail)) := by
subst wires
intro materialCanonical structuralOuter structuralBefore structuralAfter
  items result evidence structuralRequest
let headMaterial := Region.singleton materialHead
let tailMaterial := Region.ofItems materialTail
have materialPresentation : headMaterial.conjoin tailMaterial =
    Region.ofItems (.cons materialHead materialTail) := by
  exact Region.singleton_conjoin_ofItems materialHead materialTail
have combinedCanonical : (headMaterial.conjoin tailMaterial).Canonical := by
  rw [materialPresentation]
  exact materialCanonical
have childCanonical :=
  (Region.Canonical.conjoin_iff headMaterial tailMaterial).mp
    combinedCanonical
have headCanonical : headMaterial.Canonical := childCanonical.1
have tailCanonical : tailMaterial.Canonical := childCanonical.2
let parallelData :=
  (Content.Parallel.firstHead structuralOuter structuralBefore
      structuralAfter [],
    Content.Parallel.secondHead structuralOuter structuralBefore
      structuralAfter [])
obtain ⟨parallelSites⟩ := parallelItemsSites_nonempty
  (frame := Content.Parallel.rootFrame structuralOuter structuralBefore
    structuralAfter []) evidence parallelData
let headPattern := Erasure.Exposure.supportPattern headMaterial
  headCanonical
let tailPattern := Erasure.Exposure.supportPattern tailMaterial
  tailCanonical
let fullPattern := Erasure.Exposure.supportPattern
  (Region.ofItems (.cons materialHead materialTail)) materialCanonical
have selectedCase : SupportParallelSelectedCase headPattern tailPattern
    fullPattern := by
  refine fun {common sourceWires splitWires} {parallel} {heads}
    {sitePattern} frames application siteData => ?_
  exact supportParallelSelectedFactors_nonempty frames materialHead
    materialTail headCanonical tailCanonical materialCanonical application
    siteData
obtain ⟨factors⟩ := supportParallelItemsFactors_nonempty headPattern
  tailPattern fullPattern selectedCase
  (supportParallelFramesRoot structuralOuter structuralBefore
    structuralAfter) evidence parallelSites
obtain ⟨splitIso⟩ := factors.splitIso
let fullInstantiated := Region.adjoinAt
  (structuralBefore ++ structuralAfter) .nil result
let tailInstantiated := Region.adjoinAt
  (structuralBefore ++ structuralAfter) .nil factors.tailResult
let tailPending : Region structuralOuter :=
  .mk (structuralBefore ++ .rel [] :: structuralAfter)
    factors.tailSource
let headInstantiated := Region.adjoinAt
  (structuralBefore ++ .rel [] :: structuralAfter) .nil
    factors.headResult
let splitPending : Region structuralOuter :=
  .mk (structuralBefore ++ .rel [] :: .rel [] :: structuralAfter)
    factors.splitSource
have tailPendingScope : ScopePreservation
    (.mk (structuralBefore ++ .rel [] :: structuralAfter) items)
    tailPending := by
  exact supportParallelRootTailScope structuralOuter structuralBefore
    structuralAfter factors
have splitPendingScope : ScopePreservation
    (.mk (structuralBefore ++ .rel [] :: structuralAfter) items)
    splitPending := by
  exact supportParallelRootSplitScope structuralOuter structuralBefore
    structuralAfter factors
have resultHostedScope : ScopePreservation fullInstantiated
    tailInstantiated := by
  exact adjoinAt_preserves_scope
    (structuralBefore ++ structuralAfter) .nil result factors.tailResult
    factors.resultScope
have tailInstantiatedValidity := filledValidityOfScope
  structuralRequest.occurrence.interface
  structuralRequest.occurrence.context fullInstantiated tailInstantiated
  structuralRequest.instantiatedCanonical
  structuralRequest.instantiatedExternalTwoEnded resultHostedScope
have tailPendingValidity := filledValidityOfScope
  structuralRequest.occurrence.interface
  structuralRequest.occurrence.context
  (.mk (structuralBefore ++ .rel [] :: structuralAfter) items)
  tailPending structuralRequest.pendingCanonical
  structuralRequest.pendingExternalTwoEnded tailPendingScope
let tailPresentation := RegionIso.adjoinAtOfItems
  (structuralBefore ++ .rel [] :: structuralAfter) factors.tailSource
let adjoinedTail := Region.adjoinAt
  (structuralBefore ++ .rel [] :: structuralAfter) .nil
  (Region.ofItems factors.tailSource)
have adjoinedTailValidity := filledValidityOfScope
  structuralRequest.occurrence.interface
  structuralRequest.occurrence.context tailPending adjoinedTail
  tailPendingValidity.1 tailPendingValidity.2
  (ScopePreservation.ofIso tailPresentation.symm)
have headHostedScope : ScopePreservation tailPending
    headInstantiated :=
  (ScopePreservation.ofIso tailPresentation.symm).trans
    (adjoinAt_preserves_scope
      (structuralBefore ++ .rel [] :: structuralAfter) .nil
      (Region.ofItems factors.tailSource) factors.headResult
      factors.headReverseScope)
have headInstantiatedValidity := filledValidityOfScope
  structuralRequest.occurrence.interface
  structuralRequest.occurrence.context tailPending headInstantiated
  tailPendingValidity.1 tailPendingValidity.2 headHostedScope
have splitPendingValidity := filledValidityOfScope
  structuralRequest.occurrence.interface
  structuralRequest.occurrence.context
  (.mk (structuralBefore ++ .rel [] :: structuralAfter) items)
  splitPending structuralRequest.pendingCanonical
  structuralRequest.pendingExternalTwoEnded splitPendingScope
have polarityEq : structuralRequest.occurrence.context.polarity =
    structuralRequest.polarity := structuralRequest.continuation.1
have headSourceCanonical :
    (structuralRequest.occurrence.context.fill
      (polaritySource structuralRequest.polarity headInstantiated
        splitPending)).Canonical :=
  polaritySource_property structuralRequest.polarity
    (fun region =>
      (structuralRequest.occurrence.context.fill region).Canonical)
    headInstantiated splitPending headInstantiatedValidity.1
    splitPendingValidity.1
have headSourceExternal : OpenDiagram.ExternalTwoEnded
    structuralRequest.occurrence.interface.boundaryWire
    (structuralRequest.occurrence.context.fill
      (polaritySource structuralRequest.polarity headInstantiated
        splitPending)) :=
  polaritySource_property structuralRequest.polarity
    (fun region => OpenDiagram.ExternalTwoEnded
      structuralRequest.occurrence.interface.boundaryWire
      (structuralRequest.occurrence.context.fill region))
    headInstantiated splitPending headInstantiatedValidity.2
    splitPendingValidity.2
let headRequest : Telescope.Request headInstantiated splitPending := {
  boundary := structuralRequest.boundary
  source := structuralRequest.occurrence.interface.withBody
    (structuralRequest.occurrence.context.fill
      (polaritySource structuralRequest.polarity headInstantiated
        splitPending)) headSourceCanonical headSourceExternal
  endpoint := splitPending
  polarity := structuralRequest.polarity
  occurrence := exactOccurrence structuralRequest.occurrence.interface
    structuralRequest.occurrence.context
    (polaritySource structuralRequest.polarity headInstantiated
      splitPending) headSourceCanonical headSourceExternal
  instantiatedCanonical := headInstantiatedValidity.1
  instantiatedExternalTwoEnded := headInstantiatedValidity.2
  pendingCanonical := splitPendingValidity.1
  pendingExternalTwoEnded := splitPendingValidity.2
  endpointCanonical := splitPendingValidity.1
  endpointExternalTwoEnded := splitPendingValidity.2
  continuation := Telescope.refl structuralRequest.polarity
    structuralRequest.occurrence.interface
    structuralRequest.occurrence.context splitPendingValidity.1
    splitPendingValidity.2 polarityEq
}
have headCompiled := materialHeadIH rfl headCanonical
  factors.headEvidence headRequest
have headTelescope : Telescope structuralRequest.polarity
    structuralRequest.occurrence.interface
    structuralRequest.occurrence.context headInstantiated splitPending
    headInstantiatedValidity.1 headInstantiatedValidity.2
    splitPendingValidity.1 splitPendingValidity.2 := by
  exact Telescope.StrictDerives.toTelescope structuralRequest.polarity
    structuralRequest.occurrence.interface
    structuralRequest.occurrence.context headInstantiatedValidity.1
    headInstantiatedValidity.2 splitPendingValidity.1
    splitPendingValidity.2 polarityEq
    (by simpa only [headRequest, Telescope.Request.Result] using
      headCompiled)
have headBridgeTelescope : Telescope structuralRequest.polarity
    structuralRequest.occurrence.interface
    structuralRequest.occurrence.context tailPending headInstantiated
    tailPendingValidity.1 tailPendingValidity.2
    headInstantiatedValidity.1 headInstantiatedValidity.2 := by
  have renamedHeadCanonical :
      (structuralRequest.occurrence.context.fill
        (Region.adjoinAt
          (structuralBefore ++ .rel [] :: structuralAfter) .nil
          (factors.headResult.renameWires WireRenaming.id))).Canonical := by
    simpa only [Region.renameWires_id] using headInstantiatedValidity.1
  have renamedHeadExternal : OpenDiagram.ExternalTwoEnded
      structuralRequest.occurrence.interface.boundaryWire
      (structuralRequest.occurrence.context.fill
        (Region.adjoinAt
          (structuralBefore ++ .rel [] :: structuralAfter) .nil
          (factors.headResult.renameWires WireRenaming.id))) := by
    intro signature wire
    simpa only [Region.renameWires_id] using
      headInstantiatedValidity.2 wire
  have renamedAdjoinedTailCanonical :
      (structuralRequest.occurrence.context.fill
        (Region.adjoinAt
          (structuralBefore ++ .rel [] :: structuralAfter) .nil
          ((Region.ofItems factors.tailSource).renameWires
            WireRenaming.id))).Canonical := by
    simpa only [Region.renameWires_id] using adjoinedTailValidity.1
  have renamedAdjoinedTailExternal : OpenDiagram.ExternalTwoEnded
      structuralRequest.occurrence.interface.boundaryWire
      (structuralRequest.occurrence.context.fill
        (Region.adjoinAt
          (structuralBefore ++ .rel [] :: structuralAfter) .nil
          ((Region.ofItems factors.tailSource).renameWires
            WireRenaming.id))) := by
    intro signature wire
    simpa only [Region.renameWires_id] using adjoinedTailValidity.2 wire
  have rawTelescope : Telescope structuralRequest.polarity
      structuralRequest.occurrence.interface
      structuralRequest.occurrence.context adjoinedTail headInstantiated
      adjoinedTailValidity.1 adjoinedTailValidity.2
      headInstantiatedValidity.1 headInstantiatedValidity.2 := by
    simpa only [Region.renameWires_id] using
      telescopeOfHosted factors.headBridge.symm WireRenaming.id .nil
        structuralRequest.polarity
        structuralRequest.occurrence.interface
        structuralRequest.occurrence.context
        renamedAdjoinedTailCanonical renamedAdjoinedTailExternal
        renamedHeadCanonical renamedHeadExternal polarityEq
  exact telescopeIso tailPresentation
    (RegionIso.refl headInstantiated) rawTelescope
have tailContinuation : Telescope structuralRequest.polarity
    structuralRequest.occurrence.interface
    structuralRequest.occurrence.context tailPending splitPending
    tailPendingValidity.1 tailPendingValidity.2
    splitPendingValidity.1 splitPendingValidity.2 :=
  telescopeTrans headBridgeTelescope headTelescope
have tailSourceCanonical :
    (structuralRequest.occurrence.context.fill
      (polaritySource structuralRequest.polarity tailInstantiated
        splitPending)).Canonical :=
  polaritySource_property structuralRequest.polarity
    (fun region =>
      (structuralRequest.occurrence.context.fill region).Canonical)
    tailInstantiated splitPending tailInstantiatedValidity.1
    splitPendingValidity.1
have tailSourceExternal : OpenDiagram.ExternalTwoEnded
    structuralRequest.occurrence.interface.boundaryWire
    (structuralRequest.occurrence.context.fill
      (polaritySource structuralRequest.polarity tailInstantiated
        splitPending)) :=
  polaritySource_property structuralRequest.polarity
    (fun region => OpenDiagram.ExternalTwoEnded
      structuralRequest.occurrence.interface.boundaryWire
      (structuralRequest.occurrence.context.fill region))
    tailInstantiated splitPending tailInstantiatedValidity.2
    splitPendingValidity.2
let tailRequest : Telescope.Request tailInstantiated tailPending := {
  boundary := structuralRequest.boundary
  source := structuralRequest.occurrence.interface.withBody
    (structuralRequest.occurrence.context.fill
      (polaritySource structuralRequest.polarity tailInstantiated
        splitPending)) tailSourceCanonical tailSourceExternal
  endpoint := splitPending
  polarity := structuralRequest.polarity
  occurrence := exactOccurrence structuralRequest.occurrence.interface
    structuralRequest.occurrence.context
    (polaritySource structuralRequest.polarity tailInstantiated
      splitPending) tailSourceCanonical tailSourceExternal
  instantiatedCanonical := tailInstantiatedValidity.1
  instantiatedExternalTwoEnded := tailInstantiatedValidity.2
  pendingCanonical := tailPendingValidity.1
  pendingExternalTwoEnded := tailPendingValidity.2
  endpointCanonical := splitPendingValidity.1
  endpointExternalTwoEnded := splitPendingValidity.2
  continuation := tailContinuation
}
have tailCompiled := materialTailIH rfl tailCanonical
  factors.tailEvidence tailRequest
have tailTelescope : Telescope structuralRequest.polarity
    structuralRequest.occurrence.interface
    structuralRequest.occurrence.context tailInstantiated splitPending
    tailInstantiatedValidity.1 tailInstantiatedValidity.2
    splitPendingValidity.1 splitPendingValidity.2 := by
  exact Telescope.StrictDerives.toTelescope structuralRequest.polarity
    structuralRequest.occurrence.interface
    structuralRequest.occurrence.context tailInstantiatedValidity.1
    tailInstantiatedValidity.2 splitPendingValidity.1
    splitPendingValidity.2 polarityEq
    (by simpa only [tailRequest, Telescope.Request.Result] using
      tailCompiled)
have resultBridgeTelescope : Telescope structuralRequest.polarity
    structuralRequest.occurrence.interface
    structuralRequest.occurrence.context fullInstantiated
    tailInstantiated structuralRequest.instantiatedCanonical
    structuralRequest.instantiatedExternalTwoEnded
    tailInstantiatedValidity.1 tailInstantiatedValidity.2 := by
  have renamedResultCanonical :
      (structuralRequest.occurrence.context.fill
        (Region.adjoinAt (structuralBefore ++ structuralAfter) .nil
          (result.renameWires WireRenaming.id))).Canonical := by
    simpa only [Region.renameWires_id] using
      structuralRequest.instantiatedCanonical
  have renamedResultExternal : OpenDiagram.ExternalTwoEnded
      structuralRequest.occurrence.interface.boundaryWire
      (structuralRequest.occurrence.context.fill
        (Region.adjoinAt (structuralBefore ++ structuralAfter) .nil
          (result.renameWires WireRenaming.id))) := by
    intro signature wire
    simpa only [Region.renameWires_id] using
      structuralRequest.instantiatedExternalTwoEnded wire
  have renamedTailResultCanonical :
      (structuralRequest.occurrence.context.fill
        (Region.adjoinAt (structuralBefore ++ structuralAfter) .nil
          (factors.tailResult.renameWires WireRenaming.id))).Canonical := by
    simpa only [Region.renameWires_id] using tailInstantiatedValidity.1
  have renamedTailResultExternal : OpenDiagram.ExternalTwoEnded
      structuralRequest.occurrence.interface.boundaryWire
      (structuralRequest.occurrence.context.fill
        (Region.adjoinAt (structuralBefore ++ structuralAfter) .nil
          (factors.tailResult.renameWires WireRenaming.id))) := by
    intro signature wire
    simpa only [Region.renameWires_id] using
      tailInstantiatedValidity.2 wire
  simpa only [Region.renameWires_id] using
    telescopeOfHosted factors.resultBridge WireRenaming.id .nil
      structuralRequest.polarity structuralRequest.occurrence.interface
      structuralRequest.occurrence.context renamedResultCanonical
      renamedResultExternal renamedTailResultCanonical
      renamedTailResultExternal polarityEq
have preparationTelescope : Telescope structuralRequest.polarity
    structuralRequest.occurrence.interface
    structuralRequest.occurrence.context fullInstantiated splitPending
    structuralRequest.instantiatedCanonical
    structuralRequest.instantiatedExternalTwoEnded
    splitPendingValidity.1 splitPendingValidity.2 :=
  telescopeTrans resultBridgeTelescope tailTelescope
let basePreparation : structuralRequest.Preparation splitPending := {
  prepared := splitPending
  preparedCanonical := splitPendingValidity.1
  preparedExternalTwoEnded := splitPendingValidity.2
  rawPreparedCanonical := splitPendingValidity.1
  rawPreparedExternalTwoEnded := splitPendingValidity.2
  preparedIso := RegionIso.refl splitPending
  telescope := by
    simpa only [fullInstantiated] using preparationTelescope
}
let rawToSplit := (RegionIso.adjoinAt
  (structuralBefore ++ .rel [] :: .rel [] :: structuralAfter) .nil
  splitIso).trans (RegionIso.adjoinAtOfItems
    (structuralBefore ++ .rel [] :: .rel [] :: structuralAfter)
    factors.splitSource)
exact itemsParallel evidence parallelSites structuralRequest
  (basePreparation.rawIso rawToSplit.symm)

end Structural

end VisualProof.Rule.Completeness.Comprehension
