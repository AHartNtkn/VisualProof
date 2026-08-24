import VisualProof.Rule.Completeness.Comprehension.Leaf.Complete
import VisualProof.Rule.Completeness.Comprehension.Structural.Blank
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
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
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
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
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
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
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

theorem filledValidityOfScope
    {boundary wires : List Sig}
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external wires)
    (before after : Region wires)
    (beforeCanonical : (context.fill before).Canonical)
    (beforeExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill before))
    (scope : ScopePreservation before after) :
    (context.fill after).Canonical ∧
      OpenDiagram.ExternalTwoEnded interface.boundaryWire
        (context.fill after) := by
  have afterCanonical : after.Canonical := scope.canonical
    (context.holeCanonical before beforeCanonical)
  have replacement := context.replaceCanonical before after beforeCanonical
    afterCanonical scope.incidenceNonempty
  let beforeEndpoint := interface.withBody (context.fill before)
    beforeCanonical beforeExternalTwoEnded
  exact ⟨replacement.1,
    beforeEndpoint.externalTwoEnded_of_nonempty_iff _ replacement.2⟩

theorem telescopeTrans
    {boundary wires : List Sig}
    {polarity : Polarity}
    {interface : OpenDiagram boundary}
    {context : DiagramContext interface.external wires}
    {first middle last : Region wires}
    {firstCanonical : (context.fill first).Canonical}
    {firstExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill first)}
    {middleCanonical : (context.fill middle).Canonical}
    {middleExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill middle)}
    {lastCanonical : (context.fill last).Canonical}
    {lastExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill last)}
    (head : Telescope polarity interface context first middle
      firstCanonical firstExternalTwoEnded middleCanonical
      middleExternalTwoEnded)
    (tail : Telescope polarity interface context middle last
      middleCanonical middleExternalTwoEnded lastCanonical
      lastExternalTwoEnded) :
    Telescope polarity interface context first last firstCanonical
      firstExternalTwoEnded lastCanonical lastExternalTwoEnded := by
  cases polarity with
  | positive => exact ⟨head.1, head.2.trans tail.2⟩
  | negative => exact ⟨head.1, tail.2.trans head.2⟩

theorem polaritySource_property
    (polarity : Polarity) (property : α → Prop) (before after : α)
    (beforeProperty : property before) (afterProperty : property after) :
    property (polaritySource polarity before after) := by
  cases polarity
  · exact beforeProperty
  · exact afterProperty

theorem telescopeIso
    {boundary wires : List Sig} {polarity : Polarity}
    {interface : OpenDiagram boundary}
    {context : DiagramContext interface.external wires}
    {before before' after after' : Region wires}
    {beforeCanonical : (context.fill before).Canonical}
    {beforeExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill before)}
    {beforeCanonical' : (context.fill before').Canonical}
    {beforeExternalTwoEnded' : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill before')}
    {afterCanonical : (context.fill after).Canonical}
    {afterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill after)}
    {afterCanonical' : (context.fill after').Canonical}
    {afterExternalTwoEnded' : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill after')}
    (beforeIso : RegionIso (WireEquiv.refl wires) before before')
    (afterIso : RegionIso (WireEquiv.refl wires) after after')
    (telescope : Telescope polarity interface context before after
      beforeCanonical beforeExternalTwoEnded afterCanonical
      afterExternalTwoEnded) :
    Telescope polarity interface context before' after'
      beforeCanonical' beforeExternalTwoEnded' afterCanonical'
      afterExternalTwoEnded' := by
  let beforeOpenIso := OpenDiagram.withBody_iso beforeCanonical
    beforeCanonical' beforeExternalTwoEnded beforeExternalTwoEnded'
    (DiagramContext.fillIso context beforeIso)
  let afterOpenIso := OpenDiagram.withBody_iso afterCanonical
    afterCanonical' afterExternalTwoEnded afterExternalTwoEnded'
    (DiagramContext.fillIso context afterIso)
  cases polarity with
  | positive =>
      exact ⟨telescope.1, EqualityNormalization.reflTransGen_iso
        beforeOpenIso telescope.2 afterOpenIso⟩
  | negative =>
      exact ⟨telescope.1, EqualityNormalization.reflTransGen_iso
        afterOpenIso telescope.2 beforeOpenIso⟩

theorem telescopeOfHosted
    {common outer hostLocals boundary : List Sig}
    {before after : Region common}
    (transformation : HostedStrict before after)
    (rename : WireRenaming common (outer ++ hostLocals))
    (hostItems : ItemSeq (outer ++ hostLocals))
    (polarity : Polarity)
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external outer)
    (beforeCanonical :
      (context.fill (Region.adjoinAt hostLocals hostItems
        (before.renameWires rename))).Canonical)
    (beforeExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire
      (context.fill (Region.adjoinAt hostLocals hostItems
        (before.renameWires rename))))
    (afterCanonical :
      (context.fill (Region.adjoinAt hostLocals hostItems
        (after.renameWires rename))).Canonical)
    (afterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire
      (context.fill (Region.adjoinAt hostLocals hostItems
        (after.renameWires rename))))
    (polarityEq : context.polarity = polarity) :
    Telescope polarity interface context
      (Region.adjoinAt hostLocals hostItems (before.renameWires rename))
      (Region.adjoinAt hostLocals hostItems (after.renameWires rename))
      beforeCanonical beforeExternalTwoEnded afterCanonical
      afterExternalTwoEnded := by
  let beforeHosted := Region.adjoinAt hostLocals hostItems
    (before.renameWires rename)
  let afterHosted := Region.adjoinAt hostLocals hostItems
    (after.renameWires rename)
  let occurrence := exactOccurrence interface context beforeHosted
    beforeCanonical beforeExternalTwoEnded
  have strict := transformation outer hostLocals rename hostItems occurrence
    afterCanonical afterExternalTwoEnded
  have equates := strict.toEquates
  cases polarity with
  | positive => exact ⟨polarityEq, equates.1⟩
  | negative => exact ⟨polarityEq, equates.2⟩

/-- Derive the exact support-completed material pattern selected by
comprehension evidence. The material syntax and its canonicality determine
the structural recursion; the caller contributes only the authoritative
instantiation evidence and the actual telescope request. -/
theorem supportPatternDerives
    {materialWires structuralOuter structuralBefore structuralAfter :
        List Sig}
    (material : Region materialWires)
    (materialCanonical : material.Canonical)
    {items : ItemSeq
      (structuralOuter ++
        (structuralBefore ++ .rel materialWires :: structuralAfter))}
    {result : Region
      (structuralOuter ++ (structuralBefore ++ structuralAfter))}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        (Erasure.Exposure.supportPattern material materialCanonical)
        (_root_.VisualProof.Rule.Comprehension.retain structuralOuter
          structuralBefore structuralAfter materialWires)
        (_root_.VisualProof.Rule.Comprehension.selected structuralOuter
          structuralBefore structuralAfter materialWires)
        items result)
    (request : Telescope.Request
      (Region.adjoinAt (structuralBefore ++ structuralAfter) .nil result)
      (.mk (structuralBefore ++ .rel materialWires :: structuralAfter)
        items)) :
    request.Result := by
  let DerivesMaterial : {materialWires : List Sig} →
      Region materialWires → Prop := fun {materialWires} material =>
    ∀ (materialCanonical : material.Canonical)
      {structuralOuter structuralBefore structuralAfter : List Sig}
      {items : ItemSeq
        (structuralOuter ++
          (structuralBefore ++ .rel materialWires :: structuralAfter))}
      {result : Region
        (structuralOuter ++ (structuralBefore ++ structuralAfter))}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          (Erasure.Exposure.supportPattern material materialCanonical)
          (_root_.VisualProof.Rule.Comprehension.retain structuralOuter
            structuralBefore structuralAfter materialWires)
          (_root_.VisualProof.Rule.Comprehension.selected structuralOuter
            structuralBefore structuralAfter materialWires)
          items result)
      (request : Telescope.Request
        (Region.adjoinAt (structuralBefore ++ structuralAfter) .nil result)
        (.mk (structuralBefore ++ .rel materialWires :: structuralAfter)
          items)),
      request.Result
  refine (Region.rec
    (motive_1 := fun _ region => DerivesMaterial region)
    (motive_2 := fun wires item =>
      wires = [] → DerivesMaterial (Region.singleton item))
    (motive_3 := fun wires materialItems =>
      wires = [] → DerivesMaterial (Region.ofItems materialItems))
    ?_ ?_ ?_ ?_ ?_ ?_ material) materialCanonical evidence request
  · intro outer locals materialItems materialItemsIH materialCanonical
      structuralOuter structuralBefore structuralAfter items result evidence
      structuralRequest
    cases outer with
    | nil =>
        cases locals with
        | nil =>
            have materialEq : Region.ofItems materialItems =
                Region.mk [] materialItems := by
              simp only [Region.ofItems]
              congr 1
              let appendNil : WireRenaming [] ([] ++ []) :=
                ⟨fun wire => wire.appendLeft []⟩
              change materialItems.renameWires appendNil = materialItems
              have renameEq : appendNil = WireRenaming.id := by
                apply WireRenaming.ext
                intro signature wire
                cases wire
              rw [renameEq]
              exact ItemSeq.renameWires_id materialItems
            have materialItemsCanonical :
                (Region.ofItems materialItems).Canonical := by
              rw [materialEq]
              exact materialCanonical
            have patternEq :
                Erasure.Exposure.supportPattern
                    (Region.mk [] materialItems) materialCanonical =
                  Erasure.Exposure.supportPattern
                    (Region.ofItems materialItems)
                    materialItemsCanonical := by
              apply EqualityNormalization.OpenDiagram.eq_of_data
              · rfl
              · rfl
              · change (HEq
                  (Erasure.Exposure.supportBody
                    (Region.mk [] materialItems))
                  (Erasure.Exposure.supportBody
                    (Region.ofItems materialItems)))
                have sourceBodyEq :
                    Erasure.Exposure.supportBody
                        (Region.mk [] materialItems) =
                      Region.mk [] materialItems :=
                  EqualityNormalization.supportBody_eq_of_supportPins_nil
                    (Region.mk [] materialItems) rfl
                have targetBodyEq :
                    Erasure.Exposure.supportBody
                        (Region.ofItems materialItems) =
                      Region.ofItems materialItems :=
                  EqualityNormalization.supportBody_eq_of_supportPins_nil
                    (Region.ofItems materialItems) rfl
                have bodyEq := sourceBodyEq.trans
                  (materialEq.symm.trans targetBodyEq.symm)
                exact heq_of_eq bodyEq
            rw [patternEq] at evidence
            exact materialItemsIH rfl materialItemsCanonical evidence
              structuralRequest
        | cons firstLocal locals => sorry
    | cons wire wires => sorry
  · intro wires arguments head ports wiresEq
    subst wires
    sorry
  · intro wires signature arity ports wiresEq
    subst wires
    sorry
  · intro wires body bodyIH wiresEq
    subst wires
    sorry
  · intro wires wiresEq
    subst wires
    intro materialCanonical structuralOuter structuralBefore structuralAfter
      items result evidence structuralRequest
    have patternEq :
        Erasure.Exposure.supportPattern (Region.ofItems ItemSeq.nil)
            materialCanonical = Structural.Blank.blankPattern := by
      apply EqualityNormalization.OpenDiagram.eq_of_data <;> rfl
    rw [patternEq] at evidence
    exact Structural.Blank.itemsEnds evidence structuralRequest
  · intro wires materialHead materialTail materialHeadIH materialTailIH wiresEq
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
