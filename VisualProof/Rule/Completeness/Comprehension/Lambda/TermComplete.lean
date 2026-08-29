import VisualProof.Rule.Completeness.Comprehension.Lambda.TermEndpoint
import VisualProof.Rule.Completeness.Comprehension.Lambda.TermItems
import VisualProof.Rule.Completeness.Comprehension.Leaf.Accumulator
import VisualProof.Rule.Completeness.Comprehension.Normalization.ArgumentsAt
import VisualProof.Rule.Completeness.Comprehension.Normalization.Sites

namespace VisualProof.Rule.Completeness.Comprehension.LambdaTerm

open Diagram
open Theory
open WirePrimitive

theorem supportTermFormalAt
    {wires structuralOuter structuralBefore structuralAfter :
      List Sig}
    (freeArity : Nat) (term : VisualProof.Lambda.Term 0 (Fin freeArity))
    (output : Var wires .iota)
    (ports : Fin freeArity → Var wires .iota)
    {items : ItemSeq
      (structuralOuter ++
        (structuralBefore ++ .rel wires :: structuralAfter))}
    {result : Region
      (structuralOuter ++ (structuralBefore ++ structuralAfter))}
    (evidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        (Erasure.Exposure.supportPattern
          (supportTermMaterial freeArity term output ports)
          (supportTermMaterial_canonical freeArity term output ports))
        (VisualProof.Rule.Comprehension.retain structuralOuter
          structuralBefore structuralAfter wires)
        (VisualProof.Rule.Comprehension.selected structuralOuter
          structuralBefore structuralAfter wires)
        items result)
    (sites : ItemsSites (operation := normalizationOperation wires)
      (frame := normalizationFrame structuralOuter structuralBefore
        structuralAfter wires) PUnit.unit evidence)
    (request : Telescope.Request
      (Region.adjoinAt (structuralBefore ++ structuralAfter) .nil result)
      (.mk (structuralBefore ++ .rel wires :: structuralAfter) items)) :
    request.Result := by
  let targetFrame := Lambda.TermLeaf.rootFrame structuralOuter structuralBefore
    structuralAfter freeArity
  obtain ⟨retained, formalSource, formalResult, formalEvidence, formalSites,
      formalCoherence, staged, hosted, stagedScope, ⟨stagedPresentation⟩,
      _endpointPresentation, sourceCleanup, retainedEq⟩ :=
    accumulateHostedTargetWith
      (outer := structuralOuter) (before := structuralBefore)
      (after := structuralAfter) (targetInserted := []) evidence sites
      (Lambda.TermLeaf.Vars.fromTerm output ports) PUnit.unit
      (EqualityNormalization.formalPorts wires)
      ScopePreservation ScopePreservation.refl
      (fun locals before after scope =>
        adjoinAt_preserves_scope locals .nil before after scope)
      ScopePreservation.conjoin ScopePreservation.cut
      (fun before after => HostedStrict before after ∧
        HostedScope before after)
      (fun region => ⟨HostedStrict.refl region,
        fun rename => ScopePreservation.refl _⟩)
      (fun locals before after transformation =>
        ⟨HostedStrict.adjoinAt locals before after transformation.1,
          HostedScope.adjoinAt locals before after transformation.2⟩)
      (fun first second =>
        ⟨HostedStrict.conjoin _ _ _ _ first.1 second.1, by
          intro target rename
          simpa only [Region.renameWires_conjoin] using
            ScopePreservation.conjoin (first.2 rename) (second.2 rename)⟩)
      (fun transformation =>
        ⟨HostedStrict.cut _ _ transformation.1, by
          intro target rename
          simpa only [Region.singleton_renameWires, Item.renameWires] using
            ScopePreservation.cut (transformation.2 rename)⟩)
      (fun sourceIso targetIso transformation =>
        ⟨HostedStrict.iso sourceIso targetIso transformation.1, by
          intro target rename
          exact ((HostedScope.ofIso sourceIso) rename).trans
            ((transformation.2 rename).trans
              ((HostedScope.ofIso targetIso) rename))⟩)
      (fun _ _ => False)
      (fun _ _ impossible _ => False.elim impossible)
      (fun _ _ _ => True)
      (fun _ _ _ _ _ => True.intro)
      (termDataNaturality freeArity term)
      (fun retained => retained = []) rfl
      (fun first second firstEq secondEq => by
        simp only [firstEq, secondEq, List.nil_append])
      (fun {itemCommon itemSourceWires itemTargetWires} {itemFrame}
          {itemData} application siteData
          {selectedTargetSourceWires selectedTargetWires} selectedFrame _ => by
        obtain ⟨selectedRetained, selectedSource, selectedResult,
            selectedEvidence, selectedSites, selectedCoherence, selectedStaged,
            selectedHosted, selectedScope, selectedPresentation,
            selectedRetainedEq, selectedCleanup⟩ :=
          supportTermSelectedTargetItem freeArity term output ports application
            siteData selectedFrame
        exact ⟨selectedRetained, selectedSource, selectedResult,
          selectedEvidence, selectedSites, selectedCoherence, selectedStaged,
          selectedHosted, selectedScope, selectedPresentation, by
            intro bridge _alignment
            exact False.elim bridge.data_selects,
          selectedCleanup, selectedRetainedEq⟩)
  subst retained
  let common := structuralOuter ++ (structuralBefore ++ structuralAfter)
  let positionalSourceWires := structuralOuter ++
    (structuralBefore ++ .rel (Lambda.TermLeaf.arguments freeArity) ::
      structuralAfter)
  let authoritativeSourceWires := structuralOuter ++
    (structuralBefore ++ .rel wires :: structuralAfter)
  let commonRename : WireRenaming (common ++ []) common :=
    (WireEquiv.appendNil common).toRenaming
  let positionalSourceRename : WireRenaming
      (positionalSourceWires ++ []) positionalSourceWires :=
    (WireEquiv.appendNil positionalSourceWires).toRenaming
  let authoritativeSourceRename : WireRenaming
      (authoritativeSourceWires ++ []) authoritativeSourceWires :=
    (WireEquiv.appendNil authoritativeSourceWires).toRenaming
  let authoritativeFrame : Transform.Frame wires common
      authoritativeSourceWires authoritativeSourceWires :=
    Transform.Frame.replace structuralOuter structuralBefore structuralAfter
      [.rel wires] wires
  have sourceKeepCommutes : ∀ {signature} (wire : Var (common ++ []) signature),
      positionalSourceRename ((targetFrame.append []).sourceKeep wire) =
        targetFrame.sourceKeep (commonRename wire) := by
    intro signature wire
    let baseWire := commonRename wire
    have liftEq : baseWire.appendLeft [] = wire := by
      calc
        baseWire.appendLeft [] =
            (WireEquiv.appendNil common).symm baseWire :=
          (WireEquiv.appendNil_symm_apply common baseWire).symm
        _ = wire := (WireEquiv.appendNil common).left_inv wire
    calc
      positionalSourceRename ((targetFrame.append []).sourceKeep wire) =
          positionalSourceRename
            ((targetFrame.append []).sourceKeep
              (baseWire.appendLeft [])) :=
        congrArg (fun value => positionalSourceRename
          ((targetFrame.append []).sourceKeep value)) liftEq.symm
      _ = positionalSourceRename
          ((targetFrame.sourceKeep baseWire).appendLeft []) := by
        simp only [Transform.Frame.append, WireRenaming.appendRight,
          Var.appendMap_left]
      _ = targetFrame.sourceKeep baseWire := by
        simpa only [positionalSourceRename] using
          WireEquiv.appendNil_apply positionalSourceWires
            (targetFrame.sourceKeep baseWire)
      _ = targetFrame.sourceKeep (commonRename wire) := rfl
  have targetKeepCommutes : ∀ {signature} (wire : Var (common ++ []) signature),
      commonRename ((targetFrame.append []).targetKeep wire) =
        targetFrame.targetKeep (commonRename wire) := by
    intro signature wire
    let baseWire := commonRename wire
    have liftEq : baseWire.appendLeft [] = wire := by
      calc
        baseWire.appendLeft [] =
            (WireEquiv.appendNil common).symm baseWire :=
          (WireEquiv.appendNil_symm_apply common baseWire).symm
        _ = wire := (WireEquiv.appendNil common).left_inv wire
    calc
      commonRename ((targetFrame.append []).targetKeep wire) =
          commonRename ((targetFrame.append []).targetKeep
            (baseWire.appendLeft [])) :=
        congrArg (fun value => commonRename
          ((targetFrame.append []).targetKeep value)) liftEq.symm
      _ = commonRename ((targetFrame.targetKeep baseWire).appendLeft []) := by
        simp only [Transform.Frame.append, WireRenaming.appendRight,
          Var.appendMap_left]
      _ = targetFrame.targetKeep baseWire := by
        simpa only [commonRename] using WireEquiv.appendNil_apply common
          (targetFrame.targetKeep baseWire)
      _ = targetFrame.targetKeep (commonRename wire) := rfl
  have selectedCommutes :
      positionalSourceRename (targetFrame.append []).selected =
        targetFrame.selected := by
    simpa only [positionalSourceRename, Transform.Frame.append]
      using WireEquiv.appendNil_apply positionalSourceWires
        targetFrame.selected
  have argumentKeepCommutes : ∀ {signature}
      (wire : Var (common ++ []) signature),
      authoritativeSourceRename
          ((authoritativeFrame.append []).sourceKeep wire) =
        authoritativeFrame.sourceKeep (commonRename wire) := by
    intro signature wire
    let baseWire := commonRename wire
    have liftEq : baseWire.appendLeft [] = wire := by
      calc
        baseWire.appendLeft [] =
            (WireEquiv.appendNil common).symm baseWire :=
          (WireEquiv.appendNil_symm_apply common baseWire).symm
        _ = wire := (WireEquiv.appendNil common).left_inv wire
    calc
      authoritativeSourceRename
          ((authoritativeFrame.append []).sourceKeep wire) =
          authoritativeSourceRename
            ((authoritativeFrame.append []).sourceKeep
              (baseWire.appendLeft [])) :=
        congrArg (fun value => authoritativeSourceRename
          ((authoritativeFrame.append []).sourceKeep value)) liftEq.symm
      _ = authoritativeSourceRename
          ((authoritativeFrame.sourceKeep baseWire).appendLeft []) := by
        simp only [Transform.Frame.append, WireRenaming.appendRight,
          Var.appendMap_left]
      _ = authoritativeFrame.sourceKeep baseWire := by
        simpa only [authoritativeSourceRename] using
          WireEquiv.appendNil_apply authoritativeSourceWires
            (authoritativeFrame.sourceKeep baseWire)
      _ = authoritativeFrame.sourceKeep (commonRename wire) := rfl
  have argumentSelectedCommutes :
      authoritativeSourceRename (authoritativeFrame.append []).selected =
        authoritativeFrame.selected := by
    simpa only [authoritativeSourceRename, Transform.Frame.append]
      using WireEquiv.appendNil_apply authoritativeSourceWires
        authoritativeFrame.selected
  obtain ⟨flatFormalSource, flatFormalResult, flatFormalEvidence,
      flatFormalSites, flatSourceEq, flatPositionalEq, flatAuthoritativeEq,
      ⟨flatResultIso⟩, ⟨flatEndpointIso⟩⟩ :=
    targetItemsReindex
      (baseOperation := Lambda.TermLeaf.operation freeArity term)
      (external := wires) (mappedFrame := targetFrame)
      (mappedData := PUnit.unit) formalEvidence formalSites
      (Lambda.TermLeaf.Vars.fromTerm output ports)
      (EqualityNormalization.formalPorts wires)
      (authoritativeFrame.append []) authoritativeFrame
      commonRename positionalSourceRename commonRename
      authoritativeSourceRename sourceKeepCommutes targetKeepCommutes
      selectedCommutes argumentKeepCommutes argumentSelectedCommutes
      (termDataNaturality freeArity term) True.intro
  let oldLocals := structuralBefore ++ structuralAfter
  let pendingLocals := structuralBefore ++ .rel wires :: structuralAfter
  let pending : Region structuralOuter := .mk pendingLocals items
  let authoritativeItems :=
    (argumentItemsEdit flatFormalSites
      (EqualityNormalization.formalPorts wires)
      (normalizationOperation wires) authoritativeFrame PUnit.unit
      (fun _ _ _ => PUnit.unit)).1
  let authoritativePending := argumentNormalizedRegionAt
    (outer := structuralOuter) (localBefore := structuralBefore)
    (localAfter := structuralAfter) flatFormalSites
    (EqualityNormalization.formalPorts wires)
  let rawAuthoritativeItems :=
    (argumentItemsEdit formalSites
      (EqualityNormalization.formalPorts wires)
      (normalizationOperation wires) (authoritativeFrame.append [])
      PUnit.unit (fun _ _ _ => PUnit.unit)).1
  let rawAuthoritative := Region.ofItems rawAuthoritativeItems
  let flatAuthoritative := Region.ofItems authoritativeItems
  have renamedAuthoritativeEq :
      rawAuthoritative.renameWires authoritativeSourceRename =
        flatAuthoritative := by
    simpa only [rawAuthoritative, flatAuthoritative, authoritativeItems,
      rawAuthoritativeItems, Region.ofItems_renameWires] using
        congrArg Region.ofItems flatAuthoritativeEq
  let cleanupPresentation : RegionIso
      (WireEquiv.refl authoritativeSourceWires)
      (Region.adjoinAt [] .nil rawAuthoritative)
      flatAuthoritative :=
    (RegionIso.adjoinAtNil rawAuthoritative).symm.trans
      (RegionIso.ofEq renamedAuthoritativeEq)
  have sourceCleanupFlat :
      HostedStrict (Region.ofItems items) flatAuthoritative ∧
        HostedScope (Region.ofItems items) flatAuthoritative := by
    refine ⟨HostedStrict.iso (RegionIso.refl _) cleanupPresentation
        sourceCleanup.1, ?_⟩
    intro target rename
    exact (sourceCleanup.2 rename).trans
      ((HostedScope.ofIso cleanupPresentation) rename)
  have cleanupHosted : HostedStrict pending authoritativePending := by
    have lifted := HostedStrict.adjoinAt pendingLocals
      (Region.ofItems items) flatAuthoritative sourceCleanupFlat.1
    exact HostedStrict.iso
      (RegionIso.adjoinAtOfItems pendingLocals items).symm
      (by
        simpa only [authoritativePending, argumentNormalizedRegionAt,
          authoritativeItems] using
            RegionIso.adjoinAtOfItems pendingLocals authoritativeItems)
      lifted
  have cleanupHostedScope : HostedScope pending authoritativePending := by
    have lifted : HostedScope
        (Region.adjoinAt pendingLocals .nil (Region.ofItems items))
        (Region.adjoinAt pendingLocals .nil flatAuthoritative) := by
      intro target rename
      exact HostedScope.adjoinAt pendingLocals
        (Region.ofItems items) flatAuthoritative sourceCleanupFlat.2 rename
    intro target rename
    exact ((HostedScope.ofIso
        (RegionIso.adjoinAtOfItems pendingLocals items).symm) rename).trans
      ((lifted rename).trans
        ((HostedScope.ofIso (by
          simpa only [authoritativePending, argumentNormalizedRegionAt,
            authoritativeItems] using
              RegionIso.adjoinAtOfItems pendingLocals authoritativeItems))
          rename))
  have cleanupScope : ScopePreservation pending authoritativePending := by
    simpa only [Region.renameWires_id] using
      cleanupHostedScope WireRenaming.id
  have pendingCanonical :
      (request.occurrence.context.fill pending).Canonical := by
    simpa only [pending, pendingLocals] using request.pendingCanonical
  have pendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill pending) := by
    intro signature wire
    simpa only [pending, pendingLocals] using
      request.pendingExternalTwoEnded wire
  have authoritativeValidity := filledValidityOfScope
    request.occurrence.interface request.occurrence.context pending
    authoritativePending pendingCanonical pendingExternalTwoEnded cleanupScope
  have cleanupTelescope : Telescope request.polarity
      request.occurrence.interface request.occurrence.context
      authoritativePending pending authoritativeValidity.1
      authoritativeValidity.2 pendingCanonical pendingExternalTwoEnded :=
    telescopeOfHostedExact cleanupHosted.symm request.polarity
      request.occurrence.interface request.occurrence.context
      authoritativeValidity.1 authoritativeValidity.2 pendingCanonical
      pendingExternalTwoEnded request.continuation.1
  have authoritativeContinuation : Telescope request.polarity
      request.occurrence.interface request.occurrence.context
      authoritativePending request.endpoint authoritativeValidity.1
      authoritativeValidity.2 request.endpointCanonical
      request.endpointExternalTwoEnded :=
    telescopeTrans cleanupTelescope (by simpa only [pending, pendingLocals] using
      request.continuation)
  let positionalValues := Lambda.TermLeaf.Vars.fromTerm output ports
  have flatFormalCoherence : flatFormalSource =
      (argumentItemsEdit flatFormalSites positionalValues
        (normalizationOperation (Lambda.TermLeaf.arguments freeArity))
        targetFrame PUnit.unit (fun _ _ _ => PUnit.unit)).1 := by
    have mappedCoherence : formalSource.renameWires positionalSourceRename =
        (argumentItemsEdit formalSites positionalValues
          (normalizationOperation (Lambda.TermLeaf.arguments freeArity))
          (targetFrame.append []) PUnit.unit
          (fun _ _ _ => PUnit.unit)).1.renameWires
            positionalSourceRename :=
      congrArg (fun source => source.renameWires positionalSourceRename)
        formalCoherence
    exact flatSourceEq.symm.trans (mappedCoherence.trans flatPositionalEq)
  let positionalPending : Region structuralOuter :=
    .mk (structuralBefore ++
      .rel (Lambda.TermLeaf.arguments freeArity) :: structuralAfter)
      flatFormalSource
  have positionalEq : positionalPending =
      argumentNormalizedRegionAt
        (outer := structuralOuter) (localBefore := structuralBefore)
        (localAfter := structuralAfter) flatFormalSites positionalValues := by
    let positionalFrame : Transform.Frame
        (Lambda.TermLeaf.arguments freeArity)
        (structuralOuter ++ (structuralBefore ++ structuralAfter))
        (structuralOuter ++ (structuralBefore ++
          .rel (Lambda.TermLeaf.arguments freeArity) :: structuralAfter))
        (structuralOuter ++ (structuralBefore ++
          .rel (Lambda.TermLeaf.arguments freeArity) :: structuralAfter)) :=
      Transform.Frame.replace structuralOuter structuralBefore
        structuralAfter [.rel (Lambda.TermLeaf.arguments freeArity)]
        (Lambda.TermLeaf.arguments freeArity)
    have sourceIndependent := argumentItemsEdit_source_independent
      flatFormalSites positionalValues
      (normalizationOperation (Lambda.TermLeaf.arguments freeArity))
      targetFrame PUnit.unit (fun _ _ _ => PUnit.unit)
      (normalizationOperation (Lambda.TermLeaf.arguments freeArity))
      positionalFrame PUnit.unit (fun _ _ _ => PUnit.unit)
      (by
        intro wireSignature wire
        rfl)
      (by rfl)
    have normalizedCoherence : flatFormalSource =
        (argumentItemsEdit flatFormalSites positionalValues
          (normalizationOperation (Lambda.TermLeaf.arguments freeArity))
          positionalFrame PUnit.unit (fun _ _ _ => PUnit.unit)).1 :=
      flatFormalCoherence.trans sourceIndependent
    exact congrArg
      (Region.mk (structuralBefore ++
        .rel (Lambda.TermLeaf.arguments freeArity) :: structuralAfter))
      normalizedCoherence
  let recordedOutput := itemsEdit
    (operation := recordingOperation
      (Lambda.TermLeaf.operation freeArity term) wires)
    PUnit.unit flatFormalEvidence flatFormalSites
  let primitiveSites := recordingItemsSitesTarget flatFormalSites
  let output := itemsEdit
    (operation := Lambda.TermLeaf.operation freeArity term)
    PUnit.unit flatFormalEvidence primitiveSites
  have outputEndpointEq : recordedOutput.endpoint = output.endpoint :=
    recordingItemsEditEndpoint_eq flatFormalSites
  have targetKeepIdentity : targetFrame.targetKeep = WireRenaming.id := by
    apply WireRenaming.ext
    intro signature wire
    apply Var.appendCases (left := structuralOuter)
      (right := structuralBefore ++ structuralAfter)
      (motive := fun wire => targetFrame.targetKeep wire = wire)
    · intro outerSignature outerWire
      simp [targetFrame, Lambda.TermLeaf.rootFrame, Transform.Frame.replace,
        Transform.Frame.keep, Transform.Frame.localKeep]
    · intro localSignature localWire
      apply Var.appendCases (left := structuralBefore)
        (right := structuralAfter)
        (motive := fun localWire =>
          targetFrame.targetKeep
              (Var.appendRight structuralOuter localWire) =
            Var.appendRight structuralOuter localWire)
      · intro beforeSignature beforeWire
        simp [targetFrame, Lambda.TermLeaf.rootFrame, Transform.Frame.replace,
          Transform.Frame.keep, Transform.Frame.localKeep]
      · intro afterSignature afterWire
        simp [targetFrame, Lambda.TermLeaf.rootFrame, Transform.Frame.replace,
          Transform.Frame.keep, Transform.Frame.localKeep,
          Var.appendRight]
  obtain ⟨recordedLeafHosted, recordedLeafScope⟩ :=
    leafItemsEndpoint flatFormalEvidence flatFormalSites targetKeepIdentity
      (fun siteTargetKeepEq application site => by
        have endpoint := positionalTermLeafEndpoint freeArity term
          siteTargetKeepEq application site
        exact ⟨endpoint.1, endpoint.2⟩)
  have recordedLeafReverse : HostedScope recordedOutput.endpoint
      flatFormalResult := by
    intro target rename
    exact leafItemsReverseHostedScope flatFormalEvidence flatFormalSites
      targetKeepIdentity
      (fun siteTargetKeepEq application site =>
        positionalTermLeafEndpoint_reverseHostedScope freeArity term
          siteTargetKeepEq application site)
      rename
  have leafHosted : HostedStrict flatFormalResult output.endpoint := by
    rw [← outputEndpointEq]
    exact recordedLeafHosted
  have leafScope : ScopePreservation flatFormalResult output.endpoint := by
    rw [← outputEndpointEq]
    exact recordedLeafScope
  have leafReverse : HostedScope output.endpoint flatFormalResult := by
    intro target rename
    rw [← outputEndpointEq]
    exact recordedLeafReverse rename
  let stagedToFlatFormal : RegionIso (WireEquiv.refl common) staged
      flatFormalResult :=
    stagedPresentation.trans
      ((RegionIso.adjoinAtNil formalResult).symm.trans flatResultIso)
  have resultToFormal : HostedStrict result flatFormalResult :=
    HostedStrict.iso (RegionIso.refl result) stagedToFlatFormal hosted
  have resultToOutput : HostedStrict result output.endpoint :=
    HostedStrict.trans resultToFormal leafHosted
      (fun outer hostLocals rename hostItems =>
        HostedScope.adjoinHost leafReverse outer hostLocals rename hostItems)
  have resultToOutputScope : ScopePreservation result output.endpoint :=
    stagedScope.trans
      ((ScopePreservation.ofIso stagedToFlatFormal).trans leafScope)
  let instantiated := Region.adjoinAt oldLocals .nil result
  let prepared := Region.adjoinAt oldLocals .nil output.endpoint
  have instantiatedToPrepared : HostedStrict instantiated prepared := by
    simpa only [instantiated, prepared] using
      HostedStrict.adjoinAt oldLocals result output.endpoint resultToOutput
  have instantiatedToPreparedScope : ScopePreservation instantiated prepared :=
    adjoinAt_preserves_scope oldLocals .nil result output.endpoint
      resultToOutputScope
  have instantiatedCanonical :
      (request.occurrence.context.fill instantiated).Canonical := by
    simpa only [instantiated, oldLocals] using request.instantiatedCanonical
  have instantiatedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill instantiated) := by
    intro signature wire
    simpa only [instantiated, oldLocals] using
      request.instantiatedExternalTwoEnded wire
  have preparedValidity := filledValidityOfScope
    request.occurrence.interface request.occurrence.context instantiated
    prepared instantiatedCanonical instantiatedExternalTwoEnded
    instantiatedToPreparedScope
  have preparationTelescope : Telescope request.polarity
      request.occurrence.interface request.occurrence.context
      instantiated prepared instantiatedCanonical instantiatedExternalTwoEnded
      preparedValidity.1 preparedValidity.2 :=
    telescopeOfHostedExact instantiatedToPrepared request.polarity
      request.occurrence.interface request.occurrence.context
      instantiatedCanonical instantiatedExternalTwoEnded preparedValidity.1
      preparedValidity.2 request.continuation.1
  have authoritativeLocalCanonical : authoritativePending.Canonical :=
    request.occurrence.context.holeCanonical authoritativePending
      authoritativeValidity.1
  have authoritativeInvariant :
      Transform.RetainedIndexInvariant authoritativeFrame :=
    Transform.RetainedIndexInvariant.replace _ _ _ _ _
  have authoritativePaths := argumentItemsEdit_selectedPaths flatFormalSites
    (EqualityNormalization.formalPorts wires)
    (normalizationOperation wires) authoritativeFrame PUnit.unit
    (fun _ _ _ => PUnit.unit) authoritativeInvariant 0
  have formalInvariant : Transform.RetainedIndexInvariant targetFrame :=
    Transform.RetainedIndexInvariant.replace _ _ _ _ _
  have formalPaths := flatFormalSites.source_selectedPaths formalInvariant 0
  let selectedLocalIndex : Fin pendingLocals.length :=
    ⟨structuralBefore.length, by
      simp [pendingLocals]⟩
  have authoritativeRoot :=
    authoritativeLocalCanonical.1 selectedLocalIndex
  have selectedRooted : RegionPath.RootedTwo
      (flatFormalSource.incidencePaths
        (structuralOuter.length + structuralBefore.length) 0) := by
    have pathEq : flatFormalSource.incidencePaths
          (structuralOuter.length + structuralBefore.length) 0 =
        authoritativePending.items.incidencePaths
          (structuralOuter.length + structuralBefore.length) 0 := by
      calc
        flatFormalSource.incidencePaths
            (structuralOuter.length + structuralBefore.length) 0 =
            flatFormalSites.selectedPaths 0 := by
          simpa [targetFrame, Lambda.TermLeaf.rootFrame,
            Transform.Frame.replace, Transform.Frame.insertedHead]
            using formalPaths
        _ = authoritativePending.items.incidencePaths
            (structuralOuter.length + structuralBefore.length) 0 := by
          symm
          simpa [authoritativePending, argumentNormalizedRegionAt,
            authoritativeItems, authoritativeFrame,
            Transform.Frame.replace, Transform.Frame.insertedHead,
            normalizationFrame] using authoritativePaths
    rw [pathEq]
    simpa [authoritativePending, selectedLocalIndex, pendingLocals] using
      authoritativeRoot
  have primitiveNoPin : output.edit.NoSelectedPin :=
    itemsEdit_noSelectedPin primitiveSites
  let rawPrepared := Region.adjoinAt oldLocals .nil output.edit.run
  have rawPreparedCanonical : rawPrepared.Canonical := by
    dsimp only [rawPrepared]
    rw [output.run_eq]
    exact request.occurrence.context.holeCanonical prepared preparedValidity.1
  have positionalLocalValidity := Lambda.TermLeaf.target_source_validity
    output.edit primitiveNoPin rawPreparedCanonical selectedRooted
  have rawPreparedFilledCanonical :
      (request.occurrence.context.fill rawPrepared).Canonical := by
    dsimp only [rawPrepared]
    rw [output.run_eq]
    exact preparedValidity.1
  have rawPreparedFilledExternal : OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill rawPrepared) := by
    intro signature wire
    dsimp only [rawPrepared]
    rw [output.run_eq]
    exact preparedValidity.2 wire
  let rawToPositionalScope : ScopePreservation rawPrepared positionalPending := {
    canonical := fun _ => positionalLocalValidity.1
    incidenceNonempty := fun wire => by
      have paths : rawPrepared.incidencePaths wire.index.val =
          positionalPending.incidencePaths wire.index.val := by
        simpa only [rawPrepared, positionalPending, oldLocals] using
          positionalLocalValidity.2 wire
      simp only [paths]
    rootedTwo := fun wire rooted => by
      have paths : rawPrepared.incidencePaths wire.index.val =
          positionalPending.incidencePaths wire.index.val := by
        simpa only [rawPrepared, positionalPending, oldLocals] using
          positionalLocalValidity.2 wire
      rw [← paths]
      exact rooted
  }
  have positionalValidity := filledValidityOfScope
    request.occurrence.interface request.occurrence.context rawPrepared
    positionalPending rawPreparedFilledCanonical rawPreparedFilledExternal
    rawToPositionalScope
  have normalizationTelescope : Telescope request.polarity
      request.occurrence.interface request.occurrence.context
      positionalPending request.endpoint positionalValidity.1
      positionalValidity.2 request.endpointCanonical
      request.endpointExternalTwoEnded :=
    argumentNormalizationTelescopeAllAt
      (outer := structuralOuter) (localBefore := structuralBefore)
      (localAfter := structuralAfter) flatFormalSites positionalValues
      request.occurrence.interface request.occurrence.context positionalEq
      positionalValidity.1 positionalValidity.2 authoritativeValidity.1
      authoritativeValidity.2 request.endpointCanonical
      request.endpointExternalTwoEnded request.polarity request.continuation.1
      authoritativeContinuation
  let formalRequest : Telescope.Request instantiated positionalPending := {
    boundary := request.boundary
    source := request.source
    endpoint := request.endpoint
    polarity := request.polarity
    occurrence := request.occurrence
    instantiatedCanonical := instantiatedCanonical
    instantiatedExternalTwoEnded := instantiatedExternalTwoEnded
    pendingCanonical := positionalValidity.1
    pendingExternalTwoEnded := positionalValidity.2
    endpointCanonical := request.endpointCanonical
    endpointExternalTwoEnded := request.endpointExternalTwoEnded
    continuation := normalizationTelescope
  }
  let preparation : formalRequest.Preparation prepared := {
    prepared := prepared
    preparedCanonical := preparedValidity.1
    preparedExternalTwoEnded := preparedValidity.2
    rawPreparedCanonical := preparedValidity.1
    rawPreparedExternalTwoEnded := preparedValidity.2
    preparedIso := RegionIso.refl prepared
    telescope := by
      simpa only [formalRequest] using preparationTelescope
  }
  exact itemsTerm (freeArity := freeArity) (term := term)
    (localBefore := structuralBefore) (localAfter := structuralAfter)
    flatFormalEvidence primitiveSites formalRequest (by
      simpa only [prepared, oldLocals, output] using preparation)

end VisualProof.Rule.Completeness.Comprehension.LambdaTerm
