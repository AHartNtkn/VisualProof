import VisualProof.Rule.Completeness.Comprehension.Leaf.Accumulator

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

/-- Accumulate every selected application in one authoritative item sequence
into the single literal positional-Formal edit consumed at the binder home. -/
theorem accumulateAtomFormal
    {patternWires atomArguments common originalSourceWires
      originalTargetWires : List Sig}
    {pattern : OpenDiagram patternWires}
    {head : Var pattern.external (.rel atomArguments)}
    {ports : Vars pattern.external atomArguments}
    {tail : ItemSeq pattern.external}
    (body_eq :
      pattern.body = Region.ofItems (.cons (.atom head ports) tail))
    {originalFrame : Transform.Frame patternWires common
      originalSourceWires originalTargetWires}
    {operation : Transform.Operation patternWires}
    {data : operation.Data originalFrame}
    {source : ItemSeq originalSourceWires} {result : Region common}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
        originalFrame.sourceKeep originalFrame.selected source result)
    (sites : ItemsSites operation data evidence)
    {boundary : List Sig} {host : OpenDiagram boundary}
    (occurrence : Occurrence result host) :
    ∃ retained : List Sig,
      ∃ formalSource : ItemSeq
          (common ++ (.rel (positionalAtomWires atomArguments) :: retained)),
        ∃ formalResult : Region (common ++ retained),
          ∃ formalEvidence :
              _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
                (positionalAtomPattern atomArguments)
                (Leaf.Formal.rootFrame common [] retained []
                  atomArguments).sourceKeep
                (Leaf.Formal.rootFrame common [] retained []
                  atomArguments).selected
                formalSource formalResult,
            ∃ formalSites : ItemsSites
                (recordingOperation (Leaf.Formal.operation [] atomArguments)
                  pattern.external) PUnit.unit
                formalEvidence,
              ∃ formalCoherence : formalSource =
                  (argumentItemsEdit formalSites
                    (positionalAtomSelection head ports)
                    (normalizationOperation (positionalAtomWires atomArguments))
                    (Leaf.Formal.rootFrame common [] retained []
                      atomArguments) PUnit.unit
                    (fun _ _ _ => PUnit.unit)).1,
                let output := itemsEdit
                  (operation := recordingOperation
                    (Leaf.Formal.operation [] atomArguments) pattern.external)
                  PUnit.unit formalEvidence formalSites
                ∃ outputCanonical :
                  (occurrence.context.fill
                    (Region.adjoinAt retained .nil output.endpoint)).Canonical,
                ∃ outputExternalTwoEnded :
                    OpenDiagram.ExternalTwoEnded
                      occurrence.interface.boundaryWire
                      (occurrence.context.fill
                        (Region.adjoinAt retained .nil output.endpoint)),
                  EqualityNormalization.StrictEquates occurrence
                    (Region.adjoinAt retained .nil output.endpoint)
                    outputCanonical outputExternalTwoEnded := by
  let initialFrame : Transform.Frame (positionalAtomWires atomArguments)
      common (.rel (positionalAtomWires atomArguments) :: common) common :=
    Transform.Frame.replace [] [] common []
      (positionalAtomWires atomArguments)
  have folded : TargetItems
      (targetPattern := positionalAtomPattern atomArguments)
      (targetOperation := Leaf.Formal.operation [] atomArguments)
      evidence sites (positionalAtomSelection head ports) initialFrame
        PUnit.unit
        (fun retained _formalSource formalResult formalEvidence formalSites
            _coherence =>
          ∃ staged : Region common,
            HostedStrict result staged ∧
              ScopePreservation result staged ∧
                Nonempty (RegionIso (WireEquiv.refl common) staged
                  (Region.adjoinAt retained .nil formalResult))) :=
    accumulateHostedTargetWith evidence sites
      (positionalAtomSelection head ports)
      (outer := []) (before := []) (after := common)
      PUnit.unit ScopePreservation ScopePreservation.refl
      (fun locals before after scope =>
        adjoinAt_preserves_scope locals .nil before after scope)
      ScopePreservation.conjoin ScopePreservation.cut
      formalRecordingSiteNatural
      (fun {itemCommon itemSourceWires itemTargetWires} {itemFrame}
          {itemOperation} {itemData} application siteData
          {selectedTargetSourceWires selectedTargetWires} selectedFrame
          selectedData => by
        cases selectedData
        exact atomSelectedTargetItem body_eq application siteData selectedFrame)
  obtain ⟨retained, rawFormalSource, rawFormalResult, rawFormalEvidence,
      rawFormalSites, rawCoherence, rawStaged, rawHosted, rawScope,
      ⟨rawPresentation⟩⟩ := folded
  let canonicalFrame := Leaf.Formal.rootFrame common [] retained []
    atomArguments
  let move := WireEquiv.rotate [] common
    [.rel (positionalAtomWires atomArguments)]
  let forward := move.append (WireEquiv.refl retained)
  let reassociate : WireEquiv
      ((common ++ [.rel (positionalAtomWires atomArguments)]) ++ retained)
      (common ++ ([] ++ .rel (positionalAtomWires atomArguments) :: retained)) :=
    WireEquiv.ofEq (by simp)
  let sourceEquiv := forward.symm.trans reassociate
  let sourceRename := sourceEquiv.toRenaming
  let commonRename : WireRenaming (common ++ retained)
      (common ++ retained) := WireRenaming.id
  have sourceRename_common {wireSignature}
      (wire : Var common wireSignature) :
      sourceRename
          ((Var.appendRight [.rel (positionalAtomWires atomArguments)] wire).appendLeft
            retained) =
        wire.appendLeft
          (.rel (positionalAtomWires atomArguments) :: retained) := by
    let targetWire :=
      (wire.appendLeft [.rel (positionalAtomWires atomArguments)]).appendLeft
        retained
    have forwardEq : forward targetWire =
        (Var.appendRight [.rel (positionalAtomWires atomArguments)] wire).appendLeft
          retained := by
      calc
        forward targetWire =
            (move
              (wire.appendLeft
                [.rel (positionalAtomWires atomArguments)])).appendLeft
              retained :=
          WireEquiv.append_apply_left move (WireEquiv.refl retained)
            (wire.appendLeft
              [.rel (positionalAtomWires atomArguments)])
        _ = (Var.appendRight
              [.rel (positionalAtomWires atomArguments)] wire).appendLeft
            retained := by
          change
            ((WireEquiv.rotate [] common
                [.rel (positionalAtomWires atomArguments)])
              ((Var.appendRight [] wire).appendLeft
                [.rel (positionalAtomWires atomArguments)])).appendLeft
              retained = _
          rw [WireEquiv.rotate_apply_middle]
          rfl
    calc
      sourceRename
          ((Var.appendRight
              [.rel (positionalAtomWires atomArguments)] wire).appendLeft
            retained) =
          reassociate
            (forward.symm
              ((Var.appendRight
                  [.rel (positionalAtomWires atomArguments)] wire).appendLeft
                retained)) := rfl
      _ = reassociate (forward.symm (forward targetWire)) := by
        rw [forwardEq]
      _ = reassociate targetWire := by
        have inverseEq : forward.symm (forward targetWire) = targetWire :=
          forward.left_inv targetWire
        rw [inverseEq]
      _ = wire.appendLeft
          (.rel (positionalAtomWires atomArguments) :: retained) := by
        apply Var.eq_of_index_eq
        apply Fin.ext
        rw [WireEquiv.ofEq_index_val]
        simp [targetWire]
  have sourceRename_retained {wireSignature}
      (wire : Var retained wireSignature) :
      sourceRename (Var.appendRight
          (.rel (positionalAtomWires atomArguments) :: common) wire) =
        Var.appendRight common (.there wire) := by
    let targetWire := Var.appendRight
      (common ++ [.rel (positionalAtomWires atomArguments)]) wire
    have forwardEq : forward targetWire = Var.appendRight
        (.rel (positionalAtomWires atomArguments) :: common) wire := by
      change
        (move.append (WireEquiv.refl retained))
            (Var.appendRight
              ([] ++ common ++
                [.rel (positionalAtomWires atomArguments)]) wire) = _
      rw [WireEquiv.append_apply_right]
      rfl
    calc
      sourceRename
          (Var.appendRight
            (.rel (positionalAtomWires atomArguments) :: common) wire) =
          reassociate
            (forward.symm
              (Var.appendRight
                (.rel (positionalAtomWires atomArguments) :: common) wire)) :=
        rfl
      _ = reassociate (forward.symm (forward targetWire)) := by
        rw [forwardEq]
      _ = reassociate targetWire := by
        have inverseEq : forward.symm (forward targetWire) = targetWire :=
          forward.left_inv targetWire
        rw [inverseEq]
      _ = Var.appendRight common (.there wire) := by
        apply Var.eq_of_index_eq
        apply Fin.ext
        rw [WireEquiv.ofEq_index_val]
        change targetWire.index.val =
          (Var.appendRight common (.there wire)).index.val
        calc
          targetWire.index.val =
              (common ++
                [Sig.rel (positionalAtomWires atomArguments)]).length +
                wire.index.val :=
            Var.index_appendRight
              (common ++
                [Sig.rel (positionalAtomWires atomArguments)]) wire
          _ = common.length + (Var.there wire).index.val := by
            simp only [List.length_append, List.length_cons,
              List.length_nil, Nat.add_zero, Var.index, Fin.val_succ]
            omega
          _ = (Var.appendRight common (.there wire)).index.val :=
            (Var.index_appendRight common (.there wire)).symm
  have sourceRename_selected :
      sourceRename ((.here : Var
          (.rel (positionalAtomWires atomArguments) :: common)
          (.rel (positionalAtomWires atomArguments))).appendLeft retained) =
        Var.appendRight common
          ((.here : Var [.rel (positionalAtomWires atomArguments)]
            (.rel (positionalAtomWires atomArguments))).appendLeft retained) := by
    let targetWire := (Var.appendRight common (.here : Var
      [.rel (positionalAtomWires atomArguments)]
      (.rel (positionalAtomWires atomArguments)))).appendLeft retained
    have forwardEq : forward targetWire =
        ((.here : Var
          (.rel (positionalAtomWires atomArguments) :: common)
          (.rel (positionalAtomWires atomArguments))).appendLeft retained) := by
      calc
        forward targetWire =
            (move
              (Var.appendRight common
                (.here : Var [.rel (positionalAtomWires atomArguments)]
                  (.rel (positionalAtomWires atomArguments))))).appendLeft
              retained :=
          WireEquiv.append_apply_left move (WireEquiv.refl retained)
            (Var.appendRight common
              (.here : Var [.rel (positionalAtomWires atomArguments)]
                (.rel (positionalAtomWires atomArguments))))
        _ = ((.here : Var
              (.rel (positionalAtomWires atomArguments) :: common)
              (.rel (positionalAtomWires atomArguments))).appendLeft
            retained) := by
          change
            ((WireEquiv.rotate [] common
                [.rel (positionalAtomWires atomArguments)])
              (Var.appendRight ([] ++ common)
                (.here : Var [.rel (positionalAtomWires atomArguments)]
                  (.rel (positionalAtomWires atomArguments))))).appendLeft
              retained = _
          rw [WireEquiv.rotate_apply_suffix]
          rfl
    calc
      sourceRename
          ((.here : Var
            (.rel (positionalAtomWires atomArguments) :: common)
            (.rel (positionalAtomWires atomArguments))).appendLeft retained) =
          reassociate
            (forward.symm
              ((.here : Var
                (.rel (positionalAtomWires atomArguments) :: common)
                (.rel (positionalAtomWires atomArguments))).appendLeft
                  retained)) := rfl
      _ = reassociate (forward.symm (forward targetWire)) := by
        rw [forwardEq]
      _ = reassociate targetWire := by
        have inverseEq : forward.symm (forward targetWire) = targetWire :=
          forward.left_inv targetWire
        rw [inverseEq]
      _ = Var.appendRight common
          ((.here : Var [.rel (positionalAtomWires atomArguments)]
            (.rel (positionalAtomWires atomArguments))).appendLeft retained) := by
        apply Var.eq_of_index_eq
        apply Fin.ext
        rw [WireEquiv.ofEq_index_val]
        let binder := (.here :
          Var [.rel (positionalAtomWires atomArguments)]
            (.rel (positionalAtomWires atomArguments)))
        change targetWire.index.val =
          (Var.appendRight common (binder.appendLeft retained)).index.val
        calc
          targetWire.index.val =
              (Var.appendRight common binder).index.val :=
            Var.index_appendLeft (Var.appendRight common binder) retained
          _ = common.length + binder.index.val :=
            Var.index_appendRight common binder
          _ = common.length + (binder.appendLeft retained).index.val := by
            rw [Var.index_appendLeft]
          _ = (Var.appendRight common
                (binder.appendLeft retained)).index.val :=
            (Var.index_appendRight common
              (binder.appendLeft retained)).symm
  have keepCommutes : ∀ {wireSignature}
      (wire : Var (common ++ retained) wireSignature),
      sourceRename ((initialFrame.append retained).sourceKeep wire) =
        canonicalFrame.sourceKeep (commonRename wire) := by
    intro wireSignature wire
    apply Var.appendCases (left := common) (right := retained)
      (motive := fun wire =>
        sourceRename ((initialFrame.append retained).sourceKeep wire) =
          canonicalFrame.sourceKeep (commonRename wire))
    · intro inheritedSignature inherited
      rw [show (initialFrame.append retained).sourceKeep
          (inherited.appendLeft retained) =
          (Var.appendRight [.rel (positionalAtomWires atomArguments)] inherited).appendLeft
            retained by
        simp [initialFrame, Transform.Frame.replace,
          Transform.Frame.append, Transform.Frame.keep,
          Transform.Frame.localKeep, WireRenaming.appendRight,
          Var.appendMap, Var.appendRight]]
      rw [sourceRename_common]
      simp [commonRename, canonicalFrame,
        Leaf.Formal.rootFrame, Transform.Frame.replace,
        Transform.Frame.append, Transform.Frame.keep,
        Transform.Frame.localKeep, WireRenaming.appendRight,
        WireRenaming.id, Var.appendMap,
        Var.appendRight]
      unfold positionalAtomWires
      rfl
    · intro retainedSignature retainedWire
      rw [show (initialFrame.append retained).sourceKeep
          (Var.appendRight common retainedWire) =
          Var.appendRight
            (.rel (positionalAtomWires atomArguments) :: common)
            retainedWire by
        simp [initialFrame, Transform.Frame.replace,
          Transform.Frame.append, Transform.Frame.keep,
          Transform.Frame.localKeep, WireRenaming.appendRight,
          Var.appendMap, Var.appendRight]]
      rw [sourceRename_retained]
      simp [commonRename, canonicalFrame,
        Leaf.Formal.rootFrame, Transform.Frame.replace,
        Transform.Frame.append, Transform.Frame.keep,
        Transform.Frame.localKeep, WireRenaming.appendRight,
        WireRenaming.id, Region.adjoinMaterialWire, Var.appendMap,
        Var.appendRight]
      rfl
  have targetKeepCommutes : ∀ {wireSignature}
      (wire : Var (common ++ retained) wireSignature),
      commonRename ((initialFrame.append retained).targetKeep wire) =
        canonicalFrame.targetKeep (commonRename wire) := by
    intro wireSignature wire
    apply Var.appendCases (left := common) (right := retained)
      (motive := fun wire =>
        commonRename ((initialFrame.append retained).targetKeep wire) =
          canonicalFrame.targetKeep (commonRename wire))
    · intro inheritedSignature inherited
      simp [commonRename, initialFrame, canonicalFrame,
        Leaf.Formal.rootFrame, Transform.Frame.replace,
        Transform.Frame.append, Transform.Frame.keep,
        Transform.Frame.localKeep, WireRenaming.appendRight,
        WireRenaming.id, Var.appendMap, Var.appendRight]
    · intro retainedSignature retainedWire
      simp [commonRename, initialFrame, canonicalFrame,
        Leaf.Formal.rootFrame, Transform.Frame.replace,
        Transform.Frame.append, Transform.Frame.keep,
        Transform.Frame.localKeep, WireRenaming.appendRight,
        WireRenaming.id, Var.appendMap, Var.appendRight]
  have selectedCommutes :
      sourceRename (initialFrame.append retained).selected =
        canonicalFrame.selected := by
    rw [show (initialFrame.append retained).selected =
        ((.here : Var
          (.rel (positionalAtomWires atomArguments) :: common)
          (.rel (positionalAtomWires atomArguments))).appendLeft retained) by rfl]
    rw [sourceRename_selected]
    simp [canonicalFrame,
      Leaf.Formal.rootFrame, Transform.Frame.replace,
      Transform.Frame.append, Transform.Frame.insertedHead,
      Var.appendLeft, Var.appendRight]
    rfl
  obtain ⟨formalSource, formalResult, formalEvidence, formalSites,
      formalSourceEq, formalArgumentEq, ⟨formalPresentation⟩,
      ⟨formalEndpointPresentation⟩⟩ :=
    targetItemsReindex rawFormalEvidence rawFormalSites
      (positionalAtomSelection head ports) commonRename
      sourceRename commonRename keepCommutes targetKeepCommutes
      selectedCommutes formalRecordingSiteNatural
  have formalCoherence : formalSource =
      (argumentItemsEdit formalSites (positionalAtomSelection head ports)
        (normalizationOperation (positionalAtomWires atomArguments))
        canonicalFrame PUnit.unit (fun _ _ _ => PUnit.unit)).1 := by
    calc
      formalSource = rawFormalSource.renameWires sourceRename :=
        formalSourceEq.symm
      _ = (argumentItemsEdit rawFormalSites
            (positionalAtomSelection head ports)
            (normalizationOperation (positionalAtomWires atomArguments))
            (initialFrame.append retained) PUnit.unit
            (fun _ _ _ => PUnit.unit)).1.renameWires sourceRename :=
        congrArg (fun items => items.renameWires sourceRename) rawCoherence
      _ = _ := formalArgumentEq
  let output := itemsEdit
    (operation := recordingOperation
      (Leaf.Formal.operation [] atomArguments) pattern.external)
    PUnit.unit formalEvidence formalSites
  let exactOutput := Region.adjoinAt retained .nil output.endpoint
  let rawResultRename : RegionIso (WireEquiv.refl (common ++ retained))
      rawFormalResult (rawFormalResult.renameWires commonRename) := by
    simpa only [commonRename] using
      RegionIso.ofEq (Region.renameWires_id rawFormalResult).symm
  have targetKeepIdentity : canonicalFrame.targetKeep = WireRenaming.id :=
    formalRootFrame_targetKeep common retained atomArguments
  obtain ⟨leafHosted, leafScope⟩ :=
    leafItemsEndpoint formalEvidence formalSites targetKeepIdentity
      (fun siteTargetKeepEq application site =>
        positionalAtomLeafEndpoint atomArguments siteTargetKeepEq
          application site)
  let formalStart := Region.adjoinAt retained .nil formalResult
  let formalPresentationIso : RegionIso (WireEquiv.refl common)
      rawStaged formalStart :=
    (rawPresentation.trans
      (RegionIso.adjoinAt retained .nil rawResultRename)).trans
      (RegionIso.adjoinAt retained .nil formalPresentation)
  have liftedLeafHosted : HostedStrict formalStart exactOutput := by
    simpa only [formalStart, exactOutput] using
      HostedStrict.adjoinAt retained formalResult output.endpoint leafHosted
  have liftedLeafScope : ScopePreservation formalStart exactOutput := by
    simpa only [formalStart, exactOutput] using
      adjoinAt_preserves_scope retained .nil formalResult output.endpoint
        leafScope
  let emptyEquiv := WireEquiv.appendNil common
  let emptyRename : WireRenaming common (common ++ []) :=
    emptyEquiv.symm.toRenaming
  let emptyHostIso (region : Region common) :
      RegionIso (WireEquiv.refl common) region
        (Region.adjoinAt [] .nil (region.renameWires emptyRename)) := by
    let directToCollapsed := RegionIso.renameWires region WireRenaming.id
      (WireRenaming.comp emptyEquiv.toRenaming emptyRename)
      (WireEquiv.refl common) (by
        intro signature wire
        exact (emptyEquiv.right_inv wire).symm)
    let collapsedFromHosted :=
      (RegionIso.renameWiresComp region emptyRename
        emptyEquiv.toRenaming).symm
    let chained := (directToCollapsed.trans collapsedFromHosted).trans
      (RegionIso.adjoinAtNil (region.renameWires emptyRename))
    have ambientEq :
        (((WireEquiv.refl common).trans
          (WireEquiv.refl common).symm).trans
            (WireEquiv.refl common)) = WireEquiv.refl common := by
      apply WireEquiv.ext
      intro signature wire
      rfl
    simpa only [Region.renameWires_id] using chained.castAmbient ambientEq
  let sourceHosted := Region.adjoinAt [] .nil
    (result.renameWires emptyRename)
  let targetHosted := Region.adjoinAt [] .nil
    (rawStaged.renameWires emptyRename)
  let sourceHostedIso : RegionIso (WireEquiv.refl common)
      result sourceHosted := emptyHostIso result
  let targetHostedIso : RegionIso (WireEquiv.refl common)
      rawStaged targetHosted := emptyHostIso rawStaged
  have sourceHostedCanonical : sourceHosted.Canonical :=
    sourceHostedIso.canonical_iff.mp
      (occurrence.context.holeCanonical result occurrence.sourceCanonical)
  have sourceHostedNonempty : ∀ {signature} (wire : Var common signature),
      result.incidencePaths wire.index.val ≠ [] ↔
        sourceHosted.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    have lengthEq := sourceHostedIso.incidencePaths_length_eq wire
    exact ⟨fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [← lengthEq], fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [lengthEq]⟩
  let rootOccurrence : Occurrence sourceHosted host :=
    EqualityNormalization.presentationOccurrence occurrence
      sourceHostedCanonical sourceHostedNonempty sourceHostedIso
  have hostedScope : ScopePreservation sourceHosted targetHosted :=
    ScopePreservation.trans (ScopePreservation.ofIso sourceHostedIso.symm)
      (ScopePreservation.trans rawScope
        (ScopePreservation.ofIso targetHostedIso))
  have targetHostedCanonical : targetHosted.Canonical :=
    hostedScope.canonical sourceHostedCanonical
  have targetHostedReplacement := rootOccurrence.context.replaceCanonical
    sourceHosted targetHosted rootOccurrence.sourceCanonical
      targetHostedCanonical hostedScope.incidenceNonempty
  let sourceHostedEndpoint := rootOccurrence.interface.withBody
    (rootOccurrence.context.fill sourceHosted) rootOccurrence.sourceCanonical
      rootOccurrence.sourceExternalTwoEnded
  have targetHostedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      rootOccurrence.interface.boundaryWire
      (rootOccurrence.context.fill targetHosted) :=
    sourceHostedEndpoint.externalTwoEnded_of_nonempty_iff _
      targetHostedReplacement.2
  have hostedStrict := rawHosted common [] emptyRename .nil
    rootOccurrence targetHostedReplacement.1 targetHostedExternalTwoEnded
  let formalHosted := Region.adjoinAt [] .nil
    ((formalStart : Region common).renameWires emptyRename)
  let exactHosted := Region.adjoinAt [] .nil
    (exactOutput.renameWires emptyRename)
  let formalHostedIso : RegionIso (WireEquiv.refl common)
      targetHosted formalHosted :=
    (targetHostedIso.symm.trans formalPresentationIso).trans
      (emptyHostIso formalStart)
  have formalHostedCanonical : formalHosted.Canonical :=
    formalHostedIso.canonical_iff.mp targetHostedCanonical
  have formalHostedNonempty : ∀ {signature} (wire : Var common signature),
      targetHosted.incidencePaths wire.index.val ≠ [] ↔
        formalHosted.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    have lengthEq := formalHostedIso.incidencePaths_length_eq wire
    exact ⟨fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [← lengthEq], fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [lengthEq]⟩
  have formalReplacement := rootOccurrence.context.replaceCanonical
    targetHosted formalHosted targetHostedReplacement.1
      formalHostedCanonical formalHostedNonempty
  let targetHostedEndpoint := rootOccurrence.interface.withBody
    (rootOccurrence.context.fill targetHosted) targetHostedReplacement.1
      targetHostedExternalTwoEnded
  have formalHostedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      rootOccurrence.interface.boundaryWire
      (rootOccurrence.context.fill formalHosted) :=
    targetHostedEndpoint.externalTwoEnded_of_nonempty_iff _
      formalReplacement.2
  let targetHostedOccurrence : Occurrence targetHosted targetHostedEndpoint :=
    exactOccurrence rootOccurrence.interface rootOccurrence.context
      targetHosted targetHostedReplacement.1 targetHostedExternalTwoEnded
  let formalOccurrence : Occurrence formalHosted targetHostedEndpoint :=
    EqualityNormalization.presentationOccurrence targetHostedOccurrence
      formalHostedCanonical formalHostedNonempty formalHostedIso
  let formalEmptyIso := emptyHostIso formalStart
  let exactEmptyIso := emptyHostIso exactOutput
  have hostedLeafScope : ScopePreservation formalHosted exactHosted :=
    ScopePreservation.trans (ScopePreservation.ofIso formalEmptyIso.symm)
      (ScopePreservation.trans liftedLeafScope
        (ScopePreservation.ofIso exactEmptyIso))
  have exactHostedCanonical : exactHosted.Canonical :=
    hostedLeafScope.canonical formalHostedCanonical
  have exactHostedReplacement := formalOccurrence.context.replaceCanonical
    formalHosted exactHosted formalOccurrence.sourceCanonical
      exactHostedCanonical hostedLeafScope.incidenceNonempty
  let formalHostedEndpoint := formalOccurrence.interface.withBody
    (formalOccurrence.context.fill formalHosted)
      formalOccurrence.sourceCanonical formalOccurrence.sourceExternalTwoEnded
  have exactHostedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      formalOccurrence.interface.boundaryWire
      (formalOccurrence.context.fill exactHosted) :=
    formalHostedEndpoint.externalTwoEnded_of_nonempty_iff _
      exactHostedReplacement.2
  have leafStrict := liftedLeafHosted common [] emptyRename .nil
    formalOccurrence exactHostedReplacement.1
      exactHostedExternalTwoEnded
  have exactLocalCanonical : exactOutput.Canonical :=
    exactEmptyIso.canonical_iff.mpr exactHostedCanonical
  have exactNonempty : ∀ {signature} (wire : Var common signature),
      exactHosted.incidencePaths wire.index.val ≠ [] ↔
        exactOutput.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    have lengthEq := exactEmptyIso.incidencePaths_length_eq wire
    exact ⟨fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [lengthEq], fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [← lengthEq]⟩
  have exactReplacement := formalOccurrence.context.replaceCanonical
    exactHosted exactOutput exactHostedReplacement.1 exactLocalCanonical
      exactNonempty
  let exactHostedEndpoint := formalOccurrence.interface.withBody
    (formalOccurrence.context.fill exactHosted) exactHostedReplacement.1
      exactHostedExternalTwoEnded
  have exactExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      rootOccurrence.interface.boundaryWire
      (rootOccurrence.context.fill exactOutput) :=
    exactHostedEndpoint.externalTwoEnded_of_nonempty_iff _
      exactReplacement.2
  let exactTargetIso : OpenDiagramIso
      (formalOccurrence.interface.withBody
        (formalOccurrence.context.fill exactHosted)
        exactHostedReplacement.1 exactHostedExternalTwoEnded)
      (rootOccurrence.interface.withBody
        (rootOccurrence.context.fill exactOutput)
        exactReplacement.1 exactExternalTwoEnded) :=
    OpenDiagram.withBody_iso exactHostedReplacement.1 exactReplacement.1
      exactHostedExternalTwoEnded exactExternalTwoEnded
      (DiagramContext.fillIso rootOccurrence.context exactEmptyIso.symm)
  have presentedLeafStrict : EqualityNormalization.StrictEquates
      formalOccurrence exactOutput exactReplacement.1 exactExternalTwoEnded :=
    EqualityNormalization.StrictEquates.targetIso leafStrict exactTargetIso
  have presentedStrict : EqualityNormalization.StrictEquates rootOccurrence
      exactOutput exactReplacement.1 exactExternalTwoEnded :=
    ⟨hostedStrict.1.trans presentedLeafStrict.1,
      presentedLeafStrict.2.trans hostedStrict.2⟩
  have strict : EqualityNormalization.StrictEquates occurrence exactOutput
      exactReplacement.1 exactExternalTwoEnded := by
    simpa only [EqualityNormalization.StrictEquates, rootOccurrence,
      EqualityNormalization.presentationOccurrence] using presentedStrict
  exact ⟨retained, formalSource, formalResult, formalEvidence, formalSites,
    formalCoherence, exactReplacement.1, exactExternalTwoEnded, strict⟩

/-- Accumulate every selected application of an authoritative identity-headed
pattern into one literal IdentityLeaf edit consumed at the binder home. -/
theorem accumulateIdentity
    {patternWires common originalSourceWires originalTargetWires : List Sig}
    {signature : Sig} {arity : Nat}
    {pattern : OpenDiagram patternWires}
    {ports : Fin arity → Var pattern.external signature}
    {tail : ItemSeq pattern.external}
    (body_eq :
      pattern.body = Region.ofItems (.cons (.identity signature arity ports) tail))
    {originalFrame : Transform.Frame patternWires common
      originalSourceWires originalTargetWires}
    {operation : Transform.Operation patternWires}
    {data : operation.Data originalFrame}
    {source : ItemSeq originalSourceWires} {result : Region common}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        pattern
        originalFrame.sourceKeep originalFrame.selected source result)
    (sites : ItemsSites operation data evidence)
    {boundary : List Sig} {host : OpenDiagram boundary}
    (occurrence : Occurrence result host) :
    ∃ retained : List Sig,
      ∃ formalSource : ItemSeq
          (common ++ (.rel (List.replicate arity signature) :: retained)),
        ∃ formalResult : Region (common ++ retained),
          ∃ formalEvidence :
              _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
                (positionalIdentityPattern signature arity)
                (Leaf.Identity.rootFrame common [] retained signature arity).sourceKeep
                (Leaf.Identity.rootFrame common [] retained signature arity).selected
                formalSource formalResult,
            ∃ formalSites : ItemsSites
                (recordingOperation
                  (Leaf.Identity.operation signature arity) pattern.external)
                PUnit.unit
                formalEvidence,
              ∃ formalCoherence : formalSource =
                  (argumentItemsEdit formalSites
                    (Leaf.Identity.Vars.fromFn ports)
                    (normalizationOperation
                      (List.replicate arity signature))
                    (Leaf.Identity.rootFrame common [] retained signature arity)
                    PUnit.unit (fun _ _ _ => PUnit.unit)).1,
              let primitiveSites := recordingItemsSitesTarget formalSites
              let output := itemsEdit
                (operation := Leaf.Identity.operation signature arity)
                PUnit.unit formalEvidence primitiveSites
              ∃ outputCanonical :
                  (occurrence.context.fill
                    (Region.adjoinAt retained .nil output.endpoint)).Canonical,
                ∃ outputExternalTwoEnded :
                    OpenDiagram.ExternalTwoEnded
                      occurrence.interface.boundaryWire
                      (occurrence.context.fill
                        (Region.adjoinAt retained .nil output.endpoint)),
                  EqualityNormalization.StrictEquates occurrence
                    (Region.adjoinAt retained .nil output.endpoint)
                    outputCanonical outputExternalTwoEnded := by
  let initialFrame : Transform.Frame (List.replicate arity signature)
      common (.rel (List.replicate arity signature) :: common) common :=
    Transform.Frame.replace [] [] common []
      (List.replicate arity signature)
  have folded : TargetItems
      (targetPattern := positionalIdentityPattern signature arity)
      (targetOperation := Leaf.Identity.operation signature arity)
      evidence sites (Leaf.Identity.Vars.fromFn ports) initialFrame PUnit.unit
        (fun retained _formalSource formalResult formalEvidence formalSites
            _coherence =>
          ∃ staged : Region common,
            HostedStrict result staged ∧
              ScopePreservation result staged ∧
                Nonempty (RegionIso (WireEquiv.refl common) staged
                  (Region.adjoinAt retained .nil formalResult))) :=
    accumulateHostedTargetWith evidence sites
      (Leaf.Identity.Vars.fromFn ports)
      (outer := []) (before := []) (after := common)
      PUnit.unit ScopePreservation ScopePreservation.refl
      (fun locals before after scope =>
        adjoinAt_preserves_scope locals .nil before after scope)
      ScopePreservation.conjoin ScopePreservation.cut
      identityRecordingSiteNatural
      (fun {itemCommon itemSourceWires itemTargetWires} {itemFrame}
          {itemOperation} {itemData} application siteData
          {selectedTargetSourceWires selectedTargetWires} selectedFrame
          selectedData => by
        exact identitySelectedTargetItem body_eq application siteData
          selectedFrame)
  obtain ⟨retained, rawFormalSource, rawFormalResult, rawFormalEvidence,
      rawFormalSites, rawCoherence, rawStaged, rawHosted, rawScope,
      ⟨rawPresentation⟩⟩ := folded
  let canonicalFrame := Leaf.Identity.rootFrame common [] retained signature
    arity
  let move := WireEquiv.rotate [] common
    [.rel (List.replicate arity signature)]
  let forward := move.append (WireEquiv.refl retained)
  let reassociate : WireEquiv
      ((common ++ [.rel (List.replicate arity signature)]) ++ retained)
      (common ++ ([] ++ .rel (List.replicate arity signature) :: retained)) :=
    WireEquiv.ofEq (by simp)
  let sourceEquiv := forward.symm.trans reassociate
  let sourceRename := sourceEquiv.toRenaming
  let commonRename : WireRenaming (common ++ retained)
      (common ++ retained) := WireRenaming.id
  have sourceRename_common {wireSignature}
      (wire : Var common wireSignature) :
      sourceRename
          ((Var.appendRight
              [.rel (List.replicate arity signature)] wire).appendLeft
            retained) =
        wire.appendLeft
          (.rel (List.replicate arity signature) :: retained) := by
    let targetWire :=
      (wire.appendLeft [.rel (List.replicate arity signature)]).appendLeft
        retained
    have forwardEq : forward targetWire =
        (Var.appendRight [.rel (List.replicate arity signature)] wire).appendLeft
          retained := by
      calc
        forward targetWire =
            (move
              (wire.appendLeft
                [.rel (List.replicate arity signature)])).appendLeft
              retained :=
          WireEquiv.append_apply_left move (WireEquiv.refl retained)
            (wire.appendLeft [.rel (List.replicate arity signature)])
        _ = (Var.appendRight
              [.rel (List.replicate arity signature)] wire).appendLeft
            retained := by
          change
            ((WireEquiv.rotate [] common
                [.rel (List.replicate arity signature)])
              ((Var.appendRight [] wire).appendLeft
                [.rel (List.replicate arity signature)])).appendLeft
              retained = _
          rw [WireEquiv.rotate_apply_middle]
          rfl
    calc
      sourceRename
          ((Var.appendRight
              [.rel (List.replicate arity signature)] wire).appendLeft
            retained) =
          reassociate
            (forward.symm
              ((Var.appendRight
                  [.rel (List.replicate arity signature)] wire).appendLeft
                retained)) := rfl
      _ = reassociate (forward.symm (forward targetWire)) := by
        rw [forwardEq]
      _ = reassociate targetWire := by
        have inverseEq : forward.symm (forward targetWire) = targetWire :=
          forward.left_inv targetWire
        rw [inverseEq]
      _ = wire.appendLeft
          (.rel (List.replicate arity signature) :: retained) := by
        apply Var.eq_of_index_eq
        apply Fin.ext
        rw [WireEquiv.ofEq_index_val]
        simp [targetWire]
  have sourceRename_retained {wireSignature}
      (wire : Var retained wireSignature) :
      sourceRename (Var.appendRight
          (.rel (List.replicate arity signature) :: common) wire) =
        Var.appendRight common (.there wire) := by
    let targetWire := Var.appendRight
      (common ++ [.rel (List.replicate arity signature)]) wire
    have forwardEq : forward targetWire = Var.appendRight
        (.rel (List.replicate arity signature) :: common) wire := by
      change
        (move.append (WireEquiv.refl retained))
            (Var.appendRight
              ([] ++ common ++
                [.rel (List.replicate arity signature)]) wire) = _
      rw [WireEquiv.append_apply_right]
      rfl
    calc
      sourceRename
          (Var.appendRight
            (.rel (List.replicate arity signature) :: common) wire) =
          reassociate
            (forward.symm
              (Var.appendRight
                (.rel (List.replicate arity signature) :: common) wire)) :=
        rfl
      _ = reassociate (forward.symm (forward targetWire)) := by
        rw [forwardEq]
      _ = reassociate targetWire := by
        have inverseEq : forward.symm (forward targetWire) = targetWire :=
          forward.left_inv targetWire
        rw [inverseEq]
      _ = Var.appendRight common (.there wire) := by
        apply Var.eq_of_index_eq
        apply Fin.ext
        rw [WireEquiv.ofEq_index_val]
        change targetWire.index.val =
          (Var.appendRight common (.there wire)).index.val
        calc
          targetWire.index.val =
              (common ++
                [Sig.rel (List.replicate arity signature)]).length +
                wire.index.val :=
            Var.index_appendRight
              (common ++
                [Sig.rel (List.replicate arity signature)]) wire
          _ = common.length + (Var.there wire).index.val := by
            simp only [List.length_append, List.length_cons,
              List.length_nil, Nat.add_zero, Var.index, Fin.val_succ]
            omega
          _ = (Var.appendRight common (.there wire)).index.val :=
            (Var.index_appendRight common (.there wire)).symm
  have sourceRename_selected :
      sourceRename ((.here : Var
          (.rel (List.replicate arity signature) :: common)
          (.rel (List.replicate arity signature))).appendLeft retained) =
        Var.appendRight common
          ((.here : Var [.rel (List.replicate arity signature)]
            (.rel (List.replicate arity signature))).appendLeft retained) := by
    let targetWire := (Var.appendRight common (.here : Var
      [.rel (List.replicate arity signature)]
      (.rel (List.replicate arity signature)))).appendLeft retained
    have forwardEq : forward targetWire =
        ((.here : Var
          (.rel (List.replicate arity signature) :: common)
          (.rel (List.replicate arity signature))).appendLeft retained) := by
      calc
        forward targetWire =
            (move
              (Var.appendRight common
                (.here : Var [.rel (List.replicate arity signature)]
                  (.rel (List.replicate arity signature))))).appendLeft
              retained :=
          WireEquiv.append_apply_left move (WireEquiv.refl retained)
            (Var.appendRight common
              (.here : Var [.rel (List.replicate arity signature)]
                (.rel (List.replicate arity signature))))
        _ = ((.here : Var
              (.rel (List.replicate arity signature) :: common)
              (.rel (List.replicate arity signature))).appendLeft
            retained) := by
          change
            ((WireEquiv.rotate [] common
                [.rel (List.replicate arity signature)])
              (Var.appendRight ([] ++ common)
                (.here : Var [.rel (List.replicate arity signature)]
                  (.rel (List.replicate arity signature))))).appendLeft
              retained = _
          rw [WireEquiv.rotate_apply_suffix]
          rfl
    calc
      sourceRename
          ((.here : Var
            (.rel (List.replicate arity signature) :: common)
            (.rel (List.replicate arity signature))).appendLeft retained) =
          reassociate
            (forward.symm
              ((.here : Var
                (.rel (List.replicate arity signature) :: common)
                (.rel (List.replicate arity signature))).appendLeft
                  retained)) := rfl
      _ = reassociate (forward.symm (forward targetWire)) := by
        rw [forwardEq]
      _ = reassociate targetWire := by
        have inverseEq : forward.symm (forward targetWire) = targetWire :=
          forward.left_inv targetWire
        rw [inverseEq]
      _ = Var.appendRight common
          ((.here : Var [.rel (List.replicate arity signature)]
            (.rel (List.replicate arity signature))).appendLeft retained) := by
        apply Var.eq_of_index_eq
        apply Fin.ext
        rw [WireEquiv.ofEq_index_val]
        let binder := (.here :
          Var [.rel (List.replicate arity signature)]
            (.rel (List.replicate arity signature)))
        change targetWire.index.val =
          (Var.appendRight common (binder.appendLeft retained)).index.val
        calc
          targetWire.index.val =
              (Var.appendRight common binder).index.val :=
            Var.index_appendLeft (Var.appendRight common binder) retained
          _ = common.length + binder.index.val :=
            Var.index_appendRight common binder
          _ = common.length + (binder.appendLeft retained).index.val := by
            rw [Var.index_appendLeft]
          _ = (Var.appendRight common
                (binder.appendLeft retained)).index.val :=
            (Var.index_appendRight common
              (binder.appendLeft retained)).symm
  have keepCommutes : ∀ {wireSignature}
      (wire : Var (common ++ retained) wireSignature),
      sourceRename ((initialFrame.append retained).sourceKeep wire) =
        canonicalFrame.sourceKeep (commonRename wire) := by
    intro wireSignature wire
    apply Var.appendCases (left := common) (right := retained)
      (motive := fun wire =>
        sourceRename ((initialFrame.append retained).sourceKeep wire) =
          canonicalFrame.sourceKeep (commonRename wire))
    · intro inheritedSignature inherited
      rw [show (initialFrame.append retained).sourceKeep
          (inherited.appendLeft retained) =
          (Var.appendRight
            [.rel (List.replicate arity signature)] inherited).appendLeft
            retained by
        simp [initialFrame, Transform.Frame.replace,
          Transform.Frame.append, Transform.Frame.keep,
          Transform.Frame.localKeep, WireRenaming.appendRight,
          Var.appendMap, Var.appendRight]]
      rw [sourceRename_common]
      simp [commonRename, canonicalFrame,
        Leaf.Identity.rootFrame, Transform.Frame.replace,
        Transform.Frame.append, Transform.Frame.keep,
        Transform.Frame.localKeep, WireRenaming.appendRight,
        WireRenaming.id, Var.appendMap, Var.appendRight]
    · intro retainedSignature retainedWire
      rw [show (initialFrame.append retained).sourceKeep
          (Var.appendRight common retainedWire) =
          Var.appendRight
            (.rel (List.replicate arity signature) :: common)
            retainedWire by
        simp [initialFrame, Transform.Frame.replace,
          Transform.Frame.append, Transform.Frame.keep,
          Transform.Frame.localKeep, WireRenaming.appendRight,
          Var.appendMap, Var.appendRight]]
      rw [sourceRename_retained]
      simp [commonRename, canonicalFrame,
        Leaf.Identity.rootFrame, Transform.Frame.replace,
        Transform.Frame.append, Transform.Frame.keep,
        Transform.Frame.localKeep, WireRenaming.appendRight,
        WireRenaming.id, Var.appendMap, Var.appendRight]
  have targetKeepCommutes : ∀ {wireSignature}
      (wire : Var (common ++ retained) wireSignature),
      commonRename ((initialFrame.append retained).targetKeep wire) =
        canonicalFrame.targetKeep (commonRename wire) := by
    intro wireSignature wire
    apply Var.appendCases (left := common) (right := retained)
      (motive := fun wire =>
        commonRename ((initialFrame.append retained).targetKeep wire) =
          canonicalFrame.targetKeep (commonRename wire))
    · intro inheritedSignature inherited
      simp [commonRename, initialFrame, canonicalFrame,
        Leaf.Identity.rootFrame, Transform.Frame.replace,
        Transform.Frame.append, Transform.Frame.keep,
        Transform.Frame.localKeep, WireRenaming.appendRight,
        WireRenaming.id, Var.appendMap, Var.appendRight]
    · intro retainedSignature retainedWire
      simp [commonRename, initialFrame, canonicalFrame,
        Leaf.Identity.rootFrame, Transform.Frame.replace,
        Transform.Frame.append, Transform.Frame.keep,
        Transform.Frame.localKeep, WireRenaming.appendRight,
        WireRenaming.id, Var.appendMap, Var.appendRight]
  have selectedCommutes :
      sourceRename (initialFrame.append retained).selected =
        canonicalFrame.selected := by
    rw [show (initialFrame.append retained).selected =
        ((.here : Var
          (.rel (List.replicate arity signature) :: common)
          (.rel (List.replicate arity signature))).appendLeft retained) by rfl]
    rw [sourceRename_selected]
    simp [canonicalFrame,
      Leaf.Identity.rootFrame, Transform.Frame.replace,
      Transform.Frame.append, Transform.Frame.insertedHead,
      Var.appendLeft, Var.appendRight]
  obtain ⟨formalSource, formalResult, formalEvidence, formalSites,
      formalSourceEq, formalArgumentEq, ⟨formalPresentation⟩,
      ⟨formalEndpointPresentation⟩⟩ :=
    targetItemsReindex rawFormalEvidence rawFormalSites
      (Leaf.Identity.Vars.fromFn ports) commonRename
      sourceRename commonRename keepCommutes targetKeepCommutes
      selectedCommutes identityRecordingSiteNatural
  have formalCoherence : formalSource =
      (argumentItemsEdit formalSites (Leaf.Identity.Vars.fromFn ports)
        (normalizationOperation (List.replicate arity signature))
        canonicalFrame PUnit.unit (fun _ _ _ => PUnit.unit)).1 := by
    calc
      formalSource = rawFormalSource.renameWires sourceRename :=
        formalSourceEq.symm
      _ = (argumentItemsEdit rawFormalSites
            (Leaf.Identity.Vars.fromFn ports)
            (normalizationOperation (List.replicate arity signature))
            (initialFrame.append retained) PUnit.unit
            (fun _ _ _ => PUnit.unit)).1.renameWires sourceRename :=
        congrArg (fun items => items.renameWires sourceRename) rawCoherence
      _ = _ := formalArgumentEq
  let recordedOutput := itemsEdit
    (operation := recordingOperation
      (Leaf.Identity.operation signature arity) pattern.external)
    PUnit.unit formalEvidence formalSites
  let primitiveSites := recordingItemsSitesTarget formalSites
  let output := itemsEdit
    (operation := Leaf.Identity.operation signature arity)
    PUnit.unit formalEvidence primitiveSites
  have recordedEndpointEq : recordedOutput.endpoint = output.endpoint :=
    recordingItemsEditEndpoint_eq formalSites
  let exactOutput := Region.adjoinAt retained .nil output.endpoint
  let rawResultRename : RegionIso (WireEquiv.refl (common ++ retained))
      rawFormalResult (rawFormalResult.renameWires commonRename) := by
    simpa only [commonRename] using
      RegionIso.ofEq (Region.renameWires_id rawFormalResult).symm
  have targetKeepIdentity : canonicalFrame.targetKeep = WireRenaming.id := by
    simpa only [canonicalFrame] using
      formalRootFrame_targetKeep common retained
        (List.replicate arity signature)
  obtain ⟨recordedLeafHosted, recordedLeafScope⟩ :=
    leafItemsEndpoint formalEvidence formalSites targetKeepIdentity
      (fun siteTargetKeepEq application site =>
        positionalIdentityLeafEndpoint signature arity siteTargetKeepEq
          application site)
  have leafHosted : HostedStrict formalResult output.endpoint := by
    rw [← recordedEndpointEq]
    exact recordedLeafHosted
  have leafScope : ScopePreservation formalResult output.endpoint := by
    rw [← recordedEndpointEq]
    exact recordedLeafScope
  let formalStart := Region.adjoinAt retained .nil formalResult
  let formalPresentationIso : RegionIso (WireEquiv.refl common)
      rawStaged formalStart :=
    (rawPresentation.trans
      (RegionIso.adjoinAt retained .nil rawResultRename)).trans
      (RegionIso.adjoinAt retained .nil formalPresentation)
  have liftedLeafHosted : HostedStrict formalStart exactOutput := by
    simpa only [formalStart, exactOutput] using
      HostedStrict.adjoinAt retained formalResult output.endpoint leafHosted
  have liftedLeafScope : ScopePreservation formalStart exactOutput := by
    simpa only [formalStart, exactOutput] using
      adjoinAt_preserves_scope retained .nil formalResult output.endpoint
        leafScope
  let emptyEquiv := WireEquiv.appendNil common
  let emptyRename : WireRenaming common (common ++ []) :=
    emptyEquiv.symm.toRenaming
  let emptyHostIso (region : Region common) :
      RegionIso (WireEquiv.refl common) region
        (Region.adjoinAt [] .nil (region.renameWires emptyRename)) := by
    let directToCollapsed := RegionIso.renameWires region WireRenaming.id
      (WireRenaming.comp emptyEquiv.toRenaming emptyRename)
      (WireEquiv.refl common) (by
        intro signature wire
        exact (emptyEquiv.right_inv wire).symm)
    let collapsedFromHosted :=
      (RegionIso.renameWiresComp region emptyRename
        emptyEquiv.toRenaming).symm
    let chained := (directToCollapsed.trans collapsedFromHosted).trans
      (RegionIso.adjoinAtNil (region.renameWires emptyRename))
    have ambientEq :
        (((WireEquiv.refl common).trans
          (WireEquiv.refl common).symm).trans
            (WireEquiv.refl common)) = WireEquiv.refl common := by
      apply WireEquiv.ext
      intro signature wire
      rfl
    simpa only [Region.renameWires_id] using chained.castAmbient ambientEq
  let sourceHosted := Region.adjoinAt [] .nil
    (result.renameWires emptyRename)
  let targetHosted := Region.adjoinAt [] .nil
    (rawStaged.renameWires emptyRename)
  let sourceHostedIso : RegionIso (WireEquiv.refl common)
      result sourceHosted := emptyHostIso result
  let targetHostedIso : RegionIso (WireEquiv.refl common)
      rawStaged targetHosted := emptyHostIso rawStaged
  have sourceHostedCanonical : sourceHosted.Canonical :=
    sourceHostedIso.canonical_iff.mp
      (occurrence.context.holeCanonical result occurrence.sourceCanonical)
  have sourceHostedNonempty : ∀ {signature} (wire : Var common signature),
      result.incidencePaths wire.index.val ≠ [] ↔
        sourceHosted.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    have lengthEq := sourceHostedIso.incidencePaths_length_eq wire
    exact ⟨fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [← lengthEq], fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [lengthEq]⟩
  let rootOccurrence : Occurrence sourceHosted host :=
    EqualityNormalization.presentationOccurrence occurrence
      sourceHostedCanonical sourceHostedNonempty sourceHostedIso
  have hostedScope : ScopePreservation sourceHosted targetHosted :=
    ScopePreservation.trans (ScopePreservation.ofIso sourceHostedIso.symm)
      (ScopePreservation.trans rawScope
        (ScopePreservation.ofIso targetHostedIso))
  have targetHostedCanonical : targetHosted.Canonical :=
    hostedScope.canonical sourceHostedCanonical
  have targetHostedReplacement := rootOccurrence.context.replaceCanonical
    sourceHosted targetHosted rootOccurrence.sourceCanonical
      targetHostedCanonical hostedScope.incidenceNonempty
  let sourceHostedEndpoint := rootOccurrence.interface.withBody
    (rootOccurrence.context.fill sourceHosted) rootOccurrence.sourceCanonical
      rootOccurrence.sourceExternalTwoEnded
  have targetHostedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      rootOccurrence.interface.boundaryWire
      (rootOccurrence.context.fill targetHosted) :=
    sourceHostedEndpoint.externalTwoEnded_of_nonempty_iff _
      targetHostedReplacement.2
  have hostedStrict := rawHosted common [] emptyRename .nil
    rootOccurrence targetHostedReplacement.1 targetHostedExternalTwoEnded
  let formalHosted := Region.adjoinAt [] .nil
    ((formalStart : Region common).renameWires emptyRename)
  let exactHosted := Region.adjoinAt [] .nil
    (exactOutput.renameWires emptyRename)
  let formalHostedIso : RegionIso (WireEquiv.refl common)
      targetHosted formalHosted :=
    (targetHostedIso.symm.trans formalPresentationIso).trans
      (emptyHostIso formalStart)
  have formalHostedCanonical : formalHosted.Canonical :=
    formalHostedIso.canonical_iff.mp targetHostedCanonical
  have formalHostedNonempty : ∀ {signature} (wire : Var common signature),
      targetHosted.incidencePaths wire.index.val ≠ [] ↔
        formalHosted.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    have lengthEq := formalHostedIso.incidencePaths_length_eq wire
    exact ⟨fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [← lengthEq], fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [lengthEq]⟩
  have formalReplacement := rootOccurrence.context.replaceCanonical
    targetHosted formalHosted targetHostedReplacement.1
      formalHostedCanonical formalHostedNonempty
  let targetHostedEndpoint := rootOccurrence.interface.withBody
    (rootOccurrence.context.fill targetHosted) targetHostedReplacement.1
      targetHostedExternalTwoEnded
  have formalHostedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      rootOccurrence.interface.boundaryWire
      (rootOccurrence.context.fill formalHosted) :=
    targetHostedEndpoint.externalTwoEnded_of_nonempty_iff _
      formalReplacement.2
  let targetHostedOccurrence : Occurrence targetHosted targetHostedEndpoint :=
    exactOccurrence rootOccurrence.interface rootOccurrence.context
      targetHosted targetHostedReplacement.1 targetHostedExternalTwoEnded
  let formalOccurrence : Occurrence formalHosted targetHostedEndpoint :=
    EqualityNormalization.presentationOccurrence targetHostedOccurrence
      formalHostedCanonical formalHostedNonempty formalHostedIso
  let formalEmptyIso := emptyHostIso formalStart
  let exactEmptyIso := emptyHostIso exactOutput
  have hostedLeafScope : ScopePreservation formalHosted exactHosted :=
    ScopePreservation.trans (ScopePreservation.ofIso formalEmptyIso.symm)
      (ScopePreservation.trans liftedLeafScope
        (ScopePreservation.ofIso exactEmptyIso))
  have exactHostedCanonical : exactHosted.Canonical :=
    hostedLeafScope.canonical formalHostedCanonical
  have exactHostedReplacement := formalOccurrence.context.replaceCanonical
    formalHosted exactHosted formalOccurrence.sourceCanonical
      exactHostedCanonical hostedLeafScope.incidenceNonempty
  let formalHostedEndpoint := formalOccurrence.interface.withBody
    (formalOccurrence.context.fill formalHosted)
      formalOccurrence.sourceCanonical formalOccurrence.sourceExternalTwoEnded
  have exactHostedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      formalOccurrence.interface.boundaryWire
      (formalOccurrence.context.fill exactHosted) :=
    formalHostedEndpoint.externalTwoEnded_of_nonempty_iff _
      exactHostedReplacement.2
  have leafStrict := liftedLeafHosted common [] emptyRename .nil
    formalOccurrence exactHostedReplacement.1
      exactHostedExternalTwoEnded
  have exactLocalCanonical : exactOutput.Canonical :=
    exactEmptyIso.canonical_iff.mpr exactHostedCanonical
  have exactNonempty : ∀ {signature} (wire : Var common signature),
      exactHosted.incidencePaths wire.index.val ≠ [] ↔
        exactOutput.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    have lengthEq := exactEmptyIso.incidencePaths_length_eq wire
    exact ⟨fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [lengthEq], fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [← lengthEq]⟩
  have exactReplacement := formalOccurrence.context.replaceCanonical
    exactHosted exactOutput exactHostedReplacement.1 exactLocalCanonical
      exactNonempty
  let exactHostedEndpoint := formalOccurrence.interface.withBody
    (formalOccurrence.context.fill exactHosted) exactHostedReplacement.1
      exactHostedExternalTwoEnded
  have exactExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      rootOccurrence.interface.boundaryWire
      (rootOccurrence.context.fill exactOutput) :=
    exactHostedEndpoint.externalTwoEnded_of_nonempty_iff _
      exactReplacement.2
  let exactTargetIso : OpenDiagramIso
      (formalOccurrence.interface.withBody
        (formalOccurrence.context.fill exactHosted)
        exactHostedReplacement.1 exactHostedExternalTwoEnded)
      (rootOccurrence.interface.withBody
        (rootOccurrence.context.fill exactOutput)
        exactReplacement.1 exactExternalTwoEnded) :=
    OpenDiagram.withBody_iso exactHostedReplacement.1 exactReplacement.1
      exactHostedExternalTwoEnded exactExternalTwoEnded
      (DiagramContext.fillIso rootOccurrence.context exactEmptyIso.symm)
  have presentedLeafStrict : EqualityNormalization.StrictEquates
      formalOccurrence exactOutput exactReplacement.1 exactExternalTwoEnded :=
    EqualityNormalization.StrictEquates.targetIso leafStrict exactTargetIso
  have presentedStrict : EqualityNormalization.StrictEquates rootOccurrence
      exactOutput exactReplacement.1 exactExternalTwoEnded :=
    ⟨hostedStrict.1.trans presentedLeafStrict.1,
      presentedLeafStrict.2.trans hostedStrict.2⟩
  have strict : EqualityNormalization.StrictEquates occurrence exactOutput
      exactReplacement.1 exactExternalTwoEnded := by
    simpa only [EqualityNormalization.StrictEquates, rootOccurrence,
      EqualityNormalization.presentationOccurrence] using presentedStrict
  exact ⟨retained, formalSource, formalResult, formalEvidence, formalSites,
    formalCoherence, exactReplacement.1, exactExternalTwoEnded, strict⟩

/-- Extend a positional selected-wire argument tuple to the authoritative
boundary tuple, then contract the positional prefix.  This is the common
argument-normalization continuation used by both leaf compilers. -/
theorem argumentNormalizationTelescope
    {recordedArguments external common retained boundary : List Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments (common ++ retained)
      recordedSourceWires recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (common ++ retained)}
    {recordedEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (positionalValues : Vars external recordedArguments)
    (externalNonempty : external ≠ [])
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external common)
    {positionalPending endpoint : Region common}
    (positionalEq : positionalPending =
      argumentNormalizedRegion recordedSites positionalValues)
    (positionalCanonical : (context.fill positionalPending).Canonical)
    (positionalExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill positionalPending))
    (authoritativeCanonical :
      (context.fill (argumentNormalizedRegion recordedSites
        (EqualityNormalization.formalPorts external))).Canonical)
    (authoritativeExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire
      (context.fill (argumentNormalizedRegion recordedSites
        (EqualityNormalization.formalPorts external))))
    (endpointCanonical : (context.fill endpoint).Canonical)
    (endpointExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill endpoint))
    (polarity : Polarity) (polarityEq : context.polarity = polarity)
    (continuation : Telescope polarity interface context
      (argumentNormalizedRegion recordedSites
        (EqualityNormalization.formalPorts external)) endpoint
      authoritativeCanonical authoritativeExternalTwoEnded endpointCanonical
      endpointExternalTwoEnded) :
    Telescope polarity interface context positionalPending endpoint
      positionalCanonical positionalExternalTwoEnded endpointCanonical
      endpointExternalTwoEnded := by
  let authoritativeValues := EqualityNormalization.formalPorts external
  let extendedValues := Theory.Vars.extend positionalValues authoritativeValues
  let extendedPending := argumentNormalizedRegion recordedSites extendedValues
  have extendedValidity := argumentExtendedValidity recordedSites
    positionalValues interface context authoritativeCanonical
      authoritativeExternalTwoEnded
  have contractTelescope : Telescope polarity interface context
      extendedPending endpoint extendedValidity.1 extendedValidity.2
      endpointCanonical endpointExternalTwoEnded := by
    simpa only [extendedPending, extendedValues, authoritativeValues] using
      argumentVarsContractTelescope recordedSites positionalValues interface
        context authoritativeCanonical authoritativeExternalTwoEnded
        endpointCanonical endpointExternalTwoEnded polarity polarityEq
        continuation
  have positionalNormalizedCanonical :
      (context.fill
        (argumentNormalizedRegion recordedSites positionalValues)).Canonical :=
    positionalEq ▸ positionalCanonical
  have positionalNormalizedExternal : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire
      (context.fill (argumentNormalizedRegion recordedSites positionalValues)) :=
    positionalEq ▸ positionalExternalTwoEnded
  have positionalSourceCanonical :
      (context.fill (polaritySource polarity positionalPending endpoint)).Canonical := by
    cases polarity
    · exact positionalCanonical
    · exact endpointCanonical
  have positionalSourceExternal : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire
      (context.fill (polaritySource polarity positionalPending endpoint)) := by
    intro signature wire
    cases polarity
    · exact positionalExternalTwoEnded wire
    · exact endpointExternalTwoEnded wire
  let positionalSource := interface.withBody
    (context.fill (polaritySource polarity positionalPending endpoint))
    positionalSourceCanonical positionalSourceExternal
  have normalizedSourceCanonical :
      (context.fill (polaritySource polarity
        (argumentNormalizedRegion recordedSites positionalValues)
        endpoint)).Canonical := by
    cases polarity
    · exact positionalNormalizedCanonical
    · exact endpointCanonical
  have normalizedSourceExternal : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire
      (context.fill (polaritySource polarity
        (argumentNormalizedRegion recordedSites positionalValues)
        endpoint)) := by
    intro signature wire
    cases polarity
    · exact positionalNormalizedExternal wire
    · exact endpointExternalTwoEnded wire
  let normalizedOccurrence : Occurrence
      (polaritySource polarity
        (argumentNormalizedRegion recordedSites positionalValues) endpoint)
      positionalSource := {
    interface := interface
    context := context
    sourceCanonical := normalizedSourceCanonical
    sourceExternalTwoEnded := normalizedSourceExternal
    host_iso := by
      cases polarity with
      | positive =>
          simpa only [positionalSource, polaritySource] using
            OpenDiagram.withBody_iso positionalCanonical
              positionalNormalizedCanonical positionalExternalTwoEnded
              positionalNormalizedExternal
              (DiagramContext.fillIso context (RegionIso.ofEq positionalEq))
      | negative =>
          simpa only [positionalSource, polaritySource] using
            OpenDiagramIso.refl
              (interface.withBody (context.fill endpoint) endpointCanonical
                endpointExternalTwoEnded)
  }
  let projectionRequest : Telescope.Request
      (argumentNormalizedRegion recordedSites positionalValues)
      extendedPending := {
    boundary := boundary
    source := positionalSource
    endpoint := endpoint
    polarity := polarity
    occurrence := normalizedOccurrence
    instantiatedCanonical := positionalNormalizedCanonical
    instantiatedExternalTwoEnded := positionalNormalizedExternal
    pendingCanonical := extendedValidity.1
    pendingExternalTwoEnded := extendedValidity.2
    endpointCanonical := endpointCanonical
    endpointExternalTwoEnded := endpointExternalTwoEnded
    continuation := contractTelescope
  }
  have projectionCompiled : projectionRequest.Result := by
    obtain ⟨authoritativeSignature, authoritativeRest, authoritativeHead,
        authoritativeTail, authoritativeArgumentsEq,
        authoritativeValuesEq⟩ :=
      EqualityNormalization.formalPorts_cons_of_nonempty externalNonempty
    let extendedCons := Theory.Vars.extend positionalValues
      (Theory.Vars.cons authoritativeHead authoritativeTail)
    have extendedArgumentsEq :
        recordedArguments ++ external =
          recordedArguments ++ (authoritativeSignature :: authoritativeRest) :=
      congrArg (List.append recordedArguments) authoritativeArgumentsEq
    have extendedValuesEq : HEq extendedValues extendedCons := by
      exact varsExtendHEqRight positionalValues authoritativeValues
        (Theory.Vars.cons authoritativeHead authoritativeTail)
        authoritativeArgumentsEq authoritativeValuesEq
    let pendingIso := argumentNormalizationPresentation recordedSites
      extendedValues extendedCons extendedArgumentsEq extendedValuesEq
    exact argumentVarsProjectionCompiles (boundary := boundary) recordedSites
      positionalValues authoritativeHead authoritativeTail projectionRequest
      pendingIso authoritativeCanonical authoritativeExternalTwoEnded
  have optional : ∀ {first last : OpenDiagram boundary},
      Relation.TransGen Step first last → Relation.ReflTransGen Step first last := by
    intro first last steps
    induction steps with
    | single step => exact .tail .refl step
    | tail _ step induction => exact .tail induction step
  cases polarity with
  | positive =>
      have exactCompiled : Relation.TransGen Step
          (interface.withBody (context.fill positionalPending)
            positionalCanonical positionalExternalTwoEnded)
          (interface.withBody (context.fill endpoint)
            endpointCanonical endpointExternalTwoEnded) := by
        simpa [projectionRequest, normalizedOccurrence, positionalSource,
          exactOccurrence, polaritySource, polarityTarget] using
            projectionCompiled
      exact ⟨polarityEq, optional exactCompiled⟩
  | negative =>
      let targetIso : OpenDiagramIso
          (interface.withBody
            (context.fill
              (argumentNormalizedRegion recordedSites positionalValues))
            positionalNormalizedCanonical positionalNormalizedExternal)
          (interface.withBody (context.fill positionalPending)
            positionalCanonical positionalExternalTwoEnded) :=
        OpenDiagram.withBody_iso positionalNormalizedCanonical
          positionalCanonical positionalNormalizedExternal
          positionalExternalTwoEnded
          (DiagramContext.fillIso context (RegionIso.ofEq positionalEq.symm))
      have exactCompiled : Relation.TransGen Step
          (interface.withBody (context.fill endpoint)
            endpointCanonical endpointExternalTwoEnded)
          (interface.withBody
            (context.fill
              (argumentNormalizedRegion recordedSites positionalValues))
            positionalNormalizedCanonical positionalNormalizedExternal) := by
        simpa [projectionRequest, normalizedOccurrence, positionalSource,
          exactOccurrence, polaritySource, polarityTarget] using
            projectionCompiled
      exact ⟨polarityEq, optional (transGen_iso
        (OpenDiagramIso.refl _) exactCompiled targetIso)⟩

/-- Argument normalization including the structurally empty boundary case,
where the positional and authoritative tuples are both empty and no argument
step is required. -/
theorem argumentNormalizationTelescopeAll
    {recordedArguments external common retained boundary : List Sig}
    {recordedPattern : OpenDiagram recordedArguments}
    {recordedOperation : Transform.Operation recordedArguments}
    {recordedFrame : Transform.Frame recordedArguments (common ++ retained)
      recordedSourceWires recordedTargetWires}
    {recordedData : recordedOperation.Data recordedFrame}
    {recordedSource : ItemSeq recordedSourceWires}
    {recordedResult : Region (common ++ retained)}
    {recordedEvidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        recordedPattern recordedFrame.sourceKeep recordedFrame.selected
        recordedSource recordedResult}
    (recordedSites : ItemsSites
      (recordingOperation recordedOperation external) recordedData
      recordedEvidence)
    (positionalValues : Vars external recordedArguments)
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external common)
    {positionalPending endpoint : Region common}
    (positionalEq : positionalPending =
      argumentNormalizedRegion recordedSites positionalValues)
    (positionalCanonical : (context.fill positionalPending).Canonical)
    (positionalExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill positionalPending))
    (authoritativeCanonical :
      (context.fill (argumentNormalizedRegion recordedSites
        (EqualityNormalization.formalPorts external))).Canonical)
    (authoritativeExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire
      (context.fill (argumentNormalizedRegion recordedSites
        (EqualityNormalization.formalPorts external))))
    (endpointCanonical : (context.fill endpoint).Canonical)
    (endpointExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill endpoint))
    (polarity : Polarity) (polarityEq : context.polarity = polarity)
    (continuation : Telescope polarity interface context
      (argumentNormalizedRegion recordedSites
        (EqualityNormalization.formalPorts external)) endpoint
      authoritativeCanonical authoritativeExternalTwoEnded endpointCanonical
      endpointExternalTwoEnded) :
    Telescope polarity interface context positionalPending endpoint
      positionalCanonical positionalExternalTwoEnded endpointCanonical
      endpointExternalTwoEnded := by
  cases external with
  | nil =>
      cases positionalValues with
      | nil =>
          simpa only [positionalEq, EqualityNormalization.formalPorts,
            Erasure.Exposure.identityBoundary] using continuation
      | cons head tail => exact nomatch head
  | cons signature rest =>
      exact argumentNormalizationTelescope recordedSites positionalValues
        (by simp) interface context positionalEq positionalCanonical
        positionalExternalTwoEnded authoritativeCanonical
        authoritativeExternalTwoEnded endpointCanonical
        endpointExternalTwoEnded polarity polarityEq continuation


/-- The direct singleton-atom branch: accumulate every authoritative selected
site into one literal Formal edit, prepare its exact deterministic endpoint,
and run the single directed FormalApplication primitive at the binder home. -/
theorem atomFormal
    {patternWires atomArguments common originalSourceWires
      originalTargetWires : List Sig}
    {pattern : OpenDiagram patternWires}
    {head : Var pattern.external (.rel atomArguments)}
    {ports : Vars pattern.external atomArguments}
    {tail : ItemSeq pattern.external}
    (body_eq :
      pattern.body = Region.ofItems (.cons (.atom head ports) tail))
    {originalFrame : Transform.Frame patternWires common
      originalSourceWires originalTargetWires}
    {operation : Transform.Operation patternWires}
    {data : operation.Data originalFrame}
    {source : ItemSeq originalSourceWires} {result : Region common}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
        originalFrame.sourceKeep originalFrame.selected source result)
    (sites : ItemsSites operation data evidence)
    {boundary : List Sig}
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external common)
    (resultCanonical : (context.fill result).Canonical)
    (resultExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill result)) :
    ∃ retained : List Sig,
      ∃ formalSource : ItemSeq
          (common ++ (.rel pattern.external :: retained)),
        let pending : Region common :=
          .mk (.rel pattern.external :: retained)
            formalSource
        ∀ (polarity : Polarity)
          (_polarityEq : context.polarity = polarity)
          {endpoint : Region common}
          (pendingCanonical : (context.fill pending).Canonical)
          (pendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            interface.boundaryWire (context.fill pending))
          (endpointCanonical : (context.fill endpoint).Canonical)
          (endpointExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            interface.boundaryWire (context.fill endpoint))
          (_continuation : Telescope polarity interface context
            pending endpoint pendingCanonical pendingExternalTwoEnded
            endpointCanonical endpointExternalTwoEnded),
          Telescope.Compiles polarity
            (exactOccurrence interface context
              (polaritySource polarity result endpoint)
              (match polarity with
              | .positive => resultCanonical
              | .negative => endpointCanonical)
              (match polarity with
              | .positive => resultExternalTwoEnded
              | .negative => endpointExternalTwoEnded))
            resultCanonical resultExternalTwoEnded endpointCanonical
            endpointExternalTwoEnded := by
  let instantiatedEndpoint := interface.withBody (context.fill result)
    resultCanonical resultExternalTwoEnded
  let accumulatorOccurrence : Occurrence result instantiatedEndpoint :=
    exactOccurrence interface context result resultCanonical
      resultExternalTwoEnded
  obtain ⟨retained, positionalFormalSource, formalResult, formalEvidence,
      formalSites, formalCoherence, outputCanonical, outputExternalTwoEnded,
      strict⟩ :=
    accumulateAtomFormal body_eq evidence sites accumulatorOccurrence
  let recordedOutput := itemsEdit
    (operation := recordingOperation
      (Leaf.Formal.operation [] atomArguments) pattern.external)
    PUnit.unit formalEvidence formalSites
  let primitiveSites := recordingItemsSitesTarget formalSites
  let output := itemsEdit
    (operation := Leaf.Formal.operation [] atomArguments)
    PUnit.unit formalEvidence primitiveSites
  have primitiveNoPin : output.edit.NoSelectedPin := by
    exact itemsEdit_noSelectedPin primitiveSites
  have outputEndpointEq : recordedOutput.endpoint = output.endpoint :=
    recordingItemsEditEndpoint_eq formalSites
  have exactOutputEq : Region.adjoinAt retained .nil recordedOutput.endpoint =
      Region.adjoinAt retained .nil output.endpoint :=
    congrArg (Region.adjoinAt retained .nil) outputEndpointEq
  have primitiveOutputCanonical :
      (accumulatorOccurrence.context.fill
        (Region.adjoinAt retained .nil output.endpoint)).Canonical := by
    rw [← exactOutputEq]
    exact outputCanonical
  have primitiveOutputExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      accumulatorOccurrence.interface.boundaryWire
      (accumulatorOccurrence.context.fill
        (Region.adjoinAt retained .nil output.endpoint)) := by
    intro signature wire
    rw [← exactOutputEq]
    exact outputExternalTwoEnded wire
  have primitiveStrict : EqualityNormalization.StrictEquates
      accumulatorOccurrence (Region.adjoinAt retained .nil output.endpoint)
      primitiveOutputCanonical primitiveOutputExternalTwoEnded := by
    let endpointIso : OpenDiagramIso
        (accumulatorOccurrence.interface.withBody
          (accumulatorOccurrence.context.fill
            (Region.adjoinAt retained .nil recordedOutput.endpoint))
          outputCanonical outputExternalTwoEnded)
        (accumulatorOccurrence.interface.withBody
          (accumulatorOccurrence.context.fill
            (Region.adjoinAt retained .nil output.endpoint))
          primitiveOutputCanonical primitiveOutputExternalTwoEnded) :=
      OpenDiagram.withBody_iso outputCanonical primitiveOutputCanonical
        outputExternalTwoEnded primitiveOutputExternalTwoEnded
        (DiagramContext.fillIso accumulatorOccurrence.context
          (RegionIso.ofEq exactOutputEq))
    exact EqualityNormalization.StrictEquates.targetIso strict endpointIso
  let prepared := Region.adjoinAt retained .nil output.endpoint
  let positionalValues := positionalAtomSelection head ports
  let authoritativeValues := EqualityNormalization.formalPorts pattern.external
  let authoritativePending := argumentNormalizedRegion
    (common := common) (retained := retained) formalSites authoritativeValues
  let pending : Region common := authoritativePending
  refine ⟨retained, authoritativePending.items, ?_⟩
  dsimp only
  intro polarity polarityEq endpoint pendingCanonical
    pendingExternalTwoEnded endpointCanonical endpointExternalTwoEnded
    continuation
  let positionalPending : Region common :=
    .mk (.rel (positionalAtomWires atomArguments) :: retained)
      positionalFormalSource
  have authoritativeFilledCanonical :
      (context.fill authoritativePending).Canonical := by
    change (context.fill authoritativePending).Canonical at pendingCanonical
    exact pendingCanonical
  have authoritativeFilledExternal : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill authoritativePending) := by
    change OpenDiagram.ExternalTwoEnded interface.boundaryWire
      (context.fill authoritativePending) at pendingExternalTwoEnded
    exact pendingExternalTwoEnded
  have authoritativeLocalCanonical : authoritativePending.Canonical :=
    context.holeCanonical authoritativePending authoritativeFilledCanonical
  let authoritativeFrame : Transform.Frame pattern.external
      (common ++ retained)
      (common ++ (.rel pattern.external :: retained))
      (common ++ (.rel pattern.external :: retained)) :=
    Transform.Frame.replace common [] retained [.rel pattern.external]
      pattern.external
  have authoritativeInvariant :
      Transform.RetainedIndexInvariant authoritativeFrame :=
    Transform.RetainedIndexInvariant.replace _ _ _ _ _
  have authoritativePaths := argumentItemsEdit_selectedPaths formalSites
    authoritativeValues (normalizationOperation pattern.external)
    authoritativeFrame PUnit.unit (fun _ _ _ => PUnit.unit)
    authoritativeInvariant 0
  have formalInvariant : Transform.RetainedIndexInvariant
      (Leaf.Formal.rootFrame common [] retained [] atomArguments) := by
    exact Transform.RetainedIndexInvariant.replace _ _ _ _ _
  have formalPaths := formalSites.source_selectedPaths formalInvariant 0
  have selectedRooted : RegionPath.RootedTwo
      (positionalFormalSource.incidencePaths common.length 0) := by
    have authoritativeRoot := authoritativeLocalCanonical.1 (0 : Fin
      (.rel pattern.external :: retained).length)
    have pathEq : positionalFormalSource.incidencePaths common.length 0 =
        authoritativePending.items.incidencePaths common.length 0 := by
      calc
        positionalFormalSource.incidencePaths common.length 0 =
            formalSites.selectedPaths 0 := by
              simpa [Leaf.Formal.rootFrame, Transform.Frame.replace,
                Transform.Frame.insertedHead] using formalPaths
        _ = authoritativePending.items.incidencePaths common.length 0 := by
          symm
          simpa [authoritativePending, argumentNormalizedRegion,
            authoritativeFrame, Transform.Frame.replace,
            Transform.Frame.insertedHead] using authoritativePaths
    simpa only [pathEq] using authoritativeRoot
  have preparedLocalCanonical : prepared.Canonical :=
    context.holeCanonical prepared primitiveOutputCanonical
  let rawPrepared := Region.adjoinAt retained .nil output.edit.run
  have rawPreparedCanonical : rawPrepared.Canonical := by
    dsimp only [rawPrepared]
    rw [output.run_eq]
    exact preparedLocalCanonical
  have positionalLocalValidity := Leaf.Formal.target_source_validity
    output.edit primitiveNoPin rawPreparedCanonical selectedRooted
  have rawPreparedFilledCanonical : (context.fill rawPrepared).Canonical := by
    dsimp only [rawPrepared]
    rw [output.run_eq]
    exact primitiveOutputCanonical
  have positionalReplacement := context.replaceCanonical rawPrepared
    positionalPending rawPreparedFilledCanonical positionalLocalValidity.1 (by
      intro signature wire
      have paths := positionalLocalValidity.2 wire
      exact ⟨fun nonempty => by
          dsimp only [positionalPending]
          simp only [positionalAtomWires]
          rw [← paths]
          exact nonempty,
        fun nonempty => by
          dsimp only [positionalPending] at nonempty ⊢
          simp only [positionalAtomWires] at nonempty ⊢
          rw [paths]
          exact nonempty⟩)
  have positionalFilledCanonical :
      (context.fill positionalPending).Canonical := positionalReplacement.1
  have positionalFilledExternal : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill positionalPending) := by
    have rawPreparedFilledExternal : OpenDiagram.ExternalTwoEnded
        interface.boundaryWire (context.fill rawPrepared) := by
      dsimp only [rawPrepared]
      rw [output.run_eq]
      exact primitiveOutputExternalTwoEnded
    let preparedEndpoint := interface.withBody (context.fill rawPrepared)
      rawPreparedFilledCanonical rawPreparedFilledExternal
    intro signature wire
    exact preparedEndpoint.externalTwoEnded_of_nonempty_iff _
      positionalReplacement.2 wire
  have positionalEq : positionalPending =
      argumentNormalizedRegion (common := common) (retained := retained)
        formalSites positionalValues := by
    let positionalFrame : Transform.Frame
        (positionalAtomWires atomArguments) (common ++ retained)
        (common ++ (.rel (positionalAtomWires atomArguments) :: retained))
        (common ++ (.rel (positionalAtomWires atomArguments) :: retained)) :=
      { sourceKeep := Transform.Frame.keep common []
          [.rel (positionalAtomWires atomArguments)] retained
        targetKeep := Transform.Frame.keep common []
          [.rel (positionalAtomWires atomArguments)] retained
        selected := Transform.Frame.insertedHead common [] retained
          (.rel (positionalAtomWires atomArguments)) }
    have sourceIndependent := argumentItemsEdit_source_independent formalSites
      positionalValues
      (normalizationOperation (positionalAtomWires atomArguments))
      (Leaf.Formal.rootFrame common [] retained [] atomArguments)
      PUnit.unit (fun _ _ _ => PUnit.unit)
      (normalizationOperation (positionalAtomWires atomArguments))
      positionalFrame PUnit.unit (fun _ _ _ => PUnit.unit)
      (by
        intro wireSignature wire
        rfl)
      (by rfl)
    have normalizedCoherence : positionalFormalSource =
        (argumentItemsEdit formalSites positionalValues
          (normalizationOperation (positionalAtomWires atomArguments))
          positionalFrame PUnit.unit (fun _ _ _ => PUnit.unit)).1 :=
      formalCoherence.trans sourceIndependent
    exact congrArg
      (Region.mk (.rel (positionalAtomWires atomArguments) :: retained))
      normalizedCoherence
  have normalizationTelescope : Telescope polarity interface context
      positionalPending endpoint positionalFilledCanonical
      positionalFilledExternal endpointCanonical endpointExternalTwoEnded := by
    exact argumentNormalizationTelescopeAll formalSites positionalValues
      interface context positionalEq positionalFilledCanonical
      positionalFilledExternal authoritativeFilledCanonical
      authoritativeFilledExternal endpointCanonical endpointExternalTwoEnded
      polarity polarityEq (by
        simpa only [authoritativeValues, authoritativePending] using continuation)
  let request : Telescope.Request result positionalPending := {
    boundary := boundary
    source := interface.withBody
      (context.fill (polaritySource polarity result endpoint))
      (match polarity with
      | .positive => resultCanonical
      | .negative => endpointCanonical)
      (match polarity with
      | .positive => resultExternalTwoEnded
      | .negative => endpointExternalTwoEnded)
    endpoint := endpoint
    polarity := polarity
    occurrence := exactOccurrence interface context
      (polaritySource polarity result endpoint)
      (match polarity with
      | .positive => resultCanonical
      | .negative => endpointCanonical)
      (match polarity with
      | .positive => resultExternalTwoEnded
      | .negative => endpointExternalTwoEnded)
    instantiatedCanonical := resultCanonical
    instantiatedExternalTwoEnded := resultExternalTwoEnded
    pendingCanonical := positionalFilledCanonical
    pendingExternalTwoEnded := positionalFilledExternal
    endpointCanonical := endpointCanonical
    endpointExternalTwoEnded := endpointExternalTwoEnded
    continuation := normalizationTelescope
  }
  have equates := primitiveStrict.toEquates
  have preparationTelescope : Telescope polarity interface context result
      prepared resultCanonical resultExternalTwoEnded primitiveOutputCanonical
        primitiveOutputExternalTwoEnded := by
    cases polarity with
    | positive =>
        exact ⟨polarityEq, by
          simpa only [prepared, accumulatorOccurrence, exactOccurrence,
            instantiatedEndpoint] using equates.1⟩
    | negative =>
        exact ⟨polarityEq, by
          simpa only [prepared, accumulatorOccurrence, exactOccurrence,
            instantiatedEndpoint] using equates.2⟩
  let preparation : request.Preparation prepared := {
    prepared := prepared
    preparedCanonical := primitiveOutputCanonical
    preparedExternalTwoEnded := primitiveOutputExternalTwoEnded
    rawPreparedCanonical := primitiveOutputCanonical
    rawPreparedExternalTwoEnded := primitiveOutputExternalTwoEnded
    preparedIso := RegionIso.refl prepared
    telescope := by
      simpa only [request, exactOccurrence] using preparationTelescope
  }
  exact itemsFormal (before := []) (after := atomArguments)
    (localBefore := []) (localAfter := retained) formalEvidence primitiveSites
      request (by
        simpa only [prepared, output, positionalAtomWires] using
          preparation)

/-- The direct authoritative identity branch: accumulate every selected site
into one literal IdentityLeaf edit, prepare its deterministic endpoint, and
run the single directed primitive at the binder home. -/
theorem identityLeaf
    {patternWires common originalSourceWires originalTargetWires : List Sig}
    {signature : Sig} {arity : Nat}
    {pattern : OpenDiagram patternWires}
    {ports : Fin arity → Var pattern.external signature}
    {tail : ItemSeq pattern.external}
    (body_eq :
      pattern.body = Region.ofItems (.cons (.identity signature arity ports) tail))
    {originalFrame : Transform.Frame patternWires common
      originalSourceWires originalTargetWires}
    {operation : Transform.Operation patternWires}
    {data : operation.Data originalFrame}
    {source : ItemSeq originalSourceWires} {result : Region common}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        pattern
        originalFrame.sourceKeep originalFrame.selected source result)
    (sites : ItemsSites operation data evidence)
    {boundary : List Sig}
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external common)
    (resultCanonical : (context.fill result).Canonical)
    (resultExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill result)) :
    ∃ retained : List Sig,
      ∃ formalSource : ItemSeq
          (common ++ (.rel pattern.external :: retained)),
        let pending : Region common :=
          .mk (.rel pattern.external :: retained)
            formalSource
        ∀ (polarity : Polarity)
          (_polarityEq : context.polarity = polarity)
          {endpoint : Region common}
          (pendingCanonical : (context.fill pending).Canonical)
          (pendingExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            interface.boundaryWire (context.fill pending))
          (endpointCanonical : (context.fill endpoint).Canonical)
          (endpointExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            interface.boundaryWire (context.fill endpoint))
          (_continuation : Telescope polarity interface context
            pending endpoint pendingCanonical pendingExternalTwoEnded
            endpointCanonical endpointExternalTwoEnded),
          Telescope.Compiles polarity
            (exactOccurrence interface context
              (polaritySource polarity result endpoint)
              (match polarity with
              | .positive => resultCanonical
              | .negative => endpointCanonical)
              (match polarity with
              | .positive => resultExternalTwoEnded
              | .negative => endpointExternalTwoEnded))
            resultCanonical resultExternalTwoEnded endpointCanonical
            endpointExternalTwoEnded := by
  let instantiatedEndpoint := interface.withBody (context.fill result)
    resultCanonical resultExternalTwoEnded
  let accumulatorOccurrence : Occurrence result instantiatedEndpoint :=
    exactOccurrence interface context result resultCanonical
      resultExternalTwoEnded
  obtain ⟨retained, formalSource, formalResult, formalEvidence,
      formalSites, formalCoherence, outputCanonical, outputExternalTwoEnded,
      strict⟩ :=
    accumulateIdentity body_eq evidence sites accumulatorOccurrence
  let primitiveSites := recordingItemsSitesTarget formalSites
  let output := itemsEdit
    (operation := Leaf.Identity.operation signature arity)
    PUnit.unit formalEvidence primitiveSites
  have primitiveNoPin : output.edit.NoSelectedPin :=
    itemsEdit_noSelectedPin primitiveSites
  let prepared := Region.adjoinAt retained .nil output.endpoint
  let positionalValues := Leaf.Identity.Vars.fromFn ports
  let authoritativeValues := EqualityNormalization.formalPorts pattern.external
  let authoritativePending := argumentNormalizedRegion
    (common := common) (retained := retained) formalSites authoritativeValues
  let pending : Region common := authoritativePending
  refine ⟨retained, authoritativePending.items, ?_⟩
  dsimp only
  intro polarity polarityEq endpoint pendingCanonical
    pendingExternalTwoEnded endpointCanonical endpointExternalTwoEnded
    continuation
  let positionalPending : Region common :=
    .mk (.rel (List.replicate arity signature) :: retained) formalSource
  have authoritativeFilledCanonical :
      (context.fill authoritativePending).Canonical := by
    change (context.fill authoritativePending).Canonical at pendingCanonical
    exact pendingCanonical
  have authoritativeFilledExternal : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill authoritativePending) := by
    change OpenDiagram.ExternalTwoEnded interface.boundaryWire
      (context.fill authoritativePending) at pendingExternalTwoEnded
    exact pendingExternalTwoEnded
  have authoritativeLocalCanonical : authoritativePending.Canonical :=
    context.holeCanonical authoritativePending authoritativeFilledCanonical
  let authoritativeFrame : Transform.Frame pattern.external
      (common ++ retained)
      (common ++ (.rel pattern.external :: retained))
      (common ++ (.rel pattern.external :: retained)) :=
    Transform.Frame.replace common [] retained [.rel pattern.external]
      pattern.external
  have authoritativeInvariant :
      Transform.RetainedIndexInvariant authoritativeFrame :=
    Transform.RetainedIndexInvariant.replace _ _ _ _ _
  have authoritativePaths := argumentItemsEdit_selectedPaths formalSites
    authoritativeValues (normalizationOperation pattern.external)
    authoritativeFrame PUnit.unit (fun _ _ _ => PUnit.unit)
    authoritativeInvariant 0
  have formalInvariant : Transform.RetainedIndexInvariant
      (Leaf.Identity.rootFrame common [] retained signature arity) :=
    Transform.RetainedIndexInvariant.replace _ _ _ _ _
  have formalPaths := formalSites.source_selectedPaths formalInvariant 0
  have selectedRooted : RegionPath.RootedTwo
      (formalSource.incidencePaths common.length 0) := by
    have authoritativeRoot := authoritativeLocalCanonical.1 (0 : Fin
      (.rel pattern.external :: retained).length)
    have pathEq : formalSource.incidencePaths common.length 0 =
        authoritativePending.items.incidencePaths common.length 0 := by
      calc
        formalSource.incidencePaths common.length 0 =
            formalSites.selectedPaths 0 := by
          simpa [Leaf.Identity.rootFrame, Transform.Frame.replace,
            Transform.Frame.insertedHead] using formalPaths
        _ = authoritativePending.items.incidencePaths common.length 0 := by
          symm
          simpa [authoritativePending, argumentNormalizedRegion,
            authoritativeFrame, Transform.Frame.replace,
            Transform.Frame.insertedHead] using authoritativePaths
    simpa only [pathEq] using authoritativeRoot
  have preparedLocalCanonical : prepared.Canonical :=
    context.holeCanonical prepared outputCanonical
  let rawPrepared := Region.adjoinAt retained .nil output.edit.run
  have rawPreparedCanonical : rawPrepared.Canonical := by
    dsimp only [rawPrepared]
    rw [output.run_eq]
    exact preparedLocalCanonical
  have positionalLocalValidity := Leaf.Identity.target_source_validity
    output.edit primitiveNoPin rawPreparedCanonical selectedRooted
  have rawPreparedFilledCanonical : (context.fill rawPrepared).Canonical := by
    dsimp only [rawPrepared]
    rw [output.run_eq]
    exact outputCanonical
  have positionalReplacement := context.replaceCanonical rawPrepared
    positionalPending rawPreparedFilledCanonical positionalLocalValidity.1 (by
      intro wireSignature wire
      have paths := positionalLocalValidity.2 wire
      exact ⟨fun nonempty => by
          dsimp only [positionalPending]
          rw [← paths]
          exact nonempty,
        fun nonempty => by
          dsimp only [positionalPending] at nonempty ⊢
          rw [paths]
          exact nonempty⟩)
  have positionalFilledCanonical :
      (context.fill positionalPending).Canonical := positionalReplacement.1
  have positionalFilledExternal : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill positionalPending) := by
    have rawPreparedFilledExternal : OpenDiagram.ExternalTwoEnded
        interface.boundaryWire (context.fill rawPrepared) := by
      dsimp only [rawPrepared]
      rw [output.run_eq]
      exact outputExternalTwoEnded
    let preparedEndpoint := interface.withBody (context.fill rawPrepared)
      rawPreparedFilledCanonical rawPreparedFilledExternal
    intro wireSignature wire
    exact preparedEndpoint.externalTwoEnded_of_nonempty_iff _
      positionalReplacement.2 wire
  have positionalEq : positionalPending =
      argumentNormalizedRegion (common := common) (retained := retained)
        formalSites positionalValues := by
    let positionalFrame : Transform.Frame
        (List.replicate arity signature) (common ++ retained)
        (common ++ (.rel (List.replicate arity signature) :: retained))
        (common ++ (.rel (List.replicate arity signature) :: retained)) :=
      { sourceKeep := Transform.Frame.keep common []
          [.rel (List.replicate arity signature)] retained
        targetKeep := Transform.Frame.keep common []
          [.rel (List.replicate arity signature)] retained
        selected := Transform.Frame.insertedHead common [] retained
          (.rel (List.replicate arity signature)) }
    have sourceIndependent := argumentItemsEdit_source_independent formalSites
      positionalValues
      (normalizationOperation (List.replicate arity signature))
      (Leaf.Identity.rootFrame common [] retained signature arity)
      PUnit.unit (fun _ _ _ => PUnit.unit)
      (normalizationOperation (List.replicate arity signature))
      positionalFrame PUnit.unit (fun _ _ _ => PUnit.unit)
      (by intro wireSignature wire; rfl) (by rfl)
    have normalizedCoherence : formalSource =
        (argumentItemsEdit formalSites positionalValues
          (normalizationOperation (List.replicate arity signature))
          positionalFrame PUnit.unit (fun _ _ _ => PUnit.unit)).1 :=
      formalCoherence.trans sourceIndependent
    exact congrArg
      (Region.mk (.rel (List.replicate arity signature) :: retained))
      normalizedCoherence
  have normalizationTelescope : Telescope polarity interface context
      positionalPending endpoint positionalFilledCanonical
      positionalFilledExternal endpointCanonical endpointExternalTwoEnded := by
    exact argumentNormalizationTelescopeAll formalSites positionalValues
      interface context positionalEq positionalFilledCanonical
      positionalFilledExternal authoritativeFilledCanonical
      authoritativeFilledExternal endpointCanonical endpointExternalTwoEnded
      polarity polarityEq (by
        simpa only [authoritativeValues, authoritativePending] using continuation)
  let request : Telescope.Request result positionalPending := {
    boundary := boundary
    source := interface.withBody
      (context.fill (polaritySource polarity result endpoint))
      (match polarity with
      | .positive => resultCanonical
      | .negative => endpointCanonical)
      (match polarity with
      | .positive => resultExternalTwoEnded
      | .negative => endpointExternalTwoEnded)
    endpoint := endpoint
    polarity := polarity
    occurrence := exactOccurrence interface context
      (polaritySource polarity result endpoint)
      (match polarity with
      | .positive => resultCanonical
      | .negative => endpointCanonical)
      (match polarity with
      | .positive => resultExternalTwoEnded
      | .negative => endpointExternalTwoEnded)
    instantiatedCanonical := resultCanonical
    instantiatedExternalTwoEnded := resultExternalTwoEnded
    pendingCanonical := positionalFilledCanonical
    pendingExternalTwoEnded := positionalFilledExternal
    endpointCanonical := endpointCanonical
    endpointExternalTwoEnded := endpointExternalTwoEnded
    continuation := normalizationTelescope
  }
  have equates := strict.toEquates
  have preparationTelescope : Telescope polarity interface context result
      prepared resultCanonical resultExternalTwoEnded outputCanonical
        outputExternalTwoEnded := by
    cases polarity with
    | positive =>
        exact ⟨polarityEq, by
          simpa only [prepared, accumulatorOccurrence, exactOccurrence,
            instantiatedEndpoint] using equates.1⟩
    | negative =>
        exact ⟨polarityEq, by
          simpa only [prepared, accumulatorOccurrence, exactOccurrence,
            instantiatedEndpoint] using equates.2⟩
  let preparation : request.Preparation prepared := {
    prepared := prepared
    preparedCanonical := outputCanonical
    preparedExternalTwoEnded := outputExternalTwoEnded
    rawPreparedCanonical := outputCanonical
    rawPreparedExternalTwoEnded := outputExternalTwoEnded
    preparedIso := RegionIso.refl prepared
    telescope := by
      simpa only [request, exactOccurrence] using preparationTelescope
  }
  exact itemsIdentity (signature := signature) (arity := arity)
    (localBefore := []) (localAfter := retained) formalEvidence primitiveSites
      request (by
        simpa only [prepared, output, positionalPending] using preparation)


end VisualProof.Rule.Completeness.Comprehension
