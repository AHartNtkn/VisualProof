import VisualProof.Rule.Completeness.Comprehension.Structural.Hosted

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

def TargetRegion
    {targetArguments targetExternal common sourceWires targetWires originalArguments
      originalSourceWires originalTargetWires : List Sig}
    {targetPattern : OpenDiagram targetArguments}
    {targetOperation : Transform.Operation targetArguments}
    {pattern : OpenDiagram originalArguments}
    {originalFrame : Transform.Frame originalArguments common
      originalSourceWires originalTargetWires}
    {operation : Transform.Operation originalArguments}
    {data : operation.Data originalFrame}
    {source : Region originalSourceWires} {result : Region common}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult pattern
        originalFrame.sourceKeep originalFrame.selected source result)
    (_sites : RegionSites operation data evidence)
    (targetValues : Vars targetExternal targetArguments)
    (targetFrame : Transform.Frame targetArguments
      common sourceWires targetWires)
    (targetData : targetOperation.Data targetFrame)
    (K : ∀ (formalSource : Region sourceWires)
        (formalResult : Region common)
        (formalEvidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
            targetPattern targetFrame.sourceKeep targetFrame.selected
            formalSource formalResult)
        (formalSites : RegionSites
          (recordingOperation targetOperation targetExternal) targetData
          formalEvidence),
        formalSource =
          (argumentRegionEdit formalSites targetValues
            (normalizationOperation targetArguments) targetFrame
            PUnit.unit (fun _ _ _ => PUnit.unit)).1 → Prop) : Prop :=
  ∃ formalSource : Region sourceWires,
    ∃ formalResult : Region common,
      ∃ formalEvidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
            targetPattern targetFrame.sourceKeep targetFrame.selected
            formalSource formalResult,
        ∃ formalSites : RegionSites
            (recordingOperation targetOperation targetExternal) targetData
            formalEvidence,
          ∃ coherence : formalSource =
              (argumentRegionEdit formalSites targetValues
                (normalizationOperation targetArguments) targetFrame
                PUnit.unit (fun _ _ _ => PUnit.unit)).1,
            K formalSource formalResult formalEvidence formalSites coherence

def TargetItems
    {targetArguments targetExternal common sourceWires targetWires originalArguments
      originalSourceWires originalTargetWires : List Sig}
    {targetPattern : OpenDiagram targetArguments}
    {targetOperation : Transform.Operation targetArguments}
    {pattern : OpenDiagram originalArguments}
    {originalFrame : Transform.Frame originalArguments common
      originalSourceWires originalTargetWires}
    {operation : Transform.Operation originalArguments}
    {data : operation.Data originalFrame}
    {source : ItemSeq originalSourceWires} {result : Region common}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
        originalFrame.sourceKeep originalFrame.selected source result)
    (_sites : ItemsSites operation data evidence)
    (targetValues : Vars targetExternal targetArguments)
    (targetFrame : Transform.Frame targetArguments
      common sourceWires targetWires)
    (targetData : targetOperation.Data targetFrame)
    (K : ∀ (retained : List Sig)
        (formalSource : ItemSeq (sourceWires ++ retained))
        (formalResult : Region (common ++ retained))
        (formalEvidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            targetPattern (targetFrame.append retained).sourceKeep
            (targetFrame.append retained).selected formalSource formalResult)
        (formalSites : ItemsSites
          (recordingOperation targetOperation targetExternal)
          (targetOperation.appendData targetFrame targetData retained)
          formalEvidence),
        formalSource =
          (argumentItemsEdit formalSites targetValues
            (normalizationOperation targetArguments)
            (targetFrame.append retained) PUnit.unit
            (fun _ _ _ => PUnit.unit)).1 → Prop) : Prop :=
  ∃ retained : List Sig,
    ∃ formalSource : ItemSeq (sourceWires ++ retained),
      ∃ formalResult : Region (common ++ retained),
        ∃ formalEvidence :
            _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
              targetPattern
              (targetFrame.append retained).sourceKeep
              (targetFrame.append retained).selected
              formalSource formalResult,
          ∃ formalSites : ItemsSites
              (recordingOperation targetOperation targetExternal)
              (targetOperation.appendData targetFrame targetData retained)
              formalEvidence,
            ∃ coherence : formalSource =
                (argumentItemsEdit formalSites targetValues
                  (normalizationOperation targetArguments)
                  (targetFrame.append retained) PUnit.unit
                  (fun _ _ _ => PUnit.unit)).1,
              K retained formalSource formalResult formalEvidence formalSites
                coherence

def TargetItem
    {targetArguments targetExternal common sourceWires targetWires originalArguments
      originalSourceWires originalTargetWires : List Sig}
    {targetPattern : OpenDiagram targetArguments}
    {targetOperation : Transform.Operation targetArguments}
    {pattern : OpenDiagram originalArguments}
    {originalFrame : Transform.Frame originalArguments common
      originalSourceWires originalTargetWires}
    {operation : Transform.Operation originalArguments}
    {data : operation.Data originalFrame}
    {source : Item originalSourceWires} {result : Region common}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult pattern
        originalFrame.sourceKeep originalFrame.selected source result)
    (_sites : ItemSites operation data evidence)
    (targetValues : Vars targetExternal targetArguments)
    (targetFrame : Transform.Frame targetArguments
      common sourceWires targetWires)
    (targetData : targetOperation.Data targetFrame)
    (K : ∀ (retained : List Sig)
        (formalSource : ItemSeq (sourceWires ++ retained))
        (formalResult : Region (common ++ retained))
        (formalEvidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            targetPattern (targetFrame.append retained).sourceKeep
            (targetFrame.append retained).selected formalSource formalResult)
        (formalSites : ItemsSites
          (recordingOperation targetOperation targetExternal)
          (targetOperation.appendData targetFrame targetData retained)
          formalEvidence),
        formalSource =
          (argumentItemsEdit formalSites targetValues
            (normalizationOperation targetArguments)
            (targetFrame.append retained) PUnit.unit
            (fun _ _ _ => PUnit.unit)).1 → Prop) : Prop :=
  ∃ retained : List Sig,
    ∃ formalSource : ItemSeq (sourceWires ++ retained),
      ∃ formalResult : Region (common ++ retained),
        ∃ formalEvidence :
            _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
              targetPattern
              (targetFrame.append retained).sourceKeep
              (targetFrame.append retained).selected
              formalSource formalResult,
          ∃ formalSites : ItemsSites
              (recordingOperation targetOperation targetExternal)
              (targetOperation.appendData targetFrame targetData retained)
              formalEvidence,
            ∃ coherence : formalSource =
                (argumentItemsEdit formalSites targetValues
                  (normalizationOperation targetArguments)
                  (targetFrame.append retained) PUnit.unit
                  (fun _ _ _ => PUnit.unit)).1,
              K retained formalSource formalResult formalEvidence formalSites
                coherence

/-- The singleton-atom selected-site premise consumed by the shared target
fold. It is nonrecursive: all recursive traversal remains owned by the existing
Instantiation/Sites induction. -/
theorem atomSelectedTargetItem
    {patternWires atomArguments itemCommon itemSourceWires itemTargetWires
      formalSourceWires formalTargetWires : List Sig}
    {pattern : OpenDiagram patternWires}
    {head : Var pattern.external (.rel atomArguments)}
    {ports : Vars pattern.external atomArguments}
    {tail : ItemSeq pattern.external}
    (body_eq :
      pattern.body = Region.ofItems (.cons (.atom head ports) tail))
    {itemFrame : Transform.Frame patternWires itemCommon
      itemSourceWires itemTargetWires}
    {itemOperation : Transform.Operation patternWires}
    {itemData : itemOperation.Data itemFrame}
    (application : Vars itemCommon patternWires)
    (siteData : itemOperation.SiteData itemFrame itemData application)
    (formalFrame : Transform.Frame (positionalAtomWires atomArguments)
      itemCommon formalSourceWires formalTargetWires) :
    TargetItem
      (targetPattern := positionalAtomPattern atomArguments)
      (targetOperation := Leaf.Formal.operation [] atomArguments)
      (_root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
        (pattern := pattern) (retain := itemFrame.sourceKeep)
        (selected := itemFrame.selected) application)
      (ItemSites.selectedAtom (operation := itemOperation)
        (pattern := pattern) (frame := itemFrame) application siteData)
      (positionalAtomSelection head ports) formalFrame PUnit.unit
      (fun retained _formalSource formalResult formalEvidence formalSites
          _coherence =>
        ∃ staged : Region itemCommon,
          HostedStrict
              (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
                pattern application) staged ∧
            ScopePreservation
                (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
                  pattern application) staged ∧
              Nonempty (RegionIso (WireEquiv.refl itemCommon) staged
                (Region.adjoinAt retained .nil formalResult))) := by
      unfold TargetItem
      let retainedLocals := EqualityNormalization.locals pattern
      let childFrame := formalFrame.append retainedLocals
      let hostItems := atomSiteHostItems pattern tail application
      let formal : Var (itemCommon ++ retainedLocals)
          (.rel atomArguments) := atomBodyWire pattern itemCommon head
      let retainedPorts : Vars (itemCommon ++ retainedLocals)
          atomArguments :=
        ports.map fun wire => atomBodyWire pattern itemCommon wire
      let formalSource := atomFormalPrefixSource childFrame hostItems formal
        retainedPorts
      let formalResult := atomFormalPrefixResult hostItems formal retainedPorts
      let formalEvidence := atomFormalPrefixEvidence childFrame hostItems formal
        retainedPorts
      let childApplication : Vars (itemCommon ++ retainedLocals)
          pattern.external :=
        (Erasure.Exposure.identityBoundary pattern.external).map
          (fun wire => atomBodyWire pattern itemCommon wire)
      let formalSites := atomFormalPrefixRecordingSites childFrame hostItems
        formal retainedPorts childApplication
      refine ⟨retainedLocals, formalSource, formalResult, formalEvidence,
        formalSites, ?_, ?_⟩
      · let rename := atomBodyWire pattern itemCommon
        apply atomFormalPrefixSource_eq_argumentItemsEdit childFrame
          hostItems formal retainedPorts childApplication
          (positionalAtomSelection head ports) rename
        · rfl
        · rfl
      let staged := Region.adjoinAt retainedLocals .nil formalResult
      have hosted : HostedStrict
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern application) staged := by
        intro outer hostLocals rename outerHostItems boundary source
          hostedOccurrence targetCanonical targetExternalTwoEnded
        let mappedApplication := application.map fun wire => rename wire
        let sourceBefore :=
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern application).renameWires rename
        let sourceAfter :=
          _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern mappedApplication
        let sourceHostBefore := Region.adjoinAt hostLocals outerHostItems
          sourceBefore
        let sourceHostAfter := Region.adjoinAt hostLocals outerHostItems
          sourceAfter
        change Occurrence sourceHostBefore source at hostedOccurrence
        have sourceHostEq : sourceHostBefore = sourceHostAfter := by
          simp only [sourceHostBefore, sourceHostAfter, sourceBefore,
            sourceAfter, mappedApplication,
            EqualityNormalization.instantiate_renameWires]
        have sourceAfterCanonical : sourceHostAfter.Canonical := by
          rw [← sourceHostEq]
          exact hostedOccurrence.context.holeCanonical _
            hostedOccurrence.sourceCanonical
        have sourceNonempty : ∀ {signature} (wire : Var outer signature),
            sourceHostBefore.incidencePaths wire.index.val ≠ [] ↔
              sourceHostAfter.incidencePaths wire.index.val ≠ [] := by
          intro signature wire
          rw [sourceHostEq]
        let presentedOccurrence : Occurrence sourceHostAfter source :=
          EqualityNormalization.presentationOccurrence hostedOccurrence
            sourceAfterCanonical sourceNonempty
            (RegionIso.adjoinAt hostLocals outerHostItems
              (EqualityNormalization.instantiateRenameIso pattern
                application rename))
        let mappedHostItems := atomSiteHostItems pattern tail
          mappedApplication
        let mappedFormal : Var
            ((outer ++ hostLocals) ++ retainedLocals)
            (.rel atomArguments) :=
          atomBodyWire pattern (outer ++ hostLocals) head
        let mappedRetainedPorts : Vars
            ((outer ++ hostLocals) ++ retainedLocals) atomArguments :=
          ports.map fun wire =>
            atomBodyWire pattern (outer ++ hostLocals) wire
        let mappedFormalResult := atomFormalPrefixResult mappedHostItems
          mappedFormal mappedRetainedPorts
        let targetAfter := Region.adjoinAt hostLocals outerHostItems
          (Region.adjoinAt retainedLocals .nil mappedFormalResult)
        obtain ⟨ownedCanonical, ownedExternalTwoEnded, ownedStrict,
            outputCanonical, outputExternalTwoEnded, outputStrict⟩ :=
          accumulateSelectedAtomFormal body_eq outerHostItems
            mappedApplication presentedOccurrence
        change EqualityNormalization.StrictEquates presentedOccurrence
          targetAfter ownedCanonical ownedExternalTwoEnded at ownedStrict
        let retainedRename :=
          rename.appendRight (EqualityNormalization.locals pattern)
        have hostItemsEq : hostItems.renameWires retainedRename =
            mappedHostItems := by
          simpa only [hostItems, mappedHostItems, mappedApplication,
            retainedLocals, retainedRename] using
            atomSiteHostItems_renameWires pattern tail application rename
        have formalEq : retainedRename formal = mappedFormal := by
          have natural := congrArg
            (fun embedding : WireRenaming pattern.external
                ((outer ++ hostLocals) ++
                  EqualityNormalization.locals pattern) =>
              embedding head)
            (atomBodyWire_natural pattern rename)
          simpa only [formal, mappedFormal, retainedLocals, retainedRename,
            WireRenaming.comp] using natural
        have retainedPortsEq :
            retainedPorts.map (fun wire => retainedRename wire) =
              mappedRetainedPorts := by
          calc
            _ = ports.map (fun wire =>
                retainedRename (atomBodyWire pattern itemCommon wire)) :=
              Diagram.vars_map_comp ports (atomBodyWire pattern itemCommon)
                retainedRename
            _ = ports.map (fun wire =>
                atomBodyWire pattern (outer ++ hostLocals) wire) := by
              simpa only [WireRenaming.comp] using congrArg
                (fun embedding : WireRenaming pattern.external
                    ((outer ++ hostLocals) ++
                      EqualityNormalization.locals pattern) =>
                  ports.map fun wire => embedding wire)
                (atomBodyWire_natural pattern rename)
            _ = mappedRetainedPorts := rfl
        have formalResultEq : formalResult.renameWires retainedRename =
            mappedFormalResult := by
          calc
            _ = atomFormalPrefixResult
                (hostItems.renameWires retainedRename)
                (retainedRename formal)
                (retainedPorts.map fun wire => retainedRename wire) :=
              atomFormalPrefixResult_renameWires hostItems formal
                retainedPorts retainedRename
            _ = mappedFormalResult := by
              rw [hostItemsEq, formalEq, retainedPortsEq]
        let targetBefore := Region.adjoinAt hostLocals outerHostItems
          (staged.renameWires rename)
        have targetEq : targetBefore = targetAfter := by
          simp only [targetBefore, targetAfter, staged,
            Region.renameWires_adjoinAt_nil, retainedLocals]
          rw [formalResultEq]
        let targetPresentation : RegionIso (WireEquiv.refl outer)
            targetAfter targetBefore := RegionIso.ofEq targetEq.symm
        have presentedTargetCanonical :
            (presentedOccurrence.context.fill targetBefore).Canonical := by
          exact targetCanonical
        have presentedTargetExternalTwoEnded :
            OpenDiagram.ExternalTwoEnded
              presentedOccurrence.interface.boundaryWire
              (presentedOccurrence.context.fill targetBefore) := by
          intro signature wire
          exact targetExternalTwoEnded wire
        let ownedTargetIso : OpenDiagramIso
            (presentedOccurrence.interface.withBody
              (presentedOccurrence.context.fill targetAfter)
              ownedCanonical ownedExternalTwoEnded)
            (presentedOccurrence.interface.withBody
              (presentedOccurrence.context.fill targetBefore)
              presentedTargetCanonical presentedTargetExternalTwoEnded) :=
          OpenDiagram.withBody_iso ownedCanonical presentedTargetCanonical
            ownedExternalTwoEnded presentedTargetExternalTwoEnded
            (DiagramContext.fillIso presentedOccurrence.context
              targetPresentation)
        have presentedStrict : EqualityNormalization.StrictEquates
            presentedOccurrence targetBefore presentedTargetCanonical
              presentedTargetExternalTwoEnded := by
          exact EqualityNormalization.StrictEquates.targetIso ownedStrict
            ownedTargetIso
        let targetIso : OpenDiagramIso
            (presentedOccurrence.interface.withBody
              (presentedOccurrence.context.fill targetBefore)
              presentedTargetCanonical presentedTargetExternalTwoEnded)
            (hostedOccurrence.interface.withBody
              (hostedOccurrence.context.fill targetBefore)
              targetCanonical targetExternalTwoEnded) :=
          OpenDiagram.withBody_iso presentedTargetCanonical targetCanonical
            presentedTargetExternalTwoEnded targetExternalTwoEnded
            (RegionIso.refl
              (presentedOccurrence.context.fill targetBefore))
        exact ⟨transGen_iso (OpenDiagramIso.refl source)
            presentedStrict.1 targetIso,
          transGen_iso targetIso presentedStrict.2
            (OpenDiagramIso.refl source)⟩
      /- The deterministic edit endpoint is deliberately outside the semantic
      accumulator; leaf consumers prepare it at the primitive boundary.
      let outputStaged := Region.adjoinAt retainedLocals .nil
        (output.endpoint.renameWires (targetRename.appendRight retainedLocals))
      have outputHosted : HostedStrict
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern application) outputStaged := by
        intro outer hostLocals rename outerHostItems boundary source
          hostedOccurrence targetCanonical targetExternalTwoEnded
        let mappedApplication := application.map fun wire => rename wire
        let sourceBefore :=
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern application).renameWires rename
        let sourceAfter :=
          _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern mappedApplication
        let sourceHostBefore := Region.adjoinAt hostLocals outerHostItems
          sourceBefore
        let sourceHostAfter := Region.adjoinAt hostLocals outerHostItems
          sourceAfter
        change Occurrence sourceHostBefore source at hostedOccurrence
        have sourceHostEq : sourceHostBefore = sourceHostAfter := by
          simp only [sourceHostBefore, sourceHostAfter, sourceBefore,
            sourceAfter, mappedApplication,
            EqualityNormalization.instantiate_renameWires]
        have sourceAfterCanonical : sourceHostAfter.Canonical := by
          rw [← sourceHostEq]
          exact hostedOccurrence.context.holeCanonical _
            hostedOccurrence.sourceCanonical
        have sourceNonempty : ∀ {signature} (wire : Var outer signature),
            sourceHostBefore.incidencePaths wire.index.val ≠ [] ↔
              sourceHostAfter.incidencePaths wire.index.val ≠ [] := by
          intro signature wire
          rw [sourceHostEq]
        let presentedOccurrence : Occurrence sourceHostAfter source :=
          EqualityNormalization.presentationOccurrence hostedOccurrence
            sourceAfterCanonical sourceNonempty
            (RegionIso.adjoinAt hostLocals outerHostItems
              (EqualityNormalization.instantiateRenameIso pattern
                application rename))
        let mappedHostItems := atomSiteHostItems pattern tail
          mappedApplication
        let mappedFormal : Var
            ((outer ++ hostLocals) ++ retainedLocals)
            (.rel atomArguments) :=
          atomBodyWire pattern (outer ++ hostLocals) head
        let mappedRetainedPorts : Vars
            ((outer ++ hostLocals) ++ retainedLocals) atomArguments :=
          ports.map fun wire =>
            atomBodyWire pattern (outer ++ hostLocals) wire
        let mappedFormalResult := atomFormalPrefixResult mappedHostItems
          mappedFormal mappedRetainedPorts
        let mappedFrame := Leaf.Formal.rootFrame (outer ++ hostLocals) []
          retainedLocals [] atomArguments
        let mappedEvidence := atomFormalPrefixEvidence mappedFrame
          mappedHostItems mappedFormal mappedRetainedPorts
        let mappedExternalApplication : Vars
            ((outer ++ hostLocals) ++ retainedLocals) pattern.external :=
          (Erasure.Exposure.identityBoundary pattern.external).map
            (fun wire => atomBodyWire pattern (outer ++ hostLocals) wire)
        let mappedSites := atomFormalPrefixRecordingSites mappedFrame
          mappedHostItems mappedFormal mappedRetainedPorts
          mappedExternalApplication
        let mappedOutput := itemsEdit
          (operation := recordingOperation
            (Leaf.Formal.operation [] atomArguments) pattern.external)
          PUnit.unit mappedEvidence mappedSites
        have mappedTargetIdentity : mappedFrame.targetKeep =
            WireRenaming.id := by
          exact formalRootFrame_targetKeep (outer ++ hostLocals)
            retainedLocals atomArguments
        have mappedOutputEq : mappedOutput.endpoint =
            atomFormalPrefixEndpoint mappedHostItems mappedFormal
              mappedRetainedPorts := by
          have endpoint := atomFormalPrefixRecordingItemsEditEndpoint atomArguments
            pattern.external mappedFrame mappedHostItems mappedFormal
              mappedRetainedPorts mappedExternalApplication
          rw [mappedTargetIdentity] at endpoint
          exact endpoint.trans (Region.renameWires_id _)
        let targetMiddle := Region.adjoinAt hostLocals outerHostItems
          (Region.adjoinAt retainedLocals .nil mappedFormalResult)
        let targetAfter := Region.adjoinAt hostLocals outerHostItems
          (Region.adjoinAt retainedLocals .nil mappedOutput.endpoint)
        let primitiveSites := atomFormalPrefixSites mappedFrame mappedHostItems
          mappedFormal mappedRetainedPorts
        let primitiveOutput := itemsEdit
          (operation := Leaf.Formal.operation [] atomArguments)
          PUnit.unit mappedEvidence primitiveSites
        let primitiveTargetAfter := Region.adjoinAt hostLocals outerHostItems
          (Region.adjoinAt retainedLocals .nil primitiveOutput.endpoint)
        have primitiveOutputEq : primitiveOutput.endpoint =
            atomFormalPrefixEndpoint mappedHostItems mappedFormal
              mappedRetainedPorts := by
          have endpoint := atomFormalPrefixItemsEditEndpoint atomArguments
            mappedFrame mappedHostItems mappedFormal mappedRetainedPorts
          rw [mappedTargetIdentity] at endpoint
          exact endpoint.trans (Region.renameWires_id _)
        have targetAfterEq : targetAfter = primitiveTargetAfter := by
          unfold targetAfter primitiveTargetAfter
          rw [mappedOutputEq, primitiveOutputEq]
        obtain ⟨ownedCanonical, ownedExternalTwoEnded, ownedStrict,
            outputCanonical, outputExternalTwoEnded, outputStrict⟩ :=
          accumulateSelectedAtomFormal body_eq outerHostItems
            mappedApplication presentedOccurrence
        change EqualityNormalization.StrictEquates presentedOccurrence
          targetMiddle ownedCanonical ownedExternalTwoEnded at ownedStrict
        have targetAfterCanonical :
            (presentedOccurrence.context.fill targetAfter).Canonical := by
          rw [targetAfterEq]
          exact outputCanonical
        have targetAfterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            presentedOccurrence.interface.boundaryWire
            (presentedOccurrence.context.fill targetAfter) := by
          intro signature wire
          rw [targetAfterEq]
          exact outputExternalTwoEnded wire
        have outputStrictRecorded : EqualityNormalization.StrictEquates
          (exactOccurrence presentedOccurrence.interface
            presentedOccurrence.context targetMiddle ownedCanonical
              ownedExternalTwoEnded)
          targetAfter targetAfterCanonical targetAfterExternalTwoEnded := by
          let targetIso : OpenDiagramIso
              (presentedOccurrence.interface.withBody
                (presentedOccurrence.context.fill primitiveTargetAfter)
                outputCanonical outputExternalTwoEnded)
              (presentedOccurrence.interface.withBody
                (presentedOccurrence.context.fill targetAfter)
                targetAfterCanonical targetAfterExternalTwoEnded) :=
            OpenDiagram.withBody_iso outputCanonical targetAfterCanonical
              outputExternalTwoEnded targetAfterExternalTwoEnded
              (DiagramContext.fillIso presentedOccurrence.context
                (RegionIso.ofEq targetAfterEq.symm))
          exact EqualityNormalization.StrictEquates.targetIso outputStrict
            targetIso
        have combinedStrict : EqualityNormalization.StrictEquates
            presentedOccurrence targetAfter targetAfterCanonical
              targetAfterExternalTwoEnded :=
          EqualityNormalization.StrictEquates.trans ownedStrict
            outputStrictRecorded
        let retainedRename :=
          rename.appendRight (EqualityNormalization.locals pattern)
        have hostItemsEq : hostItems.renameWires retainedRename =
            mappedHostItems := by
          simpa only [hostItems, mappedHostItems, mappedApplication,
            retainedLocals, retainedRename] using
            atomSiteHostItems_renameWires pattern tail application rename
        have formalEq : retainedRename formal = mappedFormal := by
          have natural := congrArg
            (fun embedding : WireRenaming pattern.external
                ((outer ++ hostLocals) ++
                  EqualityNormalization.locals pattern) =>
              embedding head)
            (atomBodyWire_natural pattern rename)
          simpa only [formal, mappedFormal, retainedLocals, retainedRename,
            WireRenaming.comp] using natural
        have retainedPortsEq :
            retainedPorts.map (fun wire => retainedRename wire) =
              mappedRetainedPorts := by
          calc
            _ = ports.map (fun wire =>
                retainedRename (atomBodyWire pattern itemCommon wire)) :=
              Diagram.vars_map_comp ports (atomBodyWire pattern itemCommon)
                retainedRename
            _ = ports.map (fun wire =>
                atomBodyWire pattern (outer ++ hostLocals) wire) := by
              simpa only [WireRenaming.comp] using congrArg
                (fun embedding : WireRenaming pattern.external
                    ((outer ++ hostLocals) ++
                      EqualityNormalization.locals pattern) =>
                  ports.map fun wire => embedding wire)
                (atomBodyWire_natural pattern rename)
            _ = mappedRetainedPorts := rfl
        have endpointEq :
            (output.endpoint.renameWires
              (targetRename.appendRight retainedLocals)).renameWires
                retainedRename = mappedOutput.endpoint := by
          calc
            _ = Region.renameWires retainedRename
                (atomFormalPrefixEndpoint hostItems formal retainedPorts) :=
              congrArg
                  (fun region => region.renameWires retainedRename) outputEq
            _ = atomFormalPrefixEndpoint
                (hostItems.renameWires retainedRename)
                (retainedRename formal)
                (retainedPorts.map fun wire => retainedRename wire) :=
              atomFormalPrefixEndpoint_renameWires hostItems formal
                retainedPorts retainedRename
            _ = atomFormalPrefixEndpoint mappedHostItems mappedFormal
                mappedRetainedPorts := by
              rw [hostItemsEq, formalEq, retainedPortsEq]
            _ = mappedOutput.endpoint := mappedOutputEq.symm
        let targetBefore := Region.adjoinAt hostLocals outerHostItems
          (outputStaged.renameWires rename)
        have targetEq : targetBefore = targetAfter := by
          simp only [targetBefore, targetAfter, outputStaged,
            Region.renameWires_adjoinAt_nil, retainedLocals]
          rw [endpointEq]
        let targetPresentation : RegionIso (WireEquiv.refl outer)
            targetAfter targetBefore := RegionIso.ofEq targetEq.symm
        have presentedTargetCanonical :
            (presentedOccurrence.context.fill targetBefore).Canonical := by
          exact targetCanonical
        have presentedTargetExternalTwoEnded :
            OpenDiagram.ExternalTwoEnded
              presentedOccurrence.interface.boundaryWire
              (presentedOccurrence.context.fill targetBefore) := by
          intro signature wire
          exact targetExternalTwoEnded wire
        let combinedTargetIso : OpenDiagramIso
            (presentedOccurrence.interface.withBody
              (presentedOccurrence.context.fill targetAfter)
              targetAfterCanonical targetAfterExternalTwoEnded)
            (presentedOccurrence.interface.withBody
              (presentedOccurrence.context.fill targetBefore)
              presentedTargetCanonical presentedTargetExternalTwoEnded) :=
          OpenDiagram.withBody_iso targetAfterCanonical presentedTargetCanonical
            targetAfterExternalTwoEnded presentedTargetExternalTwoEnded
            (DiagramContext.fillIso presentedOccurrence.context
              targetPresentation)
        have presentedStrict : EqualityNormalization.StrictEquates
            presentedOccurrence targetBefore presentedTargetCanonical
              presentedTargetExternalTwoEnded := by
          exact EqualityNormalization.StrictEquates.targetIso combinedStrict
            combinedTargetIso
        let targetIso : OpenDiagramIso
            (presentedOccurrence.interface.withBody
              (presentedOccurrence.context.fill targetBefore)
              presentedTargetCanonical presentedTargetExternalTwoEnded)
            (hostedOccurrence.interface.withBody
              (hostedOccurrence.context.fill targetBefore)
              targetCanonical targetExternalTwoEnded) :=
          OpenDiagram.withBody_iso presentedTargetCanonical targetCanonical
            presentedTargetExternalTwoEnded targetExternalTwoEnded
            (RegionIso.refl
              (presentedOccurrence.context.fill targetBefore))
        exact ⟨transGen_iso (OpenDiagramIso.refl source)
            presentedStrict.1 targetIso,
          transGen_iso targetIso presentedStrict.2
            (OpenDiagramIso.refl source)⟩
      -/
      let direct : Region (itemCommon ++ retainedLocals) :=
        Region.singleton (.atom formal retainedPorts)
      let positional : Region (itemCommon ++ retainedLocals) :=
        _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalAtomPattern atomArguments) (.cons formal retainedPorts)
      let raw := atomExposureDescription (head := head) (ports := ports)
        tail application
      have rawSourceEq : raw.source =
          Region.adjoinAt retainedLocals hostItems direct := by
        simp only [raw, Rule.Erasure.Description.source, Region.spliceAt,
          atomExposureDescription, retainedLocals, hostItems, direct]
        exact congrArg
          (fun material => Region.adjoinAt retainedLocals hostItems material)
          (by
            simpa only [atomExposureDescription, formal, retainedPorts] using
              atomExposureMaterialRename tail application)
      let rawSourceIso := atomExposureSourceIso body_eq application
      let directSourceIso : RegionIso (WireEquiv.refl itemCommon)
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern application)
          (Region.adjoinAt retainedLocals hostItems direct) :=
        rawSourceIso.symm.trans (RegionIso.ofEq rawSourceEq)
      have exposureScope : ScopePreservation
          (Region.adjoinAt retainedLocals hostItems direct)
          (Region.adjoinAt retainedLocals hostItems positional) :=
        adjoinAt_preserves_scope retainedLocals hostItems direct positional
          (positionalAtomInstantiation_scope formal retainedPorts)
      let formalIso := atomFormalSelectedResultIso
        (pattern := pattern) (head := head) (ports := ports) tail application
      have selectedScope : ScopePreservation
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern application) staged := by
        exact ScopePreservation.trans (ScopePreservation.ofIso directSourceIso)
          (ScopePreservation.trans exposureScope (ScopePreservation.ofIso formalIso.symm))
      /-
      let outputEndpointIso : RegionIso
          (WireEquiv.refl (itemCommon ++ retainedLocals))
          (output.endpoint.renameWires
            (targetRename.appendRight retainedLocals))
          ((Region.ofItems hostItems).conjoin direct) :=
        (RegionIso.ofEq outputEq).trans
          (atomFormalPrefixEndpointIso hostItems formal retainedPorts)
      let outputLocalIso : RegionIso (WireEquiv.refl itemCommon)
          outputStaged
          (Region.adjoinAt retainedLocals hostItems direct) :=
        (RegionIso.adjoinAt retainedLocals .nil outputEndpointIso).trans
          (RegionIso.ofEq
            (adjoinAt_hostedMaterial retainedLocals hostItems direct).symm)
      let originalOutputIso : RegionIso (WireEquiv.refl itemCommon)
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern application) outputStaged :=
        directSourceIso.trans outputLocalIso.symm
      have outputScope : ScopePreservation
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern application) outputStaged :=
        ScopePreservation.ofIso originalOutputIso
      -/
      exact ⟨staged, hosted, selectedScope, ⟨RegionIso.refl staged⟩⟩

/-- The nonrecursive selected-site premise for the positional identity leaf. -/
theorem identitySelectedTargetItem
    {patternWires itemCommon itemSourceWires itemTargetWires
      formalSourceWires formalTargetWires : List Sig}
    {signature : Sig} {arity : Nat}
    {pattern : OpenDiagram patternWires}
    {ports : Fin arity → Var pattern.external signature}
    {tail : ItemSeq pattern.external}
    (body_eq :
      pattern.body = Region.ofItems (.cons (.identity signature arity ports) tail))
    {itemFrame : Transform.Frame patternWires itemCommon
      itemSourceWires itemTargetWires}
    {itemOperation : Transform.Operation patternWires}
    {itemData : itemOperation.Data itemFrame}
    (application : Vars itemCommon patternWires)
    (siteData : itemOperation.SiteData itemFrame itemData application)
    (formalFrame : Transform.Frame (List.replicate arity signature)
      itemCommon formalSourceWires formalTargetWires) :
    TargetItem
      (targetPattern := positionalIdentityPattern signature arity)
      (targetOperation := Leaf.Identity.operation signature arity)
      (_root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
        (pattern := pattern) (retain := itemFrame.sourceKeep)
        (selected := itemFrame.selected) application)
      (ItemSites.selectedAtom (operation := itemOperation)
        (pattern := pattern) (frame := itemFrame) application siteData)
      (Leaf.Identity.Vars.fromFn ports) formalFrame PUnit.unit
      (fun retained _formalSource formalResult formalEvidence formalSites
          _coherence =>
        ∃ staged : Region itemCommon,
          HostedStrict
              (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
                pattern application) staged ∧
            ScopePreservation
                (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
                  pattern application) staged ∧
              Nonempty (RegionIso (WireEquiv.refl itemCommon) staged
                (Region.adjoinAt retained .nil formalResult))) := by
  unfold TargetItem
  let retainedLocals := EqualityNormalization.locals pattern
  let childFrame := formalFrame.append retainedLocals
  let hostItems := atomSiteHostItems pattern tail application
  let retained : Vars (itemCommon ++ retainedLocals)
      (List.replicate arity signature) :=
    Leaf.Identity.Vars.fromFn
      (fun position => atomBodyWire pattern itemCommon (ports position))
  let formalSource := identityFormalPrefixSource childFrame hostItems retained
  let formalResult := identityFormalPrefixResult signature arity hostItems
    retained
  let formalEvidence := identityFormalPrefixEvidence childFrame hostItems
    retained
  let childApplication : Vars (itemCommon ++ retainedLocals)
      pattern.external :=
    (Erasure.Exposure.identityBoundary pattern.external).map
      (fun wire => atomBodyWire pattern itemCommon wire)
  let formalSites := identityFormalPrefixRecordingSites childFrame hostItems
    retained childApplication
  refine ⟨retainedLocals, formalSource, formalResult, formalEvidence,
    formalSites, ?_, ?_⟩
  · let rename := atomBodyWire pattern itemCommon
    apply identityFormalPrefixSource_eq_argumentItemsEdit childFrame
      hostItems retained childApplication (Leaf.Identity.Vars.fromFn ports)
      rename
    · rfl
    · rw [Leaf.Identity.Vars.fromFn_map]
  let staged := Region.adjoinAt retainedLocals .nil formalResult
  have hosted : HostedStrict
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern application) staged := by
    intro outer hostLocals rename outerHostItems boundary source
      hostedOccurrence targetCanonical targetExternalTwoEnded
    let mappedApplication := application.map fun wire => rename wire
    let sourceBefore :=
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern application).renameWires rename
    let sourceAfter :=
      _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern mappedApplication
    let sourceHostBefore := Region.adjoinAt hostLocals outerHostItems
      sourceBefore
    let sourceHostAfter := Region.adjoinAt hostLocals outerHostItems
      sourceAfter
    change Occurrence sourceHostBefore source at hostedOccurrence
    have sourceHostEq : sourceHostBefore = sourceHostAfter := by
      simp only [sourceHostBefore, sourceHostAfter, sourceBefore, sourceAfter,
        mappedApplication, EqualityNormalization.instantiate_renameWires]
    have sourceAfterCanonical : sourceHostAfter.Canonical := by
      rw [← sourceHostEq]
      exact hostedOccurrence.context.holeCanonical _
        hostedOccurrence.sourceCanonical
    have sourceNonempty : ∀ {wireSignature} (wire : Var outer wireSignature),
        sourceHostBefore.incidencePaths wire.index.val ≠ [] ↔
          sourceHostAfter.incidencePaths wire.index.val ≠ [] := by
      intro wireSignature wire
      rw [sourceHostEq]
    let presentedOccurrence : Occurrence sourceHostAfter source :=
      EqualityNormalization.presentationOccurrence hostedOccurrence
        sourceAfterCanonical sourceNonempty
        (RegionIso.adjoinAt hostLocals outerHostItems
          (EqualityNormalization.instantiateRenameIso pattern application
            rename))
    let mappedHostItems := atomSiteHostItems pattern tail mappedApplication
    let mappedRetained : Vars
        ((outer ++ hostLocals) ++ retainedLocals)
        (List.replicate arity signature) :=
      Leaf.Identity.Vars.fromFn
        (fun position => atomBodyWire pattern (outer ++ hostLocals)
          (ports position))
    let mappedFormalResult := identityFormalPrefixResult signature arity
      mappedHostItems mappedRetained
    let targetAfter := Region.adjoinAt hostLocals outerHostItems
      (Region.adjoinAt retainedLocals .nil mappedFormalResult)
    obtain ⟨ownedCanonical, ownedExternalTwoEnded, ownedStrict,
        outputCanonical, outputExternalTwoEnded, outputStrict⟩ :=
      accumulateSelectedIdentity body_eq outerHostItems mappedApplication
        presentedOccurrence
    change EqualityNormalization.StrictEquates presentedOccurrence targetAfter
      ownedCanonical ownedExternalTwoEnded at ownedStrict
    let retainedRename := rename.appendRight retainedLocals
    have hostItemsEq : hostItems.renameWires retainedRename =
        mappedHostItems := by
      simpa only [hostItems, mappedHostItems, mappedApplication,
        retainedLocals, retainedRename] using
        atomSiteHostItems_renameWires pattern tail application rename
    have retainedEq : retained.map (fun wire => retainedRename wire) =
        mappedRetained := by
      unfold retained mappedRetained
      rw [Leaf.Identity.Vars.fromFn_map]
      apply congrArg Leaf.Identity.Vars.fromFn
      funext position
      have natural := congrArg
        (fun embedding : WireRenaming pattern.external
            ((outer ++ hostLocals) ++ EqualityNormalization.locals pattern) =>
          embedding (ports position))
        (atomBodyWire_natural pattern rename)
      simpa only [retainedLocals, retainedRename, WireRenaming.comp] using
        natural
    have formalResultEq : formalResult.renameWires retainedRename =
        mappedFormalResult := by
      calc
        _ = identityFormalPrefixResult signature arity
            (hostItems.renameWires retainedRename)
            (retained.map fun wire => retainedRename wire) :=
          identityFormalPrefixResult_renameWires signature arity hostItems
            retained retainedRename
        _ = mappedFormalResult := by rw [hostItemsEq, retainedEq]
    let targetBefore := Region.adjoinAt hostLocals outerHostItems
      (staged.renameWires rename)
    have targetEq : targetBefore = targetAfter := by
      simp only [targetBefore, targetAfter, staged,
        Region.renameWires_adjoinAt_nil, retainedLocals]
      rw [formalResultEq]
    let targetPresentation : RegionIso (WireEquiv.refl outer)
        targetAfter targetBefore := RegionIso.ofEq targetEq.symm
    have presentedTargetCanonical :
        (presentedOccurrence.context.fill targetBefore).Canonical :=
      targetCanonical
    have presentedTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        presentedOccurrence.interface.boundaryWire
        (presentedOccurrence.context.fill targetBefore) := by
      intro wireSignature wire
      exact targetExternalTwoEnded wire
    let ownedTargetIso := OpenDiagram.withBody_iso ownedCanonical
      presentedTargetCanonical ownedExternalTwoEnded
      presentedTargetExternalTwoEnded
      (DiagramContext.fillIso presentedOccurrence.context targetPresentation)
    have presentedStrict :=
      EqualityNormalization.StrictEquates.targetIso ownedStrict
        ownedTargetIso
    let targetIso : OpenDiagramIso
        (presentedOccurrence.interface.withBody
          (presentedOccurrence.context.fill targetBefore)
          presentedTargetCanonical presentedTargetExternalTwoEnded)
        (hostedOccurrence.interface.withBody
          (hostedOccurrence.context.fill targetBefore)
          targetCanonical targetExternalTwoEnded) :=
      OpenDiagram.withBody_iso presentedTargetCanonical targetCanonical
        presentedTargetExternalTwoEnded targetExternalTwoEnded
        (RegionIso.refl _)
    exact ⟨transGen_iso (OpenDiagramIso.refl source) presentedStrict.1
        targetIso,
      transGen_iso targetIso presentedStrict.2
        (OpenDiagramIso.refl source)⟩
  /- The deterministic edit endpoint is prepared by the identity consumer.
  let outputStaged := Region.adjoinAt retainedLocals .nil
    (output.endpoint.renameWires (targetRename.appendRight retainedLocals))
  have outputHosted : HostedStrict
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern application) outputStaged := by
    intro outer hostLocals rename outerHostItems boundary source
      hostedOccurrence targetCanonical targetExternalTwoEnded
    let mappedApplication := application.map fun wire => rename wire
    let sourceAfter :=
      _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern mappedApplication
    let sourceHostAfter := Region.adjoinAt hostLocals outerHostItems sourceAfter
    have sourceHostEq :
        Region.adjoinAt hostLocals outerHostItems
            ((_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
              pattern application).renameWires rename) = sourceHostAfter := by
      simp only [sourceHostAfter, sourceAfter, mappedApplication,
        EqualityNormalization.instantiate_renameWires]
    change Occurrence
      (Region.adjoinAt hostLocals outerHostItems
        ((_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern application).renameWires rename)) source at hostedOccurrence
    have sourceAfterCanonical : sourceHostAfter.Canonical := by
      rw [← sourceHostEq]
      exact hostedOccurrence.context.holeCanonical _
        hostedOccurrence.sourceCanonical
    have sourceNonempty : ∀ {wireSignature} (wire : Var outer wireSignature),
        (Region.adjoinAt hostLocals outerHostItems
          ((_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern application).renameWires rename)).incidencePaths
              wire.index.val ≠ [] ↔
          sourceHostAfter.incidencePaths wire.index.val ≠ [] := by
      intro wireSignature wire
      rw [sourceHostEq]
    let presentedOccurrence : Occurrence sourceHostAfter source :=
      EqualityNormalization.presentationOccurrence hostedOccurrence
        sourceAfterCanonical sourceNonempty
        (RegionIso.adjoinAt hostLocals outerHostItems
          (EqualityNormalization.instantiateRenameIso pattern application
            rename))
    let mappedHostItems := atomSiteHostItems pattern tail mappedApplication
    let mappedRetained : Vars
        ((outer ++ hostLocals) ++ retainedLocals)
        (List.replicate arity signature) :=
      Leaf.Identity.Vars.fromFn
        (fun position => atomBodyWire pattern (outer ++ hostLocals)
          (ports position))
    let mappedFrame := Leaf.Identity.rootFrame (outer ++ hostLocals) []
      retainedLocals signature arity
    let mappedEvidence := identityFormalPrefixEvidence mappedFrame
      mappedHostItems mappedRetained
    let mappedSites := identityFormalPrefixSites mappedFrame mappedHostItems
      mappedRetained
    let mappedOutput := itemsEdit
      (operation := Leaf.Identity.operation signature arity)
      PUnit.unit mappedEvidence mappedSites
    let targetAfter := Region.adjoinAt hostLocals outerHostItems
      (Region.adjoinAt retainedLocals .nil mappedOutput.endpoint)
    obtain ⟨ownedCanonical, ownedExternalTwoEnded, ownedStrict,
        mappedOutputCanonical, mappedOutputExternalTwoEnded,
        mappedOutputStrict⟩ :=
      accumulateSelectedIdentity body_eq outerHostItems mappedApplication
        presentedOccurrence
    have combinedStrict := EqualityNormalization.StrictEquates.trans
      ownedStrict mappedOutputStrict
    let retainedRename := rename.appendRight retainedLocals
    have hostItemsEq : hostItems.renameWires retainedRename =
        mappedHostItems := by
      simpa only [hostItems, mappedHostItems, mappedApplication,
        retainedLocals, retainedRename] using
        atomSiteHostItems_renameWires pattern tail application rename
    have retainedEq : retained.map (fun wire => retainedRename wire) =
        mappedRetained := by
      unfold retained mappedRetained
      rw [Leaf.Identity.Vars.fromFn_map]
      apply congrArg Leaf.Identity.Vars.fromFn
      funext position
      have natural := congrArg
        (fun embedding : WireRenaming pattern.external
            ((outer ++ hostLocals) ++ EqualityNormalization.locals pattern) =>
          embedding (ports position))
        (atomBodyWire_natural pattern rename)
      simpa only [retainedLocals, retainedRename, WireRenaming.comp] using
        natural
    have mappedTargetIdentity : mappedFrame.targetKeep = WireRenaming.id := by
      apply WireRenaming.ext
      intro wireSignature wire
      apply Var.appendCases (left := outer ++ hostLocals)
        (right := retainedLocals)
        (motive := fun wire => mappedFrame.targetKeep wire =
          WireRenaming.id wire)
      · intro inheritedSignature inherited
        simp [mappedFrame, Leaf.Identity.rootFrame, Transform.Frame.replace,
          Transform.Frame.keep, Transform.Frame.localKeep, WireRenaming.id]
      · intro localSignature localWire
        simp [mappedFrame, Leaf.Identity.rootFrame, Transform.Frame.replace,
          Transform.Frame.keep, Transform.Frame.localKeep, WireRenaming.id,
          Var.appendMap, Var.appendRight]
    have mappedOutputEq : mappedOutput.endpoint =
        identityFormalPrefixEndpoint signature arity mappedHostItems
          mappedRetained :=
      by
        have endpoint := identityFormalPrefixItemsEditEndpoint signature arity
          mappedFrame mappedHostItems mappedRetained
        rw [mappedTargetIdentity] at endpoint
        exact endpoint.trans (Region.renameWires_id _)
    have endpointEq :
        (output.endpoint.renameWires
          (targetRename.appendRight retainedLocals)).renameWires
            retainedRename = mappedOutput.endpoint := by
      calc
        _ = (identityFormalPrefixEndpoint signature arity hostItems retained
              ).renameWires retainedRename :=
          congrArg (fun region => region.renameWires retainedRename) outputEq
        _ = identityFormalPrefixEndpoint signature arity
            (hostItems.renameWires retainedRename)
            (retained.map fun wire => retainedRename wire) :=
          identityFormalPrefixEndpoint_renameWires signature arity hostItems
            retained retainedRename
        _ = identityFormalPrefixEndpoint signature arity mappedHostItems
            mappedRetained := by rw [hostItemsEq, retainedEq]
        _ = mappedOutput.endpoint := mappedOutputEq.symm
    let targetBefore := Region.adjoinAt hostLocals outerHostItems
      (outputStaged.renameWires rename)
    have targetEq : targetBefore = targetAfter := by
      simp only [targetBefore, targetAfter, outputStaged,
        Region.renameWires_adjoinAt_nil, retainedLocals]
      rw [endpointEq]
    let targetPresentation : RegionIso (WireEquiv.refl outer)
        targetAfter targetBefore := RegionIso.ofEq targetEq.symm
    have presentedTargetCanonical :
        (presentedOccurrence.context.fill targetBefore).Canonical :=
      targetCanonical
    have presentedTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        presentedOccurrence.interface.boundaryWire
        (presentedOccurrence.context.fill targetBefore) := by
      intro wireSignature wire
      exact targetExternalTwoEnded wire
    let combinedTargetIso := OpenDiagram.withBody_iso mappedOutputCanonical
      presentedTargetCanonical mappedOutputExternalTwoEnded
      presentedTargetExternalTwoEnded
      (DiagramContext.fillIso presentedOccurrence.context targetPresentation)
    have presentedStrict :=
      EqualityNormalization.StrictEquates.targetIso combinedStrict
        combinedTargetIso
    let targetIso : OpenDiagramIso
        (presentedOccurrence.interface.withBody
          (presentedOccurrence.context.fill targetBefore)
          presentedTargetCanonical presentedTargetExternalTwoEnded)
        (hostedOccurrence.interface.withBody
          (hostedOccurrence.context.fill targetBefore)
          targetCanonical targetExternalTwoEnded) :=
      OpenDiagram.withBody_iso presentedTargetCanonical targetCanonical
        presentedTargetExternalTwoEnded targetExternalTwoEnded
        (RegionIso.refl _)
    exact ⟨transGen_iso (OpenDiagramIso.refl source) presentedStrict.1
        targetIso,
      transGen_iso targetIso presentedStrict.2
        (OpenDiagramIso.refl source)⟩
  -/
  let sourceIso := identitySelectedSourceIso body_eq application
  let materialScopeForward := positionalIdentityInstantiation_scope
    signature arity retained
  have materialScope : ScopePreservation
      (positionalIdentityApplication signature arity retained)
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        (positionalIdentityPattern signature arity) retained) := {
    canonical := fun _ =>
      _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate_canonical
        (positionalIdentityPattern signature arity) retained
    incidenceNonempty := fun wire =>
      (materialScopeForward.incidenceNonempty wire).symm
    rootedTwo := fun wire rooted => by
      rw [EqualityNormalization.instantiate_rootedTwo_iff]
      rw [← positionalIdentityApplication_incidencePaths_length]
      exact rooted.1
  }
  let direct := positionalIdentityApplication signature arity retained
  let positional :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      (positionalIdentityPattern signature arity) retained
  have stagedScope : ScopePreservation
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern application) staged := by
    let directScope : ScopePreservation
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern application)
        (Region.adjoinAt retainedLocals hostItems direct) :=
      ScopePreservation.ofIso sourceIso
    let exposedScope := adjoinAt_preserves_scope retainedLocals hostItems
      direct positional materialScope
    let formalIso := identityFormalSelectedResultIso
      (pattern := pattern) (ports := ports) tail application
    exact ScopePreservation.trans directScope
      (ScopePreservation.trans exposedScope
        (ScopePreservation.ofIso formalIso.symm))
  /-
  let outputEndpointIso : RegionIso
      (WireEquiv.refl (itemCommon ++ retainedLocals))
      (output.endpoint.renameWires
        (targetRename.appendRight retainedLocals))
      ((Region.ofItems hostItems).conjoin direct) :=
    (RegionIso.ofEq outputEq).trans
      (identityFormalPrefixEndpointIso signature arity hostItems retained)
  let outputLocalIso : RegionIso (WireEquiv.refl itemCommon) outputStaged
      (Region.adjoinAt retainedLocals hostItems direct) :=
    (RegionIso.adjoinAt retainedLocals .nil outputEndpointIso).trans
      (RegionIso.ofEq
        (adjoinAt_hostedMaterial retainedLocals hostItems direct).symm)
  let originalOutputIso := sourceIso.trans outputLocalIso.symm
  have outputScope : ScopePreservation
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern application) outputStaged :=
    ScopePreservation.ofIso originalOutputIso
  -/
  exact ⟨staged, hosted, stagedScope, ⟨RegionIso.refl staged⟩⟩




mutual
  /-- Leaf-only endpoint traversal for a region whose edit retains the common
  wire context literally. -/
  theorem leafRegionEndpoint
      {arguments common sourceWires : List Sig}
      {pattern : OpenDiagram arguments}
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires common}
      {data : operation.Data frame}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : RegionSites operation data evidence)
      (targetKeepEq : frame.targetKeep = WireRenaming.id)
      (selected : ∀
        {siteCommon siteSourceWires : List Sig}
        {siteFrame : Transform.Frame arguments siteCommon siteSourceWires
          siteCommon}
        {siteData : operation.Data siteFrame}
        (siteTargetKeepEq : siteFrame.targetKeep = WireRenaming.id)
        (ports : Vars siteCommon arguments)
        (site : operation.SiteData siteFrame siteData ports),
        HostedStrict
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern ports)
          (operation.site siteFrame siteData ports site) ∧
        ScopePreservation
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern ports)
          (operation.site siteFrame siteData ports site)) :
      HostedStrict result (regionEdit data evidence sites).endpoint ∧
        ScopePreservation result (regionEdit data evidence sites).endpoint := by
    cases sites with
    | @mk _ _ _ _ _ _ locals _ _ _ childSites =>
        have childTargetKeep : (frame.append locals).targetKeep =
            WireRenaming.id := by
          apply WireRenaming.ext
          intro signature wire
          change frame.targetKeep.appendRight locals wire = wire
          rw [targetKeepEq]
          exact WireRenaming.appendRight_id_apply locals wire
        obtain ⟨childHosted, childScope⟩ :=
          leafItemsEndpoint _ childSites childTargetKeep selected
        exact ⟨HostedStrict.adjoinAt _ _ _ childHosted,
          adjoinAt_preserves_scope _ .nil _ _ childScope⟩
  termination_by sizeOf source

  /-- Leaf-only endpoint traversal for an item sequence. -/
  theorem leafItemsEndpoint
      {arguments common sourceWires : List Sig}
      {pattern : OpenDiagram arguments}
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires common}
      {data : operation.Data frame}
      {source : ItemSeq sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : ItemsSites operation data evidence)
      (targetKeepEq : frame.targetKeep = WireRenaming.id)
      (selected : ∀
        {siteCommon siteSourceWires : List Sig}
        {siteFrame : Transform.Frame arguments siteCommon siteSourceWires
          siteCommon}
        {siteData : operation.Data siteFrame}
        (siteTargetKeepEq : siteFrame.targetKeep = WireRenaming.id)
        (ports : Vars siteCommon arguments)
        (site : operation.SiteData siteFrame siteData ports),
        HostedStrict
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern ports)
          (operation.site siteFrame siteData ports site) ∧
        ScopePreservation
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern ports)
          (operation.site siteFrame siteData ports site)) :
      HostedStrict result (itemsEdit data evidence sites).endpoint ∧
        ScopePreservation result (itemsEdit data evidence sites).endpoint := by
    cases sites with
    | nil _ =>
        exact ⟨HostedStrict.refl _, ScopePreservation.refl _⟩
    | cons itemSites tailSites =>
        obtain ⟨itemHosted, itemScope⟩ :=
          leafItemEndpoint _ itemSites targetKeepEq selected
        obtain ⟨tailHosted, tailScope⟩ :=
          leafItemsEndpoint _ tailSites targetKeepEq selected
        exact ⟨HostedStrict.conjoin _ _ _ _ itemHosted tailHosted,
          ScopePreservation.conjoin itemScope tailScope⟩
  termination_by sizeOf source

  /-- Leaf-only endpoint traversal for one item. -/
  theorem leafItemEndpoint
      {arguments common sourceWires : List Sig}
      {pattern : OpenDiagram arguments}
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires common}
      {data : operation.Data frame}
      {source : Item sourceWires} {result : Region common}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected source result)
      (sites : ItemSites operation data evidence)
      (targetKeepEq : frame.targetKeep = WireRenaming.id)
      (selected : ∀
        {siteCommon siteSourceWires : List Sig}
        {siteFrame : Transform.Frame arguments siteCommon siteSourceWires
          siteCommon}
        {siteData : operation.Data siteFrame}
        (siteTargetKeepEq : siteFrame.targetKeep = WireRenaming.id)
        (ports : Vars siteCommon arguments)
        (site : operation.SiteData siteFrame siteData ports),
        HostedStrict
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern ports)
          (operation.site siteFrame siteData ports site) ∧
        ScopePreservation
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern ports)
          (operation.site siteFrame siteData ports site)) :
      HostedStrict result (itemEdit data evidence sites).endpoint ∧
        ScopePreservation result (itemEdit data evidence sites).endpoint := by
    cases sites with
    | atom head ports =>
        have headEq : frame.targetKeep head = head := by
          rw [targetKeepEq]
          rfl
        have portsEq : ports.map (fun wire => frame.targetKeep wire) = ports := by
          rw [targetKeepEq]
          exact Diagram.vars_map_id ports
        simpa only [itemEdit, ExactEdit.refl, Transform.ItemEdit.run,
          headEq, portsEq] using
          And.intro (HostedStrict.refl (Region.singleton (.atom head ports)))
            (ScopePreservation.refl (Region.singleton (.atom head ports)))
    | selectedAtom ports site =>
        simpa only [itemEdit, ExactEdit.refl] using
          selected targetKeepEq ports site
    | identity signature arity ports =>
        have portsEq : (fun index => frame.targetKeep (ports index)) = ports := by
          funext index
          rw [targetKeepEq]
          rfl
        simpa only [itemEdit, ExactEdit.refl, Transform.ItemEdit.run,
          portsEq] using
          And.intro
            (HostedStrict.refl
              (Region.singleton (.identity signature arity ports)))
            (ScopePreservation.refl
              (Region.singleton (.identity signature arity ports)))
    | cut childSites =>
        obtain ⟨childHosted, childScope⟩ :=
          leafRegionEndpoint _ childSites targetKeepEq selected
        exact ⟨HostedStrict.cut _ _ childHosted,
          ScopePreservation.cut childScope⟩
  termination_by sizeOf source
end

/-- The selected-site endpoint transformation for the positional identity
leaf. The recording payload is irrelevant to the primitive endpoint. -/
theorem positionalIdentityLeafEndpoint
    (signature : Sig) (arity : Nat)
    {originalArguments common sourceWires : List Sig}
    {frame : Transform.Frame (List.replicate arity signature) common
      sourceWires common}
    (targetKeepEq : frame.targetKeep = WireRenaming.id)
    (application : Vars common (List.replicate arity signature))
    (site : (recordingOperation
      (Leaf.Identity.operation signature arity) originalArguments).SiteData
        frame PUnit.unit application) :
    HostedStrict
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalIdentityPattern signature arity) application)
        ((recordingOperation
          (Leaf.Identity.operation signature arity) originalArguments).site
            frame PUnit.unit application site) ∧
      ScopePreservation
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalIdentityPattern signature arity) application)
        ((recordingOperation
          (Leaf.Identity.operation signature arity) originalArguments).site
            frame PUnit.unit application site) := by
  rcases site with ⟨⟨identityPorts, applicationEq⟩, recordedApplication⟩
  subst application
  have targetEq :
      (recordingOperation
        (Leaf.Identity.operation signature arity) originalArguments).site
          frame PUnit.unit (Leaf.Identity.Vars.fromFn identityPorts)
          ⟨⟨identityPorts, rfl⟩, recordedApplication⟩ =
        positionalIdentityApplication signature arity
          (Leaf.Identity.Vars.fromFn identityPorts) := by
    change Region.singleton (.identity signature arity
      (fun position => frame.targetKeep (identityPorts position))) = _
    rw [targetKeepEq]
    simp [positionalIdentityApplication, WireRenaming.id,
      Leaf.Identity.Vars.toFn_fromFn]
  rw [targetEq]
  refine ⟨?_, positionalIdentityInstantiation_scope signature arity
    (Leaf.Identity.Vars.fromFn identityPorts)⟩
  intro outer hostLocals rename hostItems boundary source occurrence
    targetCanonical targetExternalTwoEnded
  let mappedApplication :=
    (Leaf.Identity.Vars.fromFn identityPorts).map fun wire => rename wire
  let positional :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      (positionalIdentityPattern signature arity) mappedApplication
  let direct := positionalIdentityApplication signature arity
    mappedApplication
  let sourceBefore := Region.adjoinAt hostLocals hostItems
    ((_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      (positionalIdentityPattern signature arity)
      (Leaf.Identity.Vars.fromFn identityPorts)).renameWires rename)
  let sourceAfter := Region.adjoinAt hostLocals hostItems positional
  change Occurrence sourceBefore source at occurrence
  have sourceEq : sourceBefore = sourceAfter := by
    simp only [sourceBefore, sourceAfter, positional, mappedApplication,
      EqualityNormalization.instantiate_renameWires]
  have sourceAfterCanonical : sourceAfter.Canonical := by
    rw [← sourceEq]
    exact occurrence.context.holeCanonical _ occurrence.sourceCanonical
  let sourcePresentation : RegionIso (WireEquiv.refl outer)
      sourceBefore sourceAfter := RegionIso.ofEq sourceEq
  let presentedOccurrence : Occurrence sourceAfter source :=
    EqualityNormalization.presentationOccurrence occurrence
      sourceAfterCanonical (fun _ => by rw [sourceEq]) sourcePresentation
  let targetBefore := Region.adjoinAt hostLocals hostItems
    ((positionalIdentityApplication signature arity
      (Leaf.Identity.Vars.fromFn identityPorts)).renameWires rename)
  let targetAfter := Region.adjoinAt hostLocals hostItems direct
  have targetEq' : targetBefore = targetAfter := by
    simp only [targetBefore, targetAfter, direct, mappedApplication,
      positionalIdentityApplication, Region.singleton_renameWires,
      Item.renameWires, Leaf.Identity.Vars.fromFn_map,
      Leaf.Identity.Vars.toFn_map, Leaf.Identity.Vars.toFn_fromFn]
  change (occurrence.context.fill targetBefore).Canonical at targetCanonical
  change OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
    (occurrence.context.fill targetBefore) at targetExternalTwoEnded
  have targetAfterCanonical :
      (presentedOccurrence.context.fill targetAfter).Canonical := by
    rw [← targetEq']
    exact targetCanonical
  have targetAfterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      presentedOccurrence.interface.boundaryWire
      (presentedOccurrence.context.fill targetAfter) := by
    intro wireSignature wire
    rw [← targetEq']
    exact targetExternalTwoEnded wire
  let targetOpen := presentedOccurrence.interface.withBody
    (presentedOccurrence.context.fill targetAfter) targetAfterCanonical
      targetAfterExternalTwoEnded
  let directOccurrence : Occurrence targetAfter targetOpen :=
    exactOccurrence presentedOccurrence.interface presentedOccurrence.context
      targetAfter targetAfterCanonical targetAfterExternalTwoEnded
  have core := equatesPositionalIdentityApplication signature arity
    mappedApplication directOccurrence presentedOccurrence.sourceCanonical
      presentedOccurrence.sourceExternalTwoEnded
  let targetIso : OpenDiagramIso targetOpen
      (occurrence.interface.withBody
        (occurrence.context.fill targetBefore) targetCanonical
          targetExternalTwoEnded) :=
    OpenDiagram.withBody_iso targetAfterCanonical targetCanonical
      targetAfterExternalTwoEnded targetExternalTwoEnded
      (DiagramContext.fillIso occurrence.context
        (RegionIso.ofEq targetEq'.symm))
  exact ⟨transGen_iso presentedOccurrence.host_iso.symm core.2 targetIso,
    transGen_iso targetIso core.1 presentedOccurrence.host_iso.symm⟩

/-- Exposing the literal positional atom is a nonempty symmetric phase from
the direct atom to its positional-pattern instantiation. -/
theorem equatesPositionalAtomApplication
    {boundary outer atomArguments : List Sig}
    {hostLocals : List Sig}
    {hostItems : ItemSeq (outer ++ hostLocals)}
    (formal : Var (outer ++ hostLocals) (.rel atomArguments))
    (retained : Vars (outer ++ hostLocals) atomArguments)
    {source : OpenDiagram boundary}
    (occurrence : Occurrence
      (Region.adjoinAt hostLocals hostItems
        (Region.singleton (.atom formal retained))) source)
    (targetCanonical :
      (occurrence.context.fill
        (Region.adjoinAt hostLocals hostItems
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            (positionalAtomPattern atomArguments) (.cons formal retained)))).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill
        (Region.adjoinAt hostLocals hostItems
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            (positionalAtomPattern atomArguments) (.cons formal retained))))) :
    EqualityNormalization.StrictEquates occurrence
      (Region.adjoinAt hostLocals hostItems
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalAtomPattern atomArguments) (.cons formal retained)))
      targetCanonical targetExternalTwoEnded := by
  let description : Rule.Erasure.Description outer := {
    materialWires := positionalAtomWires atomArguments
    hostLocals := hostLocals
    hostItems := hostItems.append
      (EqualityNormalization.contextPins outer hostLocals)
    material := Region.singleton (positionalAtomItem atomArguments)
    wireMap := EqualityNormalization.formalSubstitution (.cons formal retained)
  }
  have nonempty : outer ++ hostLocals ≠ [] := by
    intro empty
    have bound := formal.index.isLt
    simpa [empty] using bound
  apply EqualityNormalization.pinnedExposureStrict occurrence
    targetCanonical targetExternalTwoEnded nonempty description
  · change Region.adjoinAt hostLocals
      (hostItems.append
        (EqualityNormalization.contextPins outer hostLocals))
      ((Region.singleton (positionalAtomItem atomArguments)).renameWires
        (EqualityNormalization.formalSubstitution (.cons formal retained))) = _
    apply congrArg
      (fun material => Region.adjoinAt hostLocals
        (hostItems.append
          (EqualityNormalization.contextPins outer hostLocals)) material)
    calc
      (Region.singleton (positionalAtomItem atomArguments)).renameWires
          (EqualityNormalization.formalSubstitution (.cons formal retained)) =
          Region.singleton
            ((positionalAtomItem atomArguments).renameWires
              (EqualityNormalization.formalSubstitution
                (.cons formal retained))) :=
        Region.singleton_renameWires _ _
      _ = Region.singleton (.atom formal retained) := by
        apply congrArg Region.singleton
        simpa only [positionalAtomCollapse, positionalAtomSelection] using
          positionalAtomItem_rename formal retained
  · rfl
  · intro materialCanonical
    have proofEq : materialCanonical = positionalAtomCanonical atomArguments :=
      Subsingleton.elim _ _
    subst materialCanonical
    simp only [description, Erasure.Exposure.exposedRegion,
      Erasure.Exposure.applicationPorts]
    rw [positionalAtomSupportPattern_eq]
    simpa only [
      ← EqualityNormalization.formalPorts_eq_exposure,
      EqualityNormalization.formalPorts_map_substitution]

/-- The selected-site endpoint transformation for the positional formal-atom
leaf. -/
theorem positionalAtomLeafEndpoint
    (atomArguments : List Sig)
    {originalArguments common sourceWires : List Sig}
    {frame : Transform.Frame (positionalAtomWires atomArguments) common
      sourceWires common}
    (targetKeepEq : frame.targetKeep = WireRenaming.id)
    (application : Vars common (positionalAtomWires atomArguments))
    (site : (recordingOperation
      (Leaf.Formal.operation [] atomArguments) originalArguments).SiteData
        frame PUnit.unit application) :
    HostedStrict
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalAtomPattern atomArguments) application)
        ((recordingOperation
          (Leaf.Formal.operation [] atomArguments) originalArguments).site
            frame PUnit.unit application site) ∧
      ScopePreservation
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalAtomPattern atomArguments) application)
        ((recordingOperation
          (Leaf.Formal.operation [] atomArguments) originalArguments).site
            frame PUnit.unit application site) := by
  rcases site with ⟨⟨formal, ⟨retained, applicationEq⟩⟩,
    recordedApplication⟩
  simp only [Argument.Projection.Vars.insertAt] at applicationEq
  subst application
  have targetEq :
      (recordingOperation
        (Leaf.Formal.operation [] atomArguments) originalArguments).site
          frame PUnit.unit (.cons formal retained)
          ⟨⟨formal, ⟨retained, rfl⟩⟩, recordedApplication⟩ =
        Region.singleton (.atom formal retained) := by
    change Region.singleton
      (.atom (frame.targetKeep formal)
        (retained.map fun wire => frame.targetKeep wire)) = _
    rw [targetKeepEq]
    simp [WireRenaming.id, Diagram.vars_map_id]
  rw [targetEq]
  have directScope : ScopePreservation
      (Region.singleton (.atom formal retained))
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        (positionalAtomPattern atomArguments) (.cons formal retained)) := by
    simpa only [List.nil_append] using
      positionalAtomInstantiation_scope formal retained
  have reverseScope : ScopePreservation
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        (positionalAtomPattern atomArguments) (.cons formal retained))
      (Region.singleton (.atom formal retained)) := by
    constructor
    · intro _
      change (∀ localIndex : Fin 0, RegionPath.RootedTwo _) ∧ _
      exact ⟨fun localIndex => Fin.elim0 localIndex,
        ⟨True.intro, True.intro⟩⟩
    · intro signature wire
      exact (directScope.incidenceNonempty wire).symm
    · intro signature wire sourceRoot
      have countBound : 2 ≤ (Vars.cons formal retained).countIndex
          wire.index.val := by
        rw [← EqualityNormalization.instantiate_rootedTwo_iff]
        exact sourceRoot
      constructor
      · rw [selectedAtomIncidencePaths_length]
        exact countBound
      · apply RegionPath.deepestCommonAncestor_eq_nil_of_mem_nil
        let appendNil : WireRenaming common (common ++ []) :=
          ⟨fun selected => selected.appendLeft []⟩
        have retainedCountEq :
            (retained.map (fun selected => appendNil selected)).countIndex
                wire.index.val = retained.countIndex wire.index.val :=
          Vars.countIndex_map_of_sameIndex retained appendNil
            (fun selected => Var.index_appendLeft selected []) wire.index.val
        simp only [Region.singleton, Region.ofItems, Region.incidencePaths,
          ItemSeq.renameWires, Item.renameWires, ItemSeq.incidencePaths,
          Item.incidencePaths, List.append_nil, Var.index_appendLeft,
          List.mem_append]
        rw [List.mem_replicate, retainedCountEq]
        exact ⟨by
          simp only [Vars.countIndex] at countBound
          simpa only [Vars.countIndex] using
            Nat.ne_of_gt (by omega), rfl⟩
  refine ⟨?_, reverseScope⟩
  intro outer hostLocals rename hostItems boundary source occurrence
    targetCanonical targetExternalTwoEnded
  let mappedFormal := rename formal
  let mappedRetained := retained.map fun wire => rename wire
  let mappedApplication : Vars (outer ++ hostLocals)
      (positionalAtomWires atomArguments) :=
    .cons mappedFormal mappedRetained
  let sourceBefore := Region.adjoinAt hostLocals hostItems
    ((_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      (positionalAtomPattern atomArguments) (.cons formal retained)
      ).renameWires rename)
  let sourceAfter := Region.adjoinAt hostLocals hostItems
    (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      (positionalAtomPattern atomArguments) mappedApplication)
  change Occurrence sourceBefore source at occurrence
  have sourceEq : sourceBefore = sourceAfter := by
    apply congrArg (Region.adjoinAt hostLocals hostItems)
    simpa only [mappedApplication, mappedFormal, mappedRetained,
      Theory.Vars.map] using
        EqualityNormalization.instantiate_renameWires
          (positionalAtomPattern atomArguments) (.cons formal retained) rename
  have sourceAfterCanonical : sourceAfter.Canonical := by
    rw [← sourceEq]
    exact occurrence.context.holeCanonical _ occurrence.sourceCanonical
  let sourcePresentation : RegionIso (WireEquiv.refl outer)
      sourceBefore sourceAfter := RegionIso.ofEq sourceEq
  let presentedOccurrence : Occurrence sourceAfter source :=
    EqualityNormalization.presentationOccurrence occurrence
      sourceAfterCanonical (fun _ => by rw [sourceEq]) sourcePresentation
  let direct := Region.singleton (.atom mappedFormal mappedRetained)
  have directEq :
      Region.adjoinAt hostLocals hostItems
          ((Region.singleton (.atom formal retained)).renameWires rename) =
        Region.adjoinAt hostLocals hostItems direct := by
    simp [direct, mappedFormal, mappedRetained,
      Region.singleton_renameWires, Item.renameWires]
  have directCanonical :
      (presentedOccurrence.context.fill
        (Region.adjoinAt hostLocals hostItems direct)).Canonical := by
    simpa only [directEq] using targetCanonical
  have directExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      presentedOccurrence.interface.boundaryWire
      (presentedOccurrence.context.fill
        (Region.adjoinAt hostLocals hostItems direct)) := by
    intro signature wire
    simpa only [directEq] using targetExternalTwoEnded wire
  let directEndpoint := presentedOccurrence.interface.withBody
    (presentedOccurrence.context.fill
      (Region.adjoinAt hostLocals hostItems direct))
    directCanonical directExternalTwoEnded
  let directOccurrence : Occurrence
      (Region.adjoinAt hostLocals hostItems direct) directEndpoint :=
    exactOccurrence presentedOccurrence.interface presentedOccurrence.context
      (Region.adjoinAt hostLocals hostItems direct)
      directCanonical directExternalTwoEnded
  have core := equatesPositionalAtomApplication mappedFormal mappedRetained
    directOccurrence presentedOccurrence.sourceCanonical
      presentedOccurrence.sourceExternalTwoEnded
  let directIso : OpenDiagramIso directEndpoint
      (occurrence.interface.withBody
        (occurrence.context.fill
          (Region.adjoinAt hostLocals hostItems
            ((Region.singleton (.atom formal retained)).renameWires rename)))
        targetCanonical targetExternalTwoEnded) :=
    OpenDiagram.withBody_iso directCanonical targetCanonical
      directExternalTwoEnded targetExternalTwoEnded
      (DiagramContext.fillIso occurrence.context (RegionIso.ofEq directEq.symm))
  exact ⟨transGen_iso presentedOccurrence.host_iso.symm core.2 directIso,
    transGen_iso directIso core.1 presentedOccurrence.host_iso.symm⟩


end VisualProof.Rule.Completeness.Comprehension
