import VisualProof.Rule.Completeness.Comprehension.Structural.Hosted
import VisualProof.Rule.Completeness.Comprehension.Leaf.Sites

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
      VisualProof.Rule.Comprehension.Instantiation.RegionResult pattern
        originalFrame.sourceKeep originalFrame.selected source result)
    (_sites : RegionSites operation data evidence)
    (targetValues : Vars targetExternal targetArguments)
    (targetFrame : Transform.Frame targetArguments
      common sourceWires targetWires)
    (targetData : targetOperation.Data targetFrame)
    (K : ∀ (formalSource : Region sourceWires)
        (formalResult : Region common)
        (formalEvidence :
          VisualProof.Rule.Comprehension.Instantiation.RegionResult
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
          VisualProof.Rule.Comprehension.Instantiation.RegionResult
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
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult pattern
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
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult
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
            VisualProof.Rule.Comprehension.Instantiation.ItemsResult
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
      VisualProof.Rule.Comprehension.Instantiation.ItemResult pattern
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
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult
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
            VisualProof.Rule.Comprehension.Instantiation.ItemsResult
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
      (VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
        (pattern := pattern) (retain := itemFrame.sourceKeep)
        (selected := itemFrame.selected) application)
      (ItemSites.selectedAtom (operation := itemOperation)
        (pattern := pattern) (frame := itemFrame) application siteData)
      (positionalAtomSelection head ports) formalFrame PUnit.unit
      (fun retained _formalSource formalResult formalEvidence formalSites
          _coherence =>
        ∃ staged : Region itemCommon,
          HostedStrict
              (VisualProof.Rule.Comprehension.Instantiation.instantiate
                pattern application) staged ∧
            ScopePreservation
                (VisualProof.Rule.Comprehension.Instantiation.instantiate
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
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern application) staged := by
        intro outer hostLocals rename outerHostItems boundary source
          hostedOccurrence targetCanonical targetExternalTwoEnded
        let mappedApplication := application.map fun wire => rename wire
        let sourceBefore :=
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern application).renameWires rename
        let sourceAfter :=
          VisualProof.Rule.Comprehension.Instantiation.instantiate
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
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern application) outputStaged := by
        intro outer hostLocals rename outerHostItems boundary source
          hostedOccurrence targetCanonical targetExternalTwoEnded
        let mappedApplication := application.map fun wire => rename wire
        let sourceBefore :=
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern application).renameWires rename
        let sourceAfter :=
          VisualProof.Rule.Comprehension.Instantiation.instantiate
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
        VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalAtomPattern atomArguments) (.cons formal retainedPorts)
      let raw := atomExposureDescription (head := head) (ports := ports)
        tail application
      have rawSourceEq : raw.source =
          Region.adjoinAt retainedLocals hostItems direct := by
        simp only [raw, Rule.UncappedErasure.Description.source, Region.spliceAt,
          atomExposureDescription, retainedLocals, hostItems, direct]
        exact congrArg
          (fun material => Region.adjoinAt retainedLocals hostItems material)
          (by
            simpa only [atomExposureDescription, formal, retainedPorts] using
              atomExposureMaterialRename tail application)
      let rawSourceIso := atomExposureSourceIso body_eq application
      let directSourceIso : RegionIso (WireEquiv.refl itemCommon)
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
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
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
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
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern application) outputStaged :=
        directSourceIso.trans outputLocalIso.symm
      have outputScope : ScopePreservation
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern application) outputStaged :=
        ScopePreservation.ofIso originalOutputIso
      -/
      exact ⟨staged, hosted, selectedScope, ⟨RegionIso.refl staged⟩⟩

/-- The singleton atom whose support pattern is being compiled. -/
def supportAtomMaterial
    {wires atomArguments : List Sig}
    (head : Var wires (.rel atomArguments))
    (ports : Vars wires atomArguments) : Region wires :=
  Region.singleton (.atom head ports)

theorem supportAtomMaterial_canonical
    {wires atomArguments : List Sig}
    (head : Var wires (.rel atomArguments))
    (ports : Vars wires atomArguments) :
    (supportAtomMaterial head ports).Canonical := by
  change (∀ localIndex : Fin 0, RegionPath.RootedTwo _) ∧
    (ItemSeq.cons _ ItemSeq.nil).ChildrenCanonical
  exact ⟨fun localIndex => Fin.elim0 localIndex,
    ⟨True.intro, True.intro⟩⟩

/-- The authoritative support pins on the singleton atom's explicit
zero-local carrier. -/
def supportAtomPinsAppended
    {wires atomArguments : List Sig}
    (head : Var wires (.rel atomArguments))
    (ports : Vars wires atomArguments) : ItemSeq (wires ++ []) :=
  Erasure.Exposure.supportPins (supportAtomMaterial head ports) wires
    (Erasure.Exposure.identityBoundary wires)

def supportAtomTail
    {wires atomArguments : List Sig}
    (head : Var wires (.rel atomArguments))
    (ports : Vars wires atomArguments) : ItemSeq wires :=
  (supportAtomPinsAppended head ports).renameWires
    (WireEquiv.appendNil wires).toRenaming

theorem supportAtomTail_appendNil
    {wires atomArguments : List Sig}
    (head : Var wires (.rel atomArguments))
    (ports : Vars wires atomArguments) :
    (supportAtomTail head ports).renameWires
        (WireEquiv.appendNil wires).symm.toRenaming =
      supportAtomPinsAppended head ports := by
  unfold supportAtomTail
  rw [ItemSeq.renameWires_comp]
  have renameEq : WireRenaming.comp
      (WireEquiv.appendNil wires).symm.toRenaming
      (WireEquiv.appendNil wires).toRenaming = WireRenaming.id := by
    apply WireRenaming.ext
    intro signature wire
    exact (WireEquiv.appendNil wires).left_inv wire
  rw [renameEq]
  exact ItemSeq.renameWires_id _

theorem supportAtomBody_eq
    {wires atomArguments : List Sig}
    (head : Var wires (.rel atomArguments))
    (ports : Vars wires atomArguments) :
    Erasure.Exposure.supportBody (supportAtomMaterial head ports) =
      Region.ofItems (.cons (.atom head ports) (supportAtomTail head ports)) := by
  unfold Erasure.Exposure.supportBody supportAtomMaterial
  simp only [Region.singleton, Region.ofItems, Region.locals, Region.items]
  have pinsEq :
      Erasure.Exposure.supportPins
          (Region.mk [] (ItemSeq.renameWires
            ⟨fun wire => wire.appendLeft []⟩
            (.cons (.atom head ports) .nil))) wires
          (Erasure.Exposure.identityBoundary wires) =
        supportAtomPinsAppended head ports := by
    simp [supportAtomPinsAppended, supportAtomMaterial, Region.singleton,
      Region.ofItems, Region.locals]
  rw [pinsEq]
  rw [← supportAtomTail_appendNil head ports]
  have appendEq : (⟨fun wire => wire.appendLeft []⟩ :
      WireRenaming wires (wires ++ [])) =
      (WireEquiv.appendNil wires).symm.toRenaming := by
    apply WireRenaming.ext
    intro signature wire
    exact (WireEquiv.appendNil_symm_apply wires wire).symm
  rw [appendEq]
  rfl

/-- Instantiating the support completion of one atom preserves exactly the
scope of the atom and its support pins after the boundary substitution. -/
theorem supportAtomInstantiationScope
    {wires atomArguments common : List Sig}
    (head : Var wires (.rel atomArguments))
    (ports : Vars wires atomArguments)
    (application : Vars common wires) :
    let substitution := EqualityNormalization.formalSubstitution application
    let pins := EqualityNormalization.allPins wires substitution
    ScopePreservation
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        (Erasure.Exposure.supportPattern
          (supportAtomMaterial head ports)
          (supportAtomMaterial_canonical head ports))
        application)
      (((Erasure.Exposure.supportBody
          (supportAtomMaterial head ports)).renameWires substitution).conjoin
        (Region.ofItems (pins.append pins))) := by
  exact EqualityNormalization.supportInstantiationPinnedScope
    (supportAtomMaterial head ports)
    (supportAtomMaterial_canonical head ports) application

theorem positionalAtomInstantiation_reverseScope
    {wires atomArguments : List Sig}
    (formal : Var wires (.rel atomArguments))
    (retained : Vars wires atomArguments) :
    ScopePreservation
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        (positionalAtomPattern atomArguments) (.cons formal retained))
      (Region.singleton (.atom formal retained)) := by
  have directScope := positionalAtomInstantiation_scope formal retained
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
      let appendNil : WireRenaming wires (wires ++ []) :=
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
        simpa only [Vars.countIndex] using Nat.ne_of_gt (by omega), rfl⟩

theorem positionalAtomInstantiation_reverseHostedScope
    {wires atomArguments : List Sig}
    (formal : Var wires (.rel atomArguments))
    (retained : Vars wires atomArguments) :
    HostedScope
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        (positionalAtomPattern atomArguments) (.cons formal retained))
      (Region.singleton (.atom formal retained)) := by
  intro target rename
  let mappedFormal := rename formal
  let mappedRetained := retained.map fun wire => rename wire
  have sourceEq :
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        (positionalAtomPattern atomArguments) (.cons formal retained)
        ).renameWires rename =
      VisualProof.Rule.Comprehension.Instantiation.instantiate
        (positionalAtomPattern atomArguments)
        (.cons mappedFormal mappedRetained) := by
    simpa only [mappedFormal, mappedRetained, Theory.Vars.map] using
      EqualityNormalization.instantiate_renameWires
        (positionalAtomPattern atomArguments) (.cons formal retained) rename
  have targetEq :
      (Region.singleton (.atom formal retained)).renameWires rename =
        Region.singleton (.atom mappedFormal mappedRetained) := by
    simp [mappedFormal, mappedRetained, Region.singleton_renameWires,
      Item.renameWires]
  rw [sourceEq, targetEq]
  exact positionalAtomInstantiation_reverseScope mappedFormal mappedRetained

/-- A selected support-singleton atom is presented directly at its actual
application, without copied boundary locals. -/
theorem supportAtomSelectedTargetItem
    {wires atomArguments itemCommon itemSourceWires itemTargetWires
      formalSourceWires formalTargetWires : List Sig}
    (head : Var wires (.rel atomArguments))
    (ports : Vars wires atomArguments)
    {itemFrame : Transform.Frame wires itemCommon itemSourceWires
      itemTargetWires}
    {itemOperation : Transform.Operation wires}
    {itemData : itemOperation.Data itemFrame}
    (application : Vars itemCommon wires)
    (siteData : itemOperation.SiteData itemFrame itemData application)
    (formalFrame : Transform.Frame (positionalAtomWires atomArguments)
      itemCommon formalSourceWires formalTargetWires) :
    TargetItem
      (targetPattern := positionalAtomPattern atomArguments)
      (targetOperation := Leaf.Formal.operation [] atomArguments)
      (VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
        (pattern := Erasure.Exposure.supportPattern
          (supportAtomMaterial head ports)
          (supportAtomMaterial_canonical head ports))
        (retain := itemFrame.sourceKeep)
        (selected := itemFrame.selected) application)
      (ItemSites.selectedAtom (operation := itemOperation)
        (pattern := Erasure.Exposure.supportPattern
          (supportAtomMaterial head ports)
          (supportAtomMaterial_canonical head ports))
        (frame := itemFrame) application siteData)
      (positionalAtomSelection head ports) formalFrame PUnit.unit
      (fun retained _formalSource formalResult _formalEvidence formalSites
          _coherence =>
        ∃ staged : Region itemCommon,
          HostedStrict
              (VisualProof.Rule.Comprehension.Instantiation.instantiate
                (Erasure.Exposure.supportPattern
                  (supportAtomMaterial head ports)
                  (supportAtomMaterial_canonical head ports))
                application)
              staged ∧
            ScopePreservation
              (VisualProof.Rule.Comprehension.Instantiation.instantiate
                (Erasure.Exposure.supportPattern
                  (supportAtomMaterial head ports)
                  (supportAtomMaterial_canonical head ports))
                application)
              staged ∧
              Nonempty (RegionIso (WireEquiv.refl itemCommon) staged
                (Region.adjoinAt retained .nil formalResult)) ∧
              retained = [] ∧
              let authoritativeFrame : Transform.Frame wires itemCommon
                  itemSourceWires itemSourceWires := {
                sourceKeep := itemFrame.sourceKeep
                targetKeep := itemFrame.sourceKeep
                selected := itemFrame.selected
              }
              let direct := Region.singleton (.atom itemFrame.selected
                (application.map fun wire => itemFrame.sourceKeep wire))
              let authoritative := Region.adjoinAt retained .nil
                (Region.ofItems
                  (argumentItemsEdit formalSites
                    (EqualityNormalization.formalPorts wires)
                    (normalizationOperation wires)
                    (authoritativeFrame.append retained)
                    PUnit.unit (fun _ _ _ => PUnit.unit)).1)
              HostedStrict direct authoritative ∧
                HostedScope direct authoritative) := by
  unfold TargetItem
  let commonEquiv := WireEquiv.appendNil itemCommon
  let commonAppend := commonEquiv.symm.toRenaming
  let mappedApplication := application.map fun wire => commonAppend wire
  let substitution := EqualityNormalization.formalSubstitution mappedApplication
  let mappedPins := EqualityNormalization.allPins wires substitution
  let hostItems :=
    ((supportAtomTail head ports).renameWires substitution).append
      (mappedPins.append mappedPins)
  let formal := substitution head
  let retainedPorts := ports.map fun wire => substitution wire
  let childFrame := formalFrame.append []
  let formalSource := atomFormalPrefixSource childFrame hostItems formal
    retainedPorts
  let formalResult := atomFormalPrefixResult hostItems formal retainedPorts
  let formalEvidence := atomFormalPrefixEvidence childFrame hostItems formal
    retainedPorts
  let formalSites := atomFormalPrefixRecordingSites childFrame hostItems formal
    retainedPorts mappedApplication
  refine ⟨[], formalSource, formalResult, formalEvidence, formalSites, ?_, ?_⟩
  · apply atomFormalPrefixSource_eq_argumentItemsEdit childFrame hostItems
      formal retainedPorts mappedApplication
      (positionalAtomSelection head ports)
      substitution
    · exact (EqualityNormalization.formalPorts_map_substitution
        mappedApplication).symm
    · simp only [positionalAtomSelection, Vars.map]
      rfl
  · let rawSubstitution := EqualityNormalization.formalSubstitution application
    let rawSupportItems :=
      (supportAtomTail head ports).renameWires rawSubstitution
    let rawPins := EqualityNormalization.allPins wires rawSubstitution
    let rawHostItems := rawSupportItems.append (rawPins.append rawPins)
    let rawFormal := rawSubstitution head
    let rawRetainedPorts := ports.map fun wire => rawSubstitution wire
    let staged := atomFormalPrefixResult rawHostItems rawFormal rawRetainedPorts
    refine ⟨staged, ?_, ?_, ?_, rfl, ?_⟩
    · let material := supportAtomMaterial head ports
      let materialCanonical := supportAtomMaterial_canonical head ports
      let supported := Erasure.Exposure.supportBody material
      let supportedCanonical := Erasure.Exposure.supportBody_canonical
        material materialCanonical
      have supportedPinsNil : Erasure.Exposure.supportPins supported wires
          (Erasure.Exposure.identityBoundary wires) = .nil := by
        apply EqualityNormalization.supportPins_eq_nil
        intro position
        exact Erasure.Exposure.supportBody_incidence_nonempty material
          ((Erasure.Exposure.identityBoundary wires).get position)
      have supportedFixed : Erasure.Exposure.supportBody supported =
          supported :=
        EqualityNormalization.supportBody_eq_of_supportPins_nil supported
          supportedPinsNil
      have patternEq : Erasure.Exposure.supportPattern supported
            supportedCanonical =
          Erasure.Exposure.supportPattern material materialCanonical := by
        apply EqualityNormalization.OpenDiagram.eq_of_data
        · rfl
        · rfl
        · exact heq_of_eq supportedFixed
      have sourceToSupported : HostedStrict
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            (Erasure.Exposure.supportPattern material materialCanonical)
            application)
          (supported.renameWires rawSubstitution) := by
        rw [← patternEq]
        exact supportInstantiationHosted supported supportedCanonical application
      have supportedTargetEq : supported.renameWires rawSubstitution =
          Region.ofItems (.cons (.atom rawFormal rawRetainedPorts)
            rawSupportItems) := by
        change (Erasure.Exposure.supportBody
          (supportAtomMaterial head ports)).renameWires rawSubstitution = _
        rw [supportAtomBody_eq head ports]
        simp only [Region.renameWires, Region.ofItems, ItemSeq.renameWires,
          Item.renameWires, rawFormal, rawRetainedPorts, rawSupportItems]
        simp [WireRenaming.appendRight, Vars.map_map,
          ItemSeq.renameWires_comp]
        apply congrArg (fun rename =>
          (supportAtomTail head ports).renameWires rename)
        apply WireRenaming.ext
        intro signature wire
        simp [WireRenaming.comp, WireRenaming.appendRight]
      let direct := Region.singleton (.atom rawFormal rawRetainedPorts)
      let supportPins := Region.ofItems rawSupportItems
      let allPins := Region.ofItems (rawPins.append rawPins)
      let positional :=
        VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalAtomPattern atomArguments)
          (.cons rawFormal rawRetainedPorts)
      let supportedPresentation : RegionIso (WireEquiv.refl itemCommon)
          (supported.renameWires rawSubstitution)
          (direct.conjoin supportPins) :=
        (RegionIso.ofEq supportedTargetEq).trans
          (RegionIso.ofEq
            (Region.singleton_conjoin_ofItems
              (.atom rawFormal rawRetainedPorts) rawSupportItems).symm)
      have sourceToDirectPins : HostedStrict
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            (Erasure.Exposure.supportPattern material materialCanonical)
            application)
          (direct.conjoin supportPins) :=
        HostedStrict.iso (RegionIso.refl _) supportedPresentation
          sourceToSupported
      have positionalToDirect : HostedStrict positional direct := by
        have exposed := supportInstantiationHosted
          (Region.singleton (positionalAtomItem atomArguments))
          (positionalAtomCanonical atomArguments)
          (.cons rawFormal rawRetainedPorts)
        rw [positionalAtomSupportPattern_eq] at exposed
        have targetEq :
            (Region.singleton (positionalAtomItem atomArguments)).renameWires
                (EqualityNormalization.formalSubstitution
                  (.cons rawFormal rawRetainedPorts)) = direct := by
          calc
            _ = Region.singleton
                ((positionalAtomItem atomArguments).renameWires
                  (EqualityNormalization.formalSubstitution
                    (.cons rawFormal rawRetainedPorts))) :=
              Region.singleton_renameWires _ _
            _ = direct := by
              apply congrArg Region.singleton
              simpa only [positionalAtomCollapse,
                positionalAtomSelection] using
                positionalAtomItem_rename rawFormal rawRetainedPorts
        exact HostedStrict.iso (RegionIso.refl _)
          (RegionIso.ofEq targetEq) exposed
      have directToPositionalPins : HostedStrict (direct.conjoin supportPins)
          (positional.conjoin supportPins) :=
        HostedStrict.conjoin direct supportPins positional supportPins
          positionalToDirect.symm (HostedStrict.refl supportPins)
      have positionalPinsReverse : HostedScope
          (positional.conjoin supportPins)
          (direct.conjoin supportPins) := by
        intro target rename
        simpa only [positional, direct, Region.renameWires_conjoin] using
          ScopePreservation.conjoin
            (positionalAtomInstantiation_reverseHostedScope rawFormal
              rawRetainedPorts rename)
            (ScopePreservation.refl (supportPins.renameWires rename))
      have sourceToPositionalPins : HostedStrict
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            (Erasure.Exposure.supportPattern material materialCanonical)
            application)
          (positional.conjoin supportPins) :=
        HostedStrict.trans sourceToDirectPins directToPositionalPins
          (fun outer hostLocals rename hostItems =>
            HostedScope.adjoinHost positionalPinsReverse outer hostLocals
              rename hostItems)
      let source :=
        VisualProof.Rule.Comprehension.Instantiation.instantiate
          (Erasure.Exposure.supportPattern material materialCanonical)
          application
      let pinned := HostedStrict.conjoin source (Region.blank itemCommon)
        (positional.conjoin supportPins) allPins sourceToPositionalPins
        (HostedStrict.allPinsTwice wires rawSubstitution)
      let supportPinsPresentation : RegionIso (WireEquiv.refl itemCommon)
          (supportPins.conjoin allPins) (Region.ofItems rawHostItems) :=
        RegionIso.ofEq (by
          rw [Region.ofItems_conjoin])
      let resultPresentation : RegionIso (WireEquiv.refl itemCommon)
          ((positional.conjoin supportPins).conjoin allPins) staged :=
        (RegionIso.conjoinAssoc positional supportPins allPins).trans
          ((RegionIso.conjoinCongr (RegionIso.refl positional)
            supportPinsPresentation).trans
            ((RegionIso.conjoinComm positional
              (Region.ofItems rawHostItems)).trans
              (atomFormalPrefixResultIso rawHostItems rawFormal
                rawRetainedPorts).symm))
      exact HostedStrict.iso (RegionIso.conjoinBlank source).symm
        resultPresentation pinned
    · let supported := Erasure.Exposure.supportBody
        (supportAtomMaterial head ports)
      let direct := Region.singleton (.atom rawFormal rawRetainedPorts)
      let supportPins := Region.ofItems rawSupportItems
      let allPins := Region.ofItems (rawPins.append rawPins)
      let positional :=
        VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalAtomPattern atomArguments)
          (.cons rawFormal rawRetainedPorts)
      have sourceToSupportedPins : ScopePreservation
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            (Erasure.Exposure.supportPattern
              (supportAtomMaterial head ports)
              (supportAtomMaterial_canonical head ports))
            application)
          ((supported.renameWires rawSubstitution).conjoin allPins) := by
        exact supportAtomInstantiationScope head ports application
      have supportedTargetEq : supported.renameWires rawSubstitution =
          Region.ofItems (.cons (.atom rawFormal rawRetainedPorts)
            rawSupportItems) := by
        change (Erasure.Exposure.supportBody
          (supportAtomMaterial head ports)).renameWires rawSubstitution = _
        rw [supportAtomBody_eq head ports]
        simp only [Region.renameWires, Region.ofItems, ItemSeq.renameWires,
          Item.renameWires, rawFormal, rawRetainedPorts, rawSupportItems]
        simp [WireRenaming.appendRight, Vars.map_map,
          ItemSeq.renameWires_comp]
        apply congrArg (fun rename =>
          (supportAtomTail head ports).renameWires rename)
        apply WireRenaming.ext
        intro signature wire
        simp [WireRenaming.comp, WireRenaming.appendRight]
      let supportedPresentation : RegionIso (WireEquiv.refl itemCommon)
          (supported.renameWires rawSubstitution)
          (direct.conjoin supportPins) :=
        (RegionIso.ofEq supportedTargetEq).trans
          (RegionIso.ofEq
            (Region.singleton_conjoin_ofItems
              (.atom rawFormal rawRetainedPorts) rawSupportItems).symm)
      have supportedToDirectPins : ScopePreservation
          ((supported.renameWires rawSubstitution).conjoin allPins)
          ((direct.conjoin supportPins).conjoin allPins) :=
        ScopePreservation.ofIso
          (RegionIso.conjoinCongr supportedPresentation
            (RegionIso.refl allPins))
      have directToPositionalPins : ScopePreservation
          ((direct.conjoin supportPins).conjoin allPins)
          ((positional.conjoin supportPins).conjoin allPins) :=
        ScopePreservation.conjoin
          (ScopePreservation.conjoin
            (positionalAtomInstantiation_scope rawFormal rawRetainedPorts)
            (ScopePreservation.refl supportPins))
          (ScopePreservation.refl allPins)
      let supportPinsPresentation : RegionIso (WireEquiv.refl itemCommon)
          (supportPins.conjoin allPins) (Region.ofItems rawHostItems) :=
        RegionIso.ofEq (by
          rw [Region.ofItems_conjoin])
      let resultPresentation : RegionIso (WireEquiv.refl itemCommon)
          ((positional.conjoin supportPins).conjoin allPins) staged :=
        (RegionIso.conjoinAssoc positional supportPins allPins).trans
          ((RegionIso.conjoinCongr (RegionIso.refl positional)
            supportPinsPresentation).trans
            ((RegionIso.conjoinComm positional
              (Region.ofItems rawHostItems)).trans
              (atomFormalPrefixResultIso rawHostItems rawFormal
                rawRetainedPorts).symm))
      exact sourceToSupportedPins.trans
        (supportedToDirectPins.trans
          (directToPositionalPins.trans
            (ScopePreservation.ofIso resultPresentation)))
    · have mappedResultEq : staged.renameWires commonAppend = formalResult := by
        rw [atomFormalPrefixResult_renameWires]
        have hostItemsEq : rawHostItems.renameWires commonAppend = hostItems := by
          have substitutionEq : WireRenaming.comp commonAppend rawSubstitution =
              substitution := by
            apply WireRenaming.ext
            intro signature wire
            exact (EqualityNormalization.formalSubstitution_map
              application commonAppend wire).symm
          have supportItemsEq : rawSupportItems.renameWires commonAppend =
              (supportAtomTail head ports).renameWires substitution := by
            unfold rawSupportItems rawSubstitution
            rw [ItemSeq.renameWires_comp, substitutionEq]
          have pinsEq : rawPins.renameWires commonAppend = mappedPins := by
            unfold rawPins mappedPins rawSubstitution
            rw [EqualityNormalization.allPins_renameWires, substitutionEq]
          unfold rawHostItems hostItems
          simp only [ItemSeq.renameWires_append, supportItemsEq, pinsEq]
        have formalEq : commonAppend rawFormal = formal := by
          exact (EqualityNormalization.formalSubstitution_map
            application commonAppend head).symm
        have portsEq : rawRetainedPorts.map (fun wire => commonAppend wire) =
            retainedPorts := by
          unfold rawRetainedPorts retainedPorts
          rw [Vars.map_map]
          apply Vars.map_congr
          intro signature wire
          exact (EqualityNormalization.formalSubstitution_map
            application commonAppend wire).symm
        rw [hostItemsEq, formalEq, portsEq]
      let intoMapped : RegionIso commonEquiv.symm staged formalResult := by
        let renamed := RegionIso.renameWires staged WireRenaming.id
          commonAppend commonEquiv.symm (by intro signature wire; rfl)
        rw [Region.renameWires_id, mappedResultEq] at renamed
        exact renamed
      let mappedBack : RegionIso commonEquiv formalResult
          (formalResult.renameWires commonEquiv.toRenaming) := by
        simpa only [Region.renameWires_id] using
          RegionIso.renameWires formalResult WireRenaming.id
            commonEquiv.toRenaming commonEquiv (by intro signature wire; rfl)
      let chained := (intoMapped.trans mappedBack).trans
        (RegionIso.adjoinAtNil formalResult)
      have ambientEq : (commonEquiv.symm.trans commonEquiv).trans
          (WireEquiv.refl itemCommon) = WireEquiv.refl itemCommon := by
        apply WireEquiv.ext
        intro signature wire
        exact commonEquiv.right_inv wire
      exact ⟨chained.castAmbient ambientEq⟩
    · dsimp only
      simp only [formalSites]
      let authoritativeFrame : Transform.Frame wires itemCommon
          itemSourceWires itemSourceWires := {
        sourceKeep := itemFrame.sourceKeep
        targetKeep := itemFrame.sourceKeep
        selected := itemFrame.selected
      }
      have editedEq :=
        atomFormalPrefixArgumentItemsEdit_source childFrame
          (authoritativeFrame.append []) hostItems formal retainedPorts
          mappedApplication (EqualityNormalization.formalPorts wires)
      change
        let direct := Region.singleton (.atom itemFrame.selected
          (application.map fun wire => itemFrame.sourceKeep wire))
        let authoritative := Region.adjoinAt [] .nil
          (Region.ofItems
            (argumentItemsEdit
              (atomFormalPrefixRecordingSites childFrame hostItems formal
                retainedPorts mappedApplication)
              (EqualityNormalization.formalPorts wires)
              (normalizationOperation wires)
              (authoritativeFrame.append []) PUnit.unit
              (fun _ _ _ => PUnit.unit)).1)
        HostedStrict direct authoritative ∧
          HostedScope direct authoritative
      rw [editedEq]
      let rawSubstitution :=
        EqualityNormalization.formalSubstitution application
      let targetSubstitution : WireRenaming wires itemSourceWires :=
        WireRenaming.comp itemFrame.sourceKeep rawSubstitution
      let direct := Region.singleton (.atom itemFrame.selected
        (application.map fun wire => itemFrame.sourceKeep wire))
      let supportPins := Region.ofItems
        ((supportAtomTail head ports).renameWires targetSubstitution)
      let pins := EqualityNormalization.allPins wires targetSubstitution
      let allPins := Region.ofItems (pins.append pins)
      let material := supportAtomMaterial head ports
      let supportRename : WireRenaming (wires ++ []) itemSourceWires :=
        WireRenaming.comp targetSubstitution
          (WireEquiv.appendNil wires).toRenaming
      have supportStep : HostedStrict (Region.blank itemSourceWires)
          supportPins := by
        have base : HostedStrict (Region.blank wires)
            (Region.ofItems (supportAtomTail head ports)) := by
          apply HostedStrict.specialize
            (HostedStrict.supportPins material
              (Erasure.Exposure.identityBoundary wires))
            (WireEquiv.appendNil wires).toRenaming
          · change (Region.blank (wires ++ [])).renameWires
                (WireEquiv.appendNil wires).toRenaming =
              Region.blank wires
            rfl
          · unfold material supportAtomMaterial
            rw [Region.ofItems_renameWires]
            simp [supportAtomTail, supportAtomPinsAppended,
              supportAtomMaterial] <;> rfl
        apply HostedStrict.specialize base targetSubstitution
        · rfl
        · unfold supportPins
          exact Region.ofItems_renameWires
            (supportAtomTail head ports) targetSubstitution
      have allPinsStep : HostedStrict (Region.blank itemSourceWires)
          allPins :=
        HostedStrict.allPinsTwice wires targetSubstitution
      let hostStep := HostedStrict.conjoin
        (Region.blank itemSourceWires) (Region.blank itemSourceWires)
        supportPins allPins supportStep allPinsStep
      let host := supportPins.conjoin allPins
      let hostFromBlank : HostedStrict (Region.blank itemSourceWires) host :=
        HostedStrict.iso (RegionIso.blankConjoin _).symm
          (RegionIso.refl host) hostStep
      let directHost := HostedStrict.conjoin direct
        (Region.blank itemSourceWires) direct host
        (HostedStrict.refl direct) hostFromBlank
      let directToHostDirect : HostedStrict direct (host.conjoin direct) :=
        HostedStrict.iso (RegionIso.conjoinBlank direct).symm
          (RegionIso.conjoinComm direct host) directHost
      let authoritativeSource :=
        (hostItems.renameWires
            (authoritativeFrame.append []).sourceKeep).append
          (.cons (.atom (authoritativeFrame.append []).selected
            ((EqualityNormalization.formalPorts wires).map fun wire =>
              (authoritativeFrame.append []).sourceKeep
                (EqualityNormalization.formalSubstitution mappedApplication
                  wire))) .nil)
      let child := Region.ofItems authoritativeSource
      have childDownEq :
          child.renameWires (WireEquiv.appendNil itemSourceWires).toRenaming =
            host.conjoin direct := by
        let down := (WireEquiv.appendNil itemSourceWires).toRenaming
        let downFrame : WireRenaming (itemCommon ++ []) itemSourceWires :=
          WireRenaming.comp down
            (authoritativeFrame.append []).sourceKeep
        have downFrameCommonEq : ∀ {signature}
            (wire : Var itemCommon signature),
            downFrame (commonAppend wire) = itemFrame.sourceKeep wire := by
          intro signature wire
          unfold downFrame down commonAppend authoritativeFrame
          rw [show commonEquiv.symm.toRenaming wire =
              wire.appendLeft [] by
            exact WireEquiv.appendNil_symm_apply itemCommon wire]
          simp [WireRenaming.comp, Transform.Frame.append,
            WireRenaming.appendRight, Var.appendMap_left,
            WireEquiv.appendNil_apply]
        have combinedSubstitutionEq :
            WireRenaming.comp downFrame substitution =
              targetSubstitution := by
          apply WireRenaming.ext
          intro signature wire
          change downFrame
              (EqualityNormalization.formalSubstitution mappedApplication
                wire) =
            itemFrame.sourceKeep
              (EqualityNormalization.formalSubstitution application wire)
          rw [EqualityNormalization.formalSubstitution_map
            application commonAppend wire]
          exact downFrameCommonEq _
        have selectedPortsEq :
            (EqualityNormalization.formalPorts wires).map (fun wire =>
              downFrame
                (EqualityNormalization.formalSubstitution mappedApplication
                  wire)) =
              application.map fun wire => itemFrame.sourceKeep wire := by
          calc
            _ = ((EqualityNormalization.formalPorts wires).map
                (fun wire =>
                  EqualityNormalization.formalSubstitution mappedApplication
                    wire)).map (fun wire => downFrame wire) := by
              rw [Vars.map_map]
            _ = mappedApplication.map (fun wire => downFrame wire) := by
              rw [EqualityNormalization.formalPorts_map_substitution]
            _ = application.map (fun wire => itemFrame.sourceKeep wire) := by
              unfold mappedApplication
              rw [Vars.map_map]
              apply Vars.map_congr
              intro signature wire
              exact downFrameCommonEq wire
        have selectedHeadEq :
            down ((authoritativeFrame.append []).selected) =
              itemFrame.selected := by
          unfold down authoritativeFrame
          simp [Transform.Frame.append, WireEquiv.appendNil_apply]
        have hostItemsDownEq :
            hostItems.renameWires downFrame =
              ((supportAtomTail head ports).renameWires
                  targetSubstitution).append
                (pins.append pins) := by
          unfold hostItems mappedPins pins
          simp only [ItemSeq.renameWires_append,
            ItemSeq.renameWires_comp,
            EqualityNormalization.allPins_renameWires]
          rw [combinedSubstitutionEq]
        unfold host supportPins allPins direct
        unfold child authoritativeSource pins
        rw [Region.ofItems_renameWires]
        rw [show Region.singleton
              (.atom itemFrame.selected
                (application.map fun wire => itemFrame.sourceKeep wire)) =
            Region.ofItems
              (.cons (.atom itemFrame.selected
                (application.map fun wire => itemFrame.sourceKeep wire))
                .nil) by rfl]
        rw [Region.ofItems_conjoin]
        rw [Region.ofItems_conjoin]
        apply congrArg Region.ofItems
        simp only [ItemSeq.renameWires_append, ItemSeq.renameWires,
          Item.renameWires, ItemSeq.renameWires_comp, Vars.map_map]
        change
          (hostItems.renameWires downFrame).append
              (.cons (.atom
                (down ((authoritativeFrame.append []).selected))
                ((EqualityNormalization.formalPorts wires).map fun wire =>
                  downFrame
                    (EqualityNormalization.formalSubstitution
                      mappedApplication wire))) .nil) =
            (((supportAtomTail head ports).renameWires
                targetSubstitution).append
              ((EqualityNormalization.allPins wires
                  targetSubstitution).append
                (EqualityNormalization.allPins wires
                  targetSubstitution))).append
              (.cons (.atom itemFrame.selected
                (application.map fun wire => itemFrame.sourceKeep wire)) .nil)
        rw [hostItemsDownEq, selectedHeadEq, selectedPortsEq]
      have supportPinsCanonical : supportPins.Canonical := by
        have baseCanonical :
            (Region.ofItems (supportAtomTail head ports)).Canonical := by
          constructor
          · intro localIndex
            exact Fin.elim0 localIndex
          · unfold supportAtomTail supportAtomPinsAppended
            exact (ItemSeq.ChildrenCanonical.renameWires_iff _ _).mpr
              ((ItemSeq.ChildrenCanonical.renameWires_iff _ _).mpr
                (Erasure.Exposure.supportPins_childrenCanonical
                  (supportAtomMaterial head ports)
                  (Erasure.Exposure.identityBoundary wires)))
        simpa only [supportPins, Region.ofItems_renameWires] using
          (Region.Canonical.renameWires_iff
            (Region.ofItems (supportAtomTail head ports))
            targetSubstitution).mpr baseCanonical
      have allPinsCanonical : allPins.Canonical := by
        constructor
        · intro localIndex
          exact Fin.elim0 localIndex
        · exact (ItemSeq.ChildrenCanonical.renameWires_iff _ _).mpr
            (EqualityNormalization.allPins_twice_childrenCanonical
              wires targetSubstitution)
      have hostCanonical : host.Canonical := by
        exact EqualityNormalization.canonical_conjoin supportPinsCanonical
          allPinsCanonical
      have directToHostDirectScope : HostedScope direct
          (host.conjoin direct) := by
        intro target rename
        let mappedApplication :=
          (application.map fun wire => itemFrame.sourceKeep wire).map
            (fun wire => rename wire)
        let mappedSubstitution : WireRenaming wires target :=
          EqualityNormalization.formalSubstitution mappedApplication
        have mappedSubstitutionEq : mappedSubstitution =
            WireRenaming.comp rename targetSubstitution := by
          apply WireRenaming.ext
          intro signature wire
          unfold mappedSubstitution mappedApplication targetSubstitution
            rawSubstitution
          calc
            _ = rename
                (EqualityNormalization.formalSubstitution
                  (application.map fun wire => itemFrame.sourceKeep wire)
                  wire) :=
              EqualityNormalization.formalSubstitution_map
                (application.map fun wire => itemFrame.sourceKeep wire)
                rename wire
            _ = rename
                (itemFrame.sourceKeep
                  (EqualityNormalization.formalSubstitution application
                    wire)) := by
              rw [EqualityNormalization.formalSubstitution_map]
            _ = _ := rfl
        have directRenameEq : direct.renameWires rename =
            Region.singleton (.atom (rename itemFrame.selected)
              mappedApplication) := by
          unfold direct mappedApplication
          simp only [Region.singleton_renameWires, Item.renameWires,
            Vars.map_map]
        have hostRenameCanonical : (host.renameWires rename).Canonical :=
          (Region.Canonical.renameWires_iff host rename).mpr hostCanonical
        have scopeProof : ScopePreservation
            (direct.renameWires rename)
            ((host.renameWires rename).conjoin
              (direct.renameWires rename)) :=
          ScopePreservation.hostLeft
            (direct.renameWires rename) (host.renameWires rename)
            hostRenameCanonical (by
              intro signature wire hostNonempty
              rw [directRenameEq]
              intro directEmpty
              let appendNil : WireRenaming target (target ++ []) :=
                ⟨fun selected => selected.appendLeft []⟩
              have mappedCountEq :
                  (mappedApplication.map fun selected =>
                    appendNil selected).countIndex wire.index.val =
                    mappedApplication.countIndex wire.index.val :=
                Vars.countIndex_map_of_sameIndex mappedApplication appendNil
                  (fun selected => Var.index_appendLeft selected [])
                  wire.index.val
              simp only [Region.singleton, Region.ofItems,
                Region.incidencePaths, ItemSeq.renameWires,
                Item.renameWires, ItemSeq.incidencePaths,
                Item.incidencePaths, List.append_nil,
                Var.index_appendLeft] at directEmpty
              rw [mappedCountEq] at directEmpty
              have countZero : mappedApplication.countIndex
                  wire.index.val = 0 := by
                have totalZero :
                    (if (rename itemFrame.selected).index.val =
                        wire.index.val then 1 else 0) +
                      mappedApplication.countIndex wire.index.val = 0 := by
                  simpa only [List.replicate_eq_nil_iff] using directEmpty
                omega
              have noPreimage : ∀ {sourceSignature}
                  (sourceWire : Var wires sourceSignature),
                  ((WireRenaming.comp rename targetSubstitution)
                      sourceWire).index.val ≠ wire.index.val := by
                intro sourceSignature sourceWire
                rw [← mappedSubstitutionEq]
                exact EqualityNormalization.formalSubstitution_index_ne_of_countIndex_eq_zero
                  mappedApplication wire countZero sourceWire
              have supportEmpty :
                  (supportPins.renameWires rename).incidencePaths
                    wire.index.val = [] := by
                unfold supportPins
                rw [Region.ofItems_renameWires,
                  ItemSeq.renameWires_comp, Region.incidencePaths_ofItems]
                exact ItemSeq.incidencePaths_renameWires_eq_nil_of_no_preimage
                  (supportAtomTail head ports)
                  (WireRenaming.comp rename targetSubstitution)
                  wire.index.val 0 wire.index.isLt noPreimage
              have firstPinsEmpty :
                  (EqualityNormalization.allPins wires mappedSubstitution
                    ).incidencePaths wire.index.val 0 = [] := by
                exact ItemSeq.pinWires_incidence_eq_nil_of wires
                  mappedSubstitution (fun _ => true) wire.index.val 0
                  (fun sourceWire _ =>
                    EqualityNormalization.formalSubstitution_index_ne_of_countIndex_eq_zero
                      mappedApplication wire countZero sourceWire)
              have secondPinsEmpty :
                  (EqualityNormalization.allPins wires mappedSubstitution
                    ).incidencePaths wire.index.val
                      (EqualityNormalization.allPins wires
                        mappedSubstitution).length = [] := by
                exact ItemSeq.pinWires_incidence_eq_nil_of wires
                  mappedSubstitution (fun _ => true) wire.index.val
                  (EqualityNormalization.allPins wires
                    mappedSubstitution).length
                  (fun sourceWire _ =>
                    EqualityNormalization.formalSubstitution_index_ne_of_countIndex_eq_zero
                      mappedApplication wire countZero sourceWire)
              have allPinsEmpty :
                  (allPins.renameWires rename).incidencePaths
                    wire.index.val = [] := by
                rw [mappedSubstitutionEq] at firstPinsEmpty secondPinsEmpty
                unfold allPins pins
                rw [Region.ofItems_renameWires,
                  ItemSeq.renameWires_append,
                  EqualityNormalization.allPins_renameWires,
                  Region.incidencePaths_ofItems,
                  ItemSeq.incidencePaths_append, firstPinsEmpty]
                simpa only [List.nil_append, Nat.zero_add] using
                  secondPinsEmpty
              unfold host at hostNonempty
              rw [Region.renameWires_conjoin,
                Region.incidencePaths_conjoin, supportEmpty, allPinsEmpty]
                at hostNonempty
              exact hostNonempty (by simp))
        simpa only [Region.renameWires_conjoin] using scopeProof
      let targetPresentation :=
        (RegionIso.ofEq childDownEq).symm.trans
          (RegionIso.adjoinAtNil child)
      exact ⟨HostedStrict.iso (RegionIso.refl direct)
          targetPresentation directToHostDirect, by
        intro target rename
        exact (directToHostDirectScope rename).trans
          ((HostedScope.ofIso targetPresentation) rename)⟩

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
      (VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
        (pattern := pattern) (retain := itemFrame.sourceKeep)
        (selected := itemFrame.selected) application)
      (ItemSites.selectedAtom (operation := itemOperation)
        (pattern := pattern) (frame := itemFrame) application siteData)
      (Leaf.Identity.Vars.fromFn ports) formalFrame PUnit.unit
      (fun retained _formalSource formalResult formalEvidence formalSites
          _coherence =>
        ∃ staged : Region itemCommon,
          HostedStrict
              (VisualProof.Rule.Comprehension.Instantiation.instantiate
                pattern application) staged ∧
            ScopePreservation
                (VisualProof.Rule.Comprehension.Instantiation.instantiate
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
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern application) staged := by
    intro outer hostLocals rename outerHostItems boundary source
      hostedOccurrence targetCanonical targetExternalTwoEnded
    let mappedApplication := application.map fun wire => rename wire
    let sourceBefore :=
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern application).renameWires rename
    let sourceAfter :=
      VisualProof.Rule.Comprehension.Instantiation.instantiate
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
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern application) outputStaged := by
    intro outer hostLocals rename outerHostItems boundary source
      hostedOccurrence targetCanonical targetExternalTwoEnded
    let mappedApplication := application.map fun wire => rename wire
    let sourceAfter :=
      VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern mappedApplication
    let sourceHostAfter := Region.adjoinAt hostLocals outerHostItems sourceAfter
    have sourceHostEq :
        Region.adjoinAt hostLocals outerHostItems
            ((VisualProof.Rule.Comprehension.Instantiation.instantiate
              pattern application).renameWires rename) = sourceHostAfter := by
      simp only [sourceHostAfter, sourceAfter, mappedApplication,
        EqualityNormalization.instantiate_renameWires]
    change Occurrence
      (Region.adjoinAt hostLocals outerHostItems
        ((VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern application).renameWires rename)) source at hostedOccurrence
    have sourceAfterCanonical : sourceHostAfter.Canonical := by
      rw [← sourceHostEq]
      exact hostedOccurrence.context.holeCanonical _
        hostedOccurrence.sourceCanonical
    have sourceNonempty : ∀ {wireSignature} (wire : Var outer wireSignature),
        (Region.adjoinAt hostLocals outerHostItems
          ((VisualProof.Rule.Comprehension.Instantiation.instantiate
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
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        (positionalIdentityPattern signature arity) retained) := {
    canonical := fun _ =>
      VisualProof.Rule.Comprehension.Instantiation.instantiate_canonical
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
    VisualProof.Rule.Comprehension.Instantiation.instantiate
      (positionalIdentityPattern signature arity) retained
  have stagedScope : ScopePreservation
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern application) staged := by
    let directScope : ScopePreservation
        (VisualProof.Rule.Comprehension.Instantiation.instantiate
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
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
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
        VisualProof.Rule.Comprehension.Instantiation.RegionResult
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
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern ports)
          (operation.site siteFrame siteData ports site) ∧
        ScopePreservation
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
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
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult
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
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern ports)
          (operation.site siteFrame siteData ports site) ∧
        ScopePreservation
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
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
        VisualProof.Rule.Comprehension.Instantiation.ItemResult
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
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern ports)
          (operation.site siteFrame siteData ports site) ∧
        ScopePreservation
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
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
    | term output freeArity ports term =>
        have outputEq : frame.targetKeep output = output := by
          rw [targetKeepEq]
          rfl
        have portsEq : (fun index => frame.targetKeep (ports index)) = ports := by
          funext index
          rw [targetKeepEq]
          rfl
        simpa only [itemEdit, ExactEdit.refl, Transform.ItemEdit.run,
          outputEq, portsEq] using
          And.intro
            (HostedStrict.refl
              (Region.singleton (.term output freeArity ports term)))
            (ScopePreservation.refl
              (Region.singleton (.term output freeArity ports term)))
    | cut childSites =>
        obtain ⟨childHosted, childScope⟩ :=
          leafRegionEndpoint _ childSites targetKeepEq selected
        exact ⟨HostedStrict.cut _ _ childHosted,
          ScopePreservation.cut childScope⟩
  termination_by sizeOf source
end

mutual
  /-- Reverse leaf scope for a region, stable under inherited-wire
  renaming. -/
  theorem leafRegionReverseHostedScope
      {arguments common sourceWires : List Sig}
      {pattern : OpenDiagram arguments}
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires common}
      {data : operation.Data frame}
      {source : Region sourceWires} {result : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.RegionResult
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
        HostedScope
          (operation.site siteFrame siteData ports site)
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern ports)) :
      HostedScope (regionEdit data evidence sites).endpoint result := by
    intro target rename
    cases sites with
    | @mk _ _ _ _ _ _ locals _ _ _ childSites =>
        have childTargetKeep : (frame.append locals).targetKeep =
            WireRenaming.id := by
          apply WireRenaming.ext
          intro signature wire
          change frame.targetKeep.appendRight locals wire = wire
          rw [targetKeepEq]
          exact WireRenaming.appendRight_id_apply locals wire
        have childScope :=
          leafItemsReverseHostedScope _ childSites childTargetKeep selected
            (rename.appendRight locals)
        have lifted :=
          adjoinAt_preserves_scope locals .nil _ _ childScope
        simpa only [regionEdit, Region.renameWires_adjoinAt_nil] using lifted
  termination_by sizeOf source

  /-- Reverse leaf scope for an item sequence, stable under inherited-wire
  renaming. -/
  theorem leafItemsReverseHostedScope
      {arguments common sourceWires : List Sig}
      {pattern : OpenDiagram arguments}
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires common}
      {data : operation.Data frame}
      {source : ItemSeq sourceWires} {result : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult
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
        HostedScope
          (operation.site siteFrame siteData ports site)
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern ports)) :
      HostedScope (itemsEdit data evidence sites).endpoint result := by
    intro target rename
    cases sites with
    | nil _ =>
        exact ScopePreservation.refl _
    | cons itemSites tailSites =>
        have itemScope :=
          leafItemReverseHostedScope _ itemSites targetKeepEq selected rename
        have tailScope :=
          leafItemsReverseHostedScope _ tailSites targetKeepEq selected rename
        simpa only [itemsEdit, Region.renameWires_conjoin] using
          ScopePreservation.conjoin itemScope tailScope
  termination_by sizeOf source

  /-- Reverse leaf scope for one item, stable under inherited-wire
  renaming. -/
  theorem leafItemReverseHostedScope
      {arguments common sourceWires : List Sig}
      {pattern : OpenDiagram arguments}
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires common}
      {data : operation.Data frame}
      {source : Item sourceWires} {result : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemResult
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
        HostedScope
          (operation.site siteFrame siteData ports site)
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern ports)) :
      HostedScope (itemEdit data evidence sites).endpoint result := by
    intro target rename
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
          ScopePreservation.refl
            ((Region.singleton (.atom head ports)).renameWires rename)
    | selectedAtom ports site =>
        simpa only [itemEdit, ExactEdit.refl] using
          selected targetKeepEq ports site rename
    | identity signature arity ports =>
        have portsEq : (fun index => frame.targetKeep (ports index)) = ports := by
          funext index
          rw [targetKeepEq]
          rfl
        simpa only [itemEdit, ExactEdit.refl, Transform.ItemEdit.run,
          portsEq] using
          ScopePreservation.refl
            ((Region.singleton (.identity signature arity ports)
              ).renameWires rename)
    | term output freeArity ports term =>
        have outputEq : frame.targetKeep output = output := by
          rw [targetKeepEq]
          rfl
        have portsEq : (fun index => frame.targetKeep (ports index)) = ports := by
          funext index
          rw [targetKeepEq]
          rfl
        simpa only [itemEdit, ExactEdit.refl, Transform.ItemEdit.run,
          outputEq, portsEq] using
          ScopePreservation.refl
            ((Region.singleton (.term output freeArity ports term)
              ).renameWires rename)
    | cut childSites =>
        have childScope :=
          leafRegionReverseHostedScope _ childSites targetKeepEq selected rename
        simpa only [itemEdit, Region.singleton_renameWires,
          Item.renameWires] using
          ScopePreservation.cut childScope
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
        (VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalIdentityPattern signature arity) application)
        ((recordingOperation
          (Leaf.Identity.operation signature arity) originalArguments).site
            frame PUnit.unit application site) ∧
      ScopePreservation
        (VisualProof.Rule.Comprehension.Instantiation.instantiate
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
    VisualProof.Rule.Comprehension.Instantiation.instantiate
      (positionalIdentityPattern signature arity) mappedApplication
  let direct := positionalIdentityApplication signature arity
    mappedApplication
  let sourceBefore := Region.adjoinAt hostLocals hostItems
    ((VisualProof.Rule.Comprehension.Instantiation.instantiate
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
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            (positionalAtomPattern atomArguments) (.cons formal retained)))).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill
        (Region.adjoinAt hostLocals hostItems
          (VisualProof.Rule.Comprehension.Instantiation.instantiate
            (positionalAtomPattern atomArguments) (.cons formal retained))))) :
    EqualityNormalization.StrictEquates occurrence
      (Region.adjoinAt hostLocals hostItems
        (VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalAtomPattern atomArguments) (.cons formal retained)))
      targetCanonical targetExternalTwoEnded := by
  let description : Rule.UncappedErasure.Description outer := {
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
        (VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalAtomPattern atomArguments) application)
        ((recordingOperation
          (Leaf.Formal.operation [] atomArguments) originalArguments).site
            frame PUnit.unit application site) ∧
      ScopePreservation
        (VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalAtomPattern atomArguments) application)
        ((recordingOperation
          (Leaf.Formal.operation [] atomArguments) originalArguments).site
            frame PUnit.unit application site) ∧
      HostedScope
        ((recordingOperation
          (Leaf.Formal.operation [] atomArguments) originalArguments).site
            frame PUnit.unit application site)
        (VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalAtomPattern atomArguments) application) := by
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
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        (positionalAtomPattern atomArguments) (.cons formal retained)) := by
    simpa only [List.nil_append] using
      positionalAtomInstantiation_scope formal retained
  have reverseScope : ScopePreservation
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
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
  have directHostedScope : HostedScope
      (Region.singleton (.atom formal retained))
      (VisualProof.Rule.Comprehension.Instantiation.instantiate
        (positionalAtomPattern atomArguments) (.cons formal retained)) := by
    intro target rename
    let mappedFormal := rename formal
    let mappedRetained := retained.map fun wire => rename wire
    have directEq :
        (Region.singleton (.atom formal retained)).renameWires rename =
          Region.singleton (.atom mappedFormal mappedRetained) := by
      simp [mappedFormal, mappedRetained, Region.singleton_renameWires,
        Item.renameWires]
    have instantiatedEq :
        (VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalAtomPattern atomArguments) (.cons formal retained)
          ).renameWires rename =
        VisualProof.Rule.Comprehension.Instantiation.instantiate
          (positionalAtomPattern atomArguments)
          (.cons mappedFormal mappedRetained) := by
      simpa only [mappedFormal, mappedRetained, Theory.Vars.map] using
        EqualityNormalization.instantiate_renameWires
          (positionalAtomPattern atomArguments) (.cons formal retained) rename
    rw [directEq, instantiatedEq]
    simpa only [List.nil_append] using
      positionalAtomInstantiation_scope mappedFormal mappedRetained
  refine ⟨?_, reverseScope, directHostedScope⟩
  intro outer hostLocals rename hostItems boundary source occurrence
    targetCanonical targetExternalTwoEnded
  let mappedFormal := rename formal
  let mappedRetained := retained.map fun wire => rename wire
  let mappedApplication : Vars (outer ++ hostLocals)
      (positionalAtomWires atomArguments) :=
    .cons mappedFormal mappedRetained
  let sourceBefore := Region.adjoinAt hostLocals hostItems
    ((VisualProof.Rule.Comprehension.Instantiation.instantiate
      (positionalAtomPattern atomArguments) (.cons formal retained)
      ).renameWires rename)
  let sourceAfter := Region.adjoinAt hostLocals hostItems
    (VisualProof.Rule.Comprehension.Instantiation.instantiate
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
