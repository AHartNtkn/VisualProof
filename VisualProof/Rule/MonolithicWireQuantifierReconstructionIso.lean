import VisualProof.Rule.MonolithicWireQuantifierReconstruction

namespace VisualProof

universe u

namespace MonolithicWireQuantifier

namespace Internal

/-- The reconstruction fold owns both the partial carrier state and the exact
unconsumed suffix of sever-generated relation atoms. -/
structure BatchReconstructionTraceState
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {sites : List (ConcreteWireQuantifier.RelationSeverSite source)}
    (result : ConcreteWireQuantifier.RelationSeverResult source scope sites)
    (contents : List (ContentOccurrence source pattern))
    {steps : List (ConcreteWireQuantifier.RelationJoinStep
      result.checked result.relationWire pattern)}
    (current : CheckedDiagram definitions)
    (nodeImage : result.checked.val.NodeId → Option current.val.NodeId)
    (currentDying : current.val.WireId) where
  state : BatchReconstructionState sites contents current result.checked
  pendingOriginsExact :
    state.pendingOrigins = result.atoms.drop steps.length
  joinNodeImageExact : HEq state.joinNodeImage nodeImage
  representedWiresAvoidDying :
    ∀ wire, state.wireImage wire ≠ currentDying

theorem relationJoinTrace_wireImage_val
    (trace : ConcreteWireQuantifier.RelationJoinSemanticTrace
      source dying pattern parameters args steps final regionImage nodeImage
        wireImage finalDying finalScope) :
    ∀ wire, (wireImage wire).val = wire.val := by
  induction trace with
  | nil => intro wire; rfl
  | snoc trace step priorExact priorRegionExact priorNodeExact priorWireExact
      priorDyingExact priorScopeExact relationArgsExact sourceParametersExact
      induction =>
      cases priorExact
      intro wire
      rw [step.checkedWireImageExact, step.baseWireImageExact]
      change (step.priorWireImage wire).val = wire.val
      have imagesExact := eq_of_heq priorWireExact
      rw [imagesExact]
      exact induction wire

/-- Structural fold of the accepted inverse trace.  Its only list premises
state that the restored occurrence prefix and consumed application prefix
have the same length and order as the trace itself. -/
theorem batchReconstructionTraceFold_exists
    {source : CheckedDiagram definitions}
    {pattern : CheckedOpenDiagram definitions}
    {scope : source.val.RegionId}
    {sites : List (ConcreteWireQuantifier.RelationSeverSite source)}
    (result : ConcreteWireQuantifier.RelationSeverResult source scope sites)
    (allContents : List (ContentOccurrence source pattern))
    (first : ContentOccurrence source pattern)
    (entries : CheckedOccurrenceList scope first allContents)
    (sitesExact : sites = allContents.map ContentOccurrence.toConcreteSite)
    (parameters : List result.checked.val.WireId)
    (parametersAccepted : first.parameters.mapM result.wireImage? =
      some parameters)
    (args : List Sig)
    (relationSignature :
      (result.checked.val.wires result.relationWire).sig = .rel args)
    {steps : List (ConcreteWireQuantifier.RelationJoinStep
      result.checked result.relationWire pattern)}
    {current : CheckedDiagram definitions}
    {regionImage : result.checked.val.RegionId → current.val.RegionId}
    {nodeImage : result.checked.val.NodeId → Option current.val.NodeId}
    {wireImage : result.checked.val.WireId → current.val.WireId}
    {currentDying : current.val.WireId}
    {currentScope : current.val.RegionId}
    (trace : ConcreteWireQuantifier.RelationJoinSemanticTrace
      result.checked result.relationWire pattern parameters args steps current
        regionImage nodeImage wireImage currentDying currentScope)
    (contents : List (ContentOccurrence source pattern))
    (suffix : List (ContentOccurrence source pattern))
    (allContentsDecomposition : allContents = contents ++ suffix)
    (contentsLength : contents.length = steps.length)
    (applicationsExact :
      steps.map ConcreteWireQuantifier.RelationJoinStep.application =
        result.atoms.take steps.length) :
    Nonempty
      (BatchReconstructionTraceState (steps := steps) result contents current
        nodeImage currentDying) := by
  induction trace generalizing contents suffix with
  | nil =>
      have contentsEmpty : contents = [] :=
        List.eq_nil_of_length_eq_zero (by simpa using contentsLength)
      subst contents
      exact ⟨
        { state := batchReconstructionNil result
          pendingOriginsExact := by simp [batchReconstructionNil]
          joinNodeImageExact := by rfl
          representedWiresAvoidDying := by
            intro wire same
            have values := congrArg Fin.val same
            simp [batchReconstructionNil] at values
            have bound :=
              (ConcreteWireQuantifier.Internal.retainedWireIndex source
                (sites.flatMap
                  ConcreteWireQuantifier.RelationSeverSite.removedWires)
                wire.1 (by
                  exact (result.retainedWire_iff wire.1).mpr (by
                    simpa [BatchCoveredWire, restoredWire,
                      retainedBySitesWire] using wire.2))).isLt
            omega }⟩
  | @snoc priorSteps priorCurrent priorRegionImage priorNodeImage
      priorWireImage priorDying priorScope trace step priorExact
      priorRegionExact priorNodeExact priorWireExact priorDyingExact
      priorScopeExact relationArgsExact sourceParametersExact induction =>
      cases priorExact
      have contentsNonempty : contents ≠ [] := by
        intro contentsEmpty
        subst contents
        simp at contentsLength
      let prefixContents := contents.dropLast
      let content := contents.getLast contentsNonempty
      have contentsDecomposition : prefixContents ++ [content] = contents := by
        exact List.dropLast_concat_getLast contentsNonempty
      have prefixLength : prefixContents.length = priorSteps.length := by
        have finalLength : contents.length = priorSteps.length + 1 := by
          simpa using contentsLength
        simp [prefixContents, finalLength]
      have prefixApplicationsExact :
          priorSteps.map
              ConcreteWireQuantifier.RelationJoinStep.application =
            result.atoms.take priorSteps.length := by
        have restricted := congrArg (List.take priorSteps.length)
          applicationsExact
        simpa [List.map_append, List.take_take,
          Nat.min_eq_left (Nat.le_succ priorSteps.length)] using restricted
      obtain ⟨priorState⟩ :=
        induction prefixContents (content :: suffix) (by
          calc
            allContents = contents ++ suffix := allContentsDecomposition
            _ = (prefixContents ++ [content]) ++ suffix := by
              rw [contentsDecomposition]
            _ = prefixContents ++ content :: suffix := by simp)
          prefixLength prefixApplicationsExact
      have atomsDecomposition :
          result.atoms =
            (priorSteps.map
                ConcreteWireQuantifier.RelationJoinStep.application ++
              [step.application]) ++
              result.atoms.drop (priorSteps.length + 1) := by
        calc
          result.atoms =
              result.atoms.take (priorSteps.length + 1) ++
                result.atoms.drop (priorSteps.length + 1) := by
            exact (List.take_append_drop (priorSteps.length + 1)
              result.atoms).symm
          _ =
              (priorSteps.map
                  ConcreteWireQuantifier.RelationJoinStep.application ++
                [step.application]) ++
                result.atoms.drop (priorSteps.length + 1) := by
            have fullApplications :
                priorSteps.map
                    ConcreteWireQuantifier.RelationJoinStep.application ++
                  [step.application] =
                result.atoms.take (priorSteps.length + 1) := by
              simpa [List.map_append] using applicationsExact
            rw [← fullApplications]
      have pendingHead :
          result.atoms.drop priorSteps.length =
            step.application ::
              result.atoms.drop (priorSteps.length + 1) := by
        calc
          result.atoms.drop priorSteps.length =
              ((priorSteps.map
                    ConcreteWireQuantifier.RelationJoinStep.application ++
                  [step.application]) ++
                result.atoms.drop (priorSteps.length + 1)).drop
                  priorSteps.length :=
            congrArg (List.drop priorSteps.length) atomsDecomposition
          _ = step.application ::
              result.atoms.drop (priorSteps.length + 1) := by simp
      have priorNodeStateExact :
          HEq step.priorNodeImage priorState.state.joinNodeImage :=
        priorNodeExact.trans priorState.joinNodeImageExact.symm
      have currentAllDecomposition :
          allContents = prefixContents ++ content :: suffix := by
        calc
          allContents = contents ++ suffix := allContentsDecomposition
          _ = (prefixContents ++ [content]) ++ suffix := by
            rw [contentsDecomposition]
          _ = prefixContents ++ content :: suffix := by simp
      have freshRegionsNew :
          ∀ region, region ≠ pattern.val.diagram.root →
            ¬ BatchCoveredRegion sites prefixContents
              (content.occurrence.regionMap region) :=
        properRegion_not_covered_before result entries sitesExact content
          suffix currentAllDecomposition
      have freshNodesNew :
          ∀ node, ¬ BatchCoveredNode sites prefixContents
            (content.occurrence.nodeMap node) :=
        nodeImage_not_covered_before result entries sitesExact content suffix
          currentAllDecomposition
      have freshWiresNew :
          ∀ wire, wire ∉ pattern.val.boundary →
            ¬ BatchCoveredWire sites prefixContents
              (content.occurrence.wireMap wire) :=
        internalWireImage_not_covered_before result entries sitesExact content
          suffix currentAllDecomposition
      have contentMember : content ∈ allContents := by
        rw [currentAllDecomposition]
        simp
      have positionLtSites : priorSteps.length < sites.length := by
        have lengths := congrArg List.length sitesExact
        rw [currentAllDecomposition] at lengths
        simp at lengths
        omega
      let site : Fin sites.length :=
        ⟨priorSteps.length, positionLtSites⟩
      have siteExact : sites.get site = content.toConcreteSite := by
        have atPosition := congrArg
          (fun candidates => candidates[priorSteps.length]?) sitesExact
        rw [currentAllDecomposition] at atPosition
        change sites[priorSteps.length]? =
          ((prefixContents ++ content :: suffix).map
            ContentOccurrence.toConcreteSite)[priorSteps.length]?
            at atPosition
        have leftAt : sites[priorSteps.length]? = some (sites.get site) := by
          simp [List.getElem?_eq_getElem, positionLtSites, site]
        have rightAt :
            ((prefixContents ++ content :: suffix).map
              ContentOccurrence.toConcreteSite)[priorSteps.length]? =
              some content.toConcreteSite := by
          simp [prefixLength]
        rw [leftAt, rightAt] at atPosition
        exact Option.some.inj atPosition
      have applicationExact : step.application = result.atom site := by
        have atPosition := congrArg
          (fun applications => applications[priorSteps.length]?)
          applicationsExact
        simpa [List.map_append, site,
          ConcreteWireQuantifier.RelationSeverResult.atoms,
          Data.Finite.allFin_eq_finRange, positionLtSites] using atPosition
      obtain ⟨contentPosition, contentPositionExact⟩ :=
        List.get_of_mem contentMember
      let checkedContent : CheckedOccurrence scope first content :=
        contentPositionExact ▸ entries.get contentPosition
      have siteArgumentsExact :
          (sites.get site).formals.map
              (fun wire => (source.val.wires wire).sig) = args := by
        apply Sig.rel.inj
        calc
          .rel ((sites.get site).formals.map
              (fun wire => (source.val.wires wire).sig)) =
              (result.checked.val.wires result.relationWire).sig := by
            rw [result.site_formal_signatures site,
              result.relationWire_signature]
          _ = .rel args := relationSignature
      have arityExact :
          (sites.get site).formals.length = step.relationArgs.length := by
        calc
          (sites.get site).formals.length =
              ((sites.get site).formals.map
                (fun wire => (source.val.wires wire).sig)).length := by simp
          _ = args.length := congrArg List.length siteArgumentsExact
          _ = step.relationArgs.length :=
            congrArg List.length relationArgsExact.symm
      let alignment := inverseStepOccurrenceAlignmentOfChecked result first
        content checkedContent parameters parametersAccepted step site
        siteExact applicationExact arityExact sourceParametersExact
      have priorWireVal :
          ∀ wire, (step.priorWireImage wire).val = wire.val := by
        intro wire
        have imagesExact := eq_of_heq priorWireExact
        rw [imagesExact]
        exact relationJoinTrace_wireImage_val trace wire
      have boundaryRetained :
          ∀ position : Fin pattern.val.boundary.length,
            retainedBySitesWire sites
              (content.occurrence.wireMap
                (pattern.val.boundary.get position)) := by
        intro position
        exact (result.retainedWire_iff _).mp
          (alignment.boundarySurvives position)
      have boundaryWireExact :
          ∀ position : Fin pattern.val.boundary.length,
            step.checkedFragmentWire (pattern.val.boundary.get position) =
              step.checkedPriorWire
                (priorState.state.wireImage
                  ⟨content.occurrence.wireMap
                      (pattern.val.boundary.get position),
                    Or.inl (boundaryRetained position)⟩) := by
        intro position
        apply Fin.ext
        let representative := DenseList.index pattern.val.boundary
          (pattern.val.boundary.get position)
            (List.get_mem pattern.val.boundary position)
        have representativeGet :
            pattern.val.boundary.get representative =
              pattern.val.boundary.get position :=
          DenseList.get_index _ _ _
        have attachmentAt := alignment.sourceAttachmentExact representative
        let originalWire := content.occurrence.wireMap
          (pattern.val.boundary.get position)
        have originalSurvives : originalWire ∈
            ConcreteWireQuantifier.Internal.retainedWires source
              (sites.flatMap
                ConcreteWireQuantifier.RelationSeverSite.removedWires) := by
          unfold originalWire
          rw [← representativeGet]
          exact alignment.boundarySurvives representative
        have attachmentVal :
            (step.sourceAttachments.get
              (Fin.cast step.sourceAttachmentArity.symm representative)).val =
              (ConcreteWireQuantifier.Internal.retainedWireIndex source
                (sites.flatMap
                  ConcreteWireQuantifier.RelationSeverSite.removedWires)
                originalWire originalSurvives).val := by
          calc
            (step.sourceAttachments.get
                (Fin.cast step.sourceAttachmentArity.symm representative)).val =
                (result.wireImage
                  (content.occurrence.wireMap
                    (pattern.val.boundary.get representative))
                  (alignment.boundarySurvives representative)).val :=
              congrArg Fin.val attachmentAt
            _ = (ConcreteWireQuantifier.Internal.retainedWireIndex source
                  (sites.flatMap
                    ConcreteWireQuantifier.RelationSeverSite.removedWires)
                  (content.occurrence.wireMap
                    (pattern.val.boundary.get representative))
                  (alignment.boundarySurvives representative)).val :=
              result.wireImage_val _ _
            _ = (ConcreteWireQuantifier.Internal.retainedWireIndex source
                  (sites.flatMap
                    ConcreteWireQuantifier.RelationSeverSite.removedWires)
                  originalWire
                  originalSurvives).val := by
              congr 2
              exact congrArg content.occurrence.wireMap representativeGet
        calc
          (step.checkedFragmentWire
              (pattern.val.boundary.get position)).val =
              (step.sourceAttachments.get
                (Fin.cast step.sourceAttachmentArity.symm representative)).val := by
            simp [ConcreteWireQuantifier.RelationJoinStep.checkedFragmentWire,
              ConcreteSpliceAttachment.fragmentWire,
              ConcreteSpliceAttachment.representativeTarget,
              ConcreteSpliceAttachment.representativePosition,
              representative, step.targetExact]
            rw [step.baseWireImageExact]
            exact priorWireVal _
          _ = (ConcreteWireQuantifier.Internal.retainedWireIndex source
                (sites.flatMap
                  ConcreteWireQuantifier.RelationSeverSite.removedWires)
                originalWire
                originalSurvives).val :=
            attachmentVal
          _ = (priorState.state.wireImage
                ⟨originalWire, Or.inl (boundaryRetained position)⟩).val := by
            symm
            exact priorState.state.retainedWireImage_val originalWire
              (boundaryRetained position)
          _ = (step.checkedPriorWire
                (priorState.state.wireImage
                  ⟨originalWire, Or.inl (boundaryRetained position)⟩)).val := by
            rw [step.checkedPriorWire_val]
      have rootRetainedMember :
          content.occurrence.regionMap pattern.val.diagram.root ∈
            ConcreteWireQuantifier.Internal.retainedRegions source
              (sites.flatMap
                ConcreteWireQuantifier.RelationSeverSite.removedRegions) := by
        have retained := result.siteRegion_survives site
        rw [siteExact] at retained
        have regionExact :=
          entries.occurrenceRegion_eq_selectionRegion content contentMember
        simpa [Occurrence.maps_root, regionExact] using retained
      have rootRetained :
          retainedBySitesRegion sites
            (content.occurrence.regionMap pattern.val.diagram.root) :=
        (result.retainedRegion_iff _).mp rootRetainedMember
      have rootCovered :
          BatchCoveredRegion sites prefixContents
            (content.occurrence.regionMap pattern.val.diagram.root) :=
        Or.inl rootRetained
      let next := batchReconstructionSnoc priorState.state content step
        rfl priorNodeStateExact
        (result.atoms.drop (priorSteps.length + 1)) (by
          rw [priorState.pendingOriginsExact, pendingHead])
        freshRegionsNew freshNodesNew freshWiresNew boundaryRetained
          boundaryWireExact rootCovered (by
          apply Fin.ext
          have sourceRegionExact :
              step.sourceRegion =
                result.regionImage
                  (content.occurrence.regionMap
                    pattern.val.diagram.root) rootRetainedMember := by
            have sameNode := step.sourceNodeExact
            rw [applicationExact, result.atom_generated] at sameNode
            have regionExact :=
              entries.occurrenceRegion_eq_selectionRegion content contentMember
            have siteRegionExact :
                (sites.get site).region =
                  content.occurrence.regionMap pattern.val.diagram.root := by
              have selectedRegionExact := congrArg
                ConcreteWireQuantifier.RelationSeverSite.region siteExact
              change (sites.get site).region = content.selection.region
                at selectedRegionExact
              simpa [Occurrence.maps_root, regionExact] using
                selectedRegionExact
            have siteRetainedMember := result.siteRegion_survives site
            have sourceFromSite :
                step.sourceRegion =
                  result.regionImage (sites.get site).region
                    siteRetainedMember := by
              simpa using (CNode.atom.inj sameNode).1.symm
            have regionImage_congr :
                ∀ (left right : source.val.RegionId)
                  (leftMember : left ∈
                    ConcreteWireQuantifier.Internal.retainedRegions source
                      (sites.flatMap
                        ConcreteWireQuantifier.RelationSeverSite.removedRegions))
                  (rightMember : right ∈
                    ConcreteWireQuantifier.Internal.retainedRegions source
                      (sites.flatMap
                        ConcreteWireQuantifier.RelationSeverSite.removedRegions)),
                  left = right →
                    result.regionImage left leftMember =
                      result.regionImage right rightMember := by
              intro left right leftMember rightMember same
              subst right
              rfl
            exact sourceFromSite.trans
              (regionImage_congr _ _ siteRetainedMember rootRetainedMember
                siteRegionExact)
          change
            (step.checkedFragmentRegion pattern.val.diagram.root).val =
              (step.checkedPriorRegion
                (priorState.state.regionImage
                  ⟨content.occurrence.regionMap pattern.val.diagram.root,
                    rootCovered⟩)).val
          rw [step.checkedPriorRegion_val]
          calc
            (step.checkedFragmentRegion pattern.val.diagram.root).val =
                step.site.val := by
              simp [ConcreteWireQuantifier.RelationJoinStep.checkedFragmentRegion,
                ConcreteSpliceAttachment.fragmentRegion,
                ConcreteSpliceAttachment.hostRegion]
            _ = (step.baseRegionImage step.sourceRegion).val := by
              rw [step.siteExact]
            _ = (step.priorRegionImage step.sourceRegion).val := by
              rw [step.baseRegionImageExact]
              rfl
            _ = step.sourceRegion.val := step.priorRegionImageVal _
            _ = (result.regionImage
                  (content.occurrence.regionMap pattern.val.diagram.root)
                  rootRetainedMember).val := congrArg Fin.val sourceRegionExact
            _ = (ConcreteWireQuantifier.Internal.retainedRegionIndex source
                  (sites.flatMap
                    ConcreteWireQuantifier.RelationSeverSite.removedRegions)
                  (content.occurrence.regionMap pattern.val.diagram.root)
                  rootRetainedMember).val :=
              result.regionImage_val _ rootRetainedMember
            _ = (priorState.state.regionImage
                  ⟨content.occurrence.regionMap pattern.val.diagram.root,
                    rootCovered⟩).val := by
              symm
              exact priorState.state.retainedRegionImage_val _ rootRetained)
      have nextPending :
          next.pendingOrigins =
            result.atoms.drop (priorSteps ++ [step]).length := by
        dsimp [next, batchReconstructionSnoc]
        simp
      exact ⟨contentsDecomposition ▸
        { state := next
          pendingOriginsExact := nextPending
          joinNodeImageExact := by
            dsimp [next, batchReconstructionSnoc]
            exact HEq.rfl
          representedWiresAvoidDying := by
            intro wire same
            by_cases old : BatchCoveredWire sites prefixContents wire.1
            · have priorDyingEq :
                  step.priorWireImage result.relationWire = priorDying :=
                eq_of_heq priorDyingExact
              have priorImageEq :
                  step.checkedPriorWire (priorState.state.wireImage
                      ⟨wire.1, old⟩) =
                    step.checkedPriorWire
                      (step.priorWireImage result.relationWire) := by
                simpa [next, batchReconstructionSnoc, old,
                  step.checkedWireImageExact, step.baseWireImageExact] using
                  same
              have representedEq :=
                step.checkedPriorWire_injective priorImageEq
              exact priorState.representedWiresAvoidDying ⟨wire.1, old⟩
                (by simpa [priorDyingEq] using representedEq)
            · let fresh := newlyCoveredWire content wire.1 wire.2 old
              exact step.checkedFragmentWire_ne_checkedPriorWire_of_internal
                fresh.choose fresh.choose_spec.1
                (step.priorWireImage result.relationWire) (by
                  simpa [next, batchReconstructionSnoc, old,
                    step.checkedWireImageExact,
                    step.baseWireImageExact] using same) }⟩

/-- The complete accepted inverse trace has a construction-owned carrier
state over the entire checked occurrence family. -/
theorem RelationSeverConcreteReceipt.fullReconstructionState_exists
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    Nonempty
      (BatchReconstructionTraceState (steps := receipt.inverse.steps)
        receipt.result occurrences
        receipt.inverse.boundFinal receipt.inverse.boundNodeImage
          receipt.inverse.boundDying) := by
  have contentsLength :
      occurrences.length = receipt.inverse.steps.length := by
    exact
      (receipt.sites_occurrences_length.symm.trans
        receipt.inverseSteps_sites_length.symm)
  have stepsAtomsLength :
      receipt.inverse.steps.length = receipt.result.atoms.length := by
    calc
      receipt.inverse.steps.length =
          (receipt.inverse.steps.map
            ConcreteWireQuantifier.RelationJoinStep.application).length := by
        simp
      _ = receipt.result.atoms.length :=
        congrArg List.length receipt.inverseStepsExact
  have applicationsExact :
      receipt.inverse.steps.map
          ConcreteWireQuantifier.RelationJoinStep.application =
        receipt.result.atoms.take receipt.inverse.steps.length := by
    calc
      receipt.inverse.steps.map
          ConcreteWireQuantifier.RelationJoinStep.application =
        receipt.result.atoms := receipt.inverseStepsExact
      _ = receipt.result.atoms.take receipt.inverse.steps.length := by
        rw [stepsAtomsLength]
        simp
  exact batchReconstructionTraceFold_exists receipt.result occurrences
    receipt.extractions.first receipt.extractions.entries
    receipt.extractions.entries.semanticEvidence_sites receipt.parameters
    receipt.parametersAccepted receipt.inverse.args
      receipt.inverse.relation_signature receipt.inverse.semantic_trace
      occurrences []
      (by simp) contentsLength applicationsExact

noncomputable def
    RelationSeverConcreteReceipt.fullReconstructionState
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    BatchReconstructionTraceState (steps := receipt.inverse.steps)
      receipt.result occurrences
      receipt.inverse.boundFinal receipt.inverse.boundNodeImage
        receipt.inverse.boundDying :=
  Classical.choice receipt.fullReconstructionState_exists

theorem
    RelationSeverConcreteReceipt.fullReconstruction_pendingOriginsEmpty
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    receipt.fullReconstructionState.state.pendingOrigins = [] := by
  rw [receipt.fullReconstructionState.pendingOriginsExact]
  have stepsAtomsLength :
      receipt.inverse.steps.length = receipt.result.atoms.length := by
    calc
      receipt.inverse.steps.length =
          (receipt.inverse.steps.map
            ConcreteWireQuantifier.RelationJoinStep.application).length := by
        simp
      _ = receipt.result.atoms.length :=
        congrArg List.length receipt.inverseStepsExact
  rw [stepsAtomsLength]
  simp

theorem
    RelationSeverConcreteReceipt.fullReconstruction_pendingApplicationsEmpty
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    receipt.fullReconstructionState.state.pendingApplications = [] := by
  rw [receipt.fullReconstructionState.state.pendingApplicationsExact,
    receipt.fullReconstruction_pendingOriginsEmpty]
  rfl

/-- Reindex the completed fold by the occurrence-owned concrete site list,
the authoritative index used by the coverage theorems. -/
noncomputable def
    RelationSeverConcreteReceipt.completeCarrierState
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    BatchReconstructionState
      (occurrences.map ContentOccurrence.toConcreteSite) occurrences
      receipt.inverse.boundFinal receipt.result.checked := by
  have sitesExact :=
    receipt.extractions.entries.semanticEvidence_sites
  exact sitesExact ▸ receipt.fullReconstructionState.state

noncomputable def
    RelationSeverConcreteReceipt.completeRegionImage
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    source.val.RegionId → receipt.inverse.boundFinal.val.RegionId :=
  fun region => receipt.fullReconstructionState.state.regionImage
    ⟨region, by
      change BatchCoveredRegion
        (receipt.extractions.entries.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site)
        occurrences region
      rw [receipt.extractions.entries.semanticEvidence_sites]
      exact receipt.extractions.entries.regionCoverage region⟩

noncomputable def
    RelationSeverConcreteReceipt.completeNodeImage
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    source.val.NodeId → receipt.inverse.boundFinal.val.NodeId :=
  fun node => receipt.fullReconstructionState.state.nodeImage
    ⟨node, by
      change BatchCoveredNode
        (receipt.extractions.entries.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site)
        occurrences node
      rw [receipt.extractions.entries.semanticEvidence_sites]
      exact receipt.extractions.entries.nodeCoverage node⟩

noncomputable def
    RelationSeverConcreteReceipt.completeWireImage
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    source.val.WireId → receipt.inverse.boundFinal.val.WireId :=
  fun wire => receipt.fullReconstructionState.state.wireImage
    ⟨wire, by
      change BatchCoveredWire
        (receipt.extractions.entries.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site)
        occurrences wire
      rw [receipt.extractions.entries.semanticEvidence_sites]
      exact receipt.extractions.entries.wireCoverage wire⟩

noncomputable def
    RelationSeverConcreteReceipt.completePortImage
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (node : source.val.NodeId) :
    Data.Finite.FiniteEquiv CPort CPort :=
  receipt.fullReconstructionState.state.portImage
    ⟨node, by
      change BatchCoveredNode
        (receipt.extractions.entries.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site)
        occurrences node
      rw [receipt.extractions.entries.semanticEvidence_sites]
      exact receipt.extractions.entries.nodeCoverage node⟩

theorem RelationSeverConcreteReceipt.completeRegionImage_injective
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    Function.Injective receipt.completeRegionImage := by
  intro left right same
  exact Subtype.ext_iff.mp
    (receipt.fullReconstructionState.state.regionImage_injective same)

theorem RelationSeverConcreteReceipt.completeRegionImage_sheet
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (region : source.val.RegionId)
    (data : source.val.regions region = .sheet) :
    receipt.inverse.boundFinal.val.regions
        (receipt.completeRegionImage region) = .sheet := by
  exact receipt.fullReconstructionState.state.regionSheetExact
    ⟨region, by
      change BatchCoveredRegion
        (receipt.extractions.entries.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site)
        occurrences region
      rw [receipt.extractions.entries.semanticEvidence_sites]
      exact receipt.extractions.entries.regionCoverage region⟩ data

theorem RelationSeverConcreteReceipt.completeRegionImage_cut
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (region parent : source.val.RegionId)
    (data : source.val.regions region = .cut parent) :
    receipt.inverse.boundFinal.val.regions
        (receipt.completeRegionImage region) =
      .cut (receipt.completeRegionImage parent) := by
  exact receipt.fullReconstructionState.state.regionCutExact
    ⟨region, by
      change BatchCoveredRegion
        (receipt.extractions.entries.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site)
        occurrences region
      rw [receipt.extractions.entries.semanticEvidence_sites]
      exact receipt.extractions.entries.regionCoverage region⟩ parent data

theorem RelationSeverConcreteReceipt.completeNodeImage_injective
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    Function.Injective receipt.completeNodeImage := by
  intro left right same
  exact Subtype.ext_iff.mp
    (receipt.fullReconstructionState.state.nodeImage_injective same)

theorem RelationSeverConcreteReceipt.completeNodeImage_data
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (node : source.val.NodeId) :
    receipt.inverse.boundFinal.val.nodes
        (receipt.completeNodeImage node) =
      (source.val.nodes node).relocate
        (receipt.completeRegionImage (source.val.nodes node).region) := by
  exact receipt.fullReconstructionState.state.nodeTableExact
    ⟨node, by
      change BatchCoveredNode
        (receipt.extractions.entries.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site)
        occurrences node
      rw [receipt.extractions.entries.semanticEvidence_sites]
      exact receipt.extractions.entries.nodeCoverage node⟩

noncomputable def
    RelationSeverConcreteReceipt.completePlainRegionImage
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    source.val.RegionId → receipt.inverse.plainFinal.val.RegionId :=
  fun region => receipt.inverse.plainBoundRegionImage
    (receipt.completeRegionImage region)

theorem
    RelationSeverConcreteReceipt.completePlainRegionImage_injective
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    Function.Injective receipt.completePlainRegionImage := by
  intro left right same
  apply receipt.completeRegionImage_injective
  exact receipt.inverse.plainBoundRegionImage_injective same

theorem
    RelationSeverConcreteReceipt.completePlainRegionImage_sheet
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (region : source.val.RegionId)
    (data : source.val.regions region = .sheet) :
    receipt.inverse.plainFinal.val.regions
        (receipt.completePlainRegionImage region) = .sheet :=
  receipt.inverse.plainBoundRegionImage_sheet _
    (receipt.completeRegionImage_sheet region data)

theorem
    RelationSeverConcreteReceipt.completePlainRegionImage_cut
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (region parent : source.val.RegionId)
    (data : source.val.regions region = .cut parent) :
    receipt.inverse.plainFinal.val.regions
        (receipt.completePlainRegionImage region) =
      .cut (receipt.completePlainRegionImage parent) :=
  receipt.inverse.plainBoundRegionImage_cut _ _
    (receipt.completeRegionImage_cut region parent data)

noncomputable def
    RelationSeverConcreteReceipt.completePlainNodeImage
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    source.val.NodeId → receipt.inverse.plainFinal.val.NodeId :=
  fun node => receipt.inverse.plainBoundNodeImage
    (receipt.completeNodeImage node)

theorem
    RelationSeverConcreteReceipt.completePlainNodeImage_injective
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    Function.Injective receipt.completePlainNodeImage := by
  intro left right same
  apply receipt.completeNodeImage_injective
  exact receipt.inverse.plainBoundNodeImage_injective same

theorem
    RelationSeverConcreteReceipt.completePlainNodeImage_data
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (node : source.val.NodeId) :
    receipt.inverse.plainFinal.val.nodes
        (receipt.completePlainNodeImage node) =
      (source.val.nodes node).relocate
        (receipt.completePlainRegionImage
          (source.val.nodes node).region) := by
  have deleted := receipt.inverse.plainBoundNodeImage_data
    (receipt.completeNodeImage node)
  rw [receipt.completeNodeImage_data] at deleted
  simpa [RelationSeverConcreteReceipt.completePlainNodeImage,
    RelationSeverConcreteReceipt.completePlainRegionImage,
    CNode.relocate_relocate, CNode.region_relocate] using deleted

theorem RelationSeverConcreteReceipt.completeWireImage_injective
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    Function.Injective receipt.completeWireImage := by
  intro left right same
  exact Subtype.ext_iff.mp
    (receipt.fullReconstructionState.state.wireImage_injective same)

theorem RelationSeverConcreteReceipt.completeWireImage_signature
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (wire : source.val.WireId) :
    (receipt.inverse.boundFinal.val.wires
      (receipt.completeWireImage wire)).sig =
        (source.val.wires wire).sig := by
  exact receipt.fullReconstructionState.state.wireSignatureExact
    ⟨wire, by
      change BatchCoveredWire
        (receipt.extractions.entries.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site)
        occurrences wire
      rw [receipt.extractions.entries.semanticEvidence_sites]
      exact receipt.extractions.entries.wireCoverage wire⟩

theorem RelationSeverConcreteReceipt.completeWireImage_scope
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (wire : source.val.WireId) :
    (receipt.inverse.boundFinal.val.wires
      (receipt.completeWireImage wire)).scope =
        receipt.completeRegionImage (source.val.wires wire).scope := by
  have fullScope := receipt.fullReconstructionState.state.wireScopeExact
    ⟨wire, by
      change BatchCoveredWire
        (receipt.extractions.entries.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site)
        occurrences wire
      rw [receipt.extractions.entries.semanticEvidence_sites]
      exact receipt.extractions.entries.wireCoverage wire⟩
  exact fullScope

theorem
    RelationSeverConcreteReceipt.completeWireImage_ne_boundDying
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (wire : source.val.WireId) :
    receipt.completeWireImage wire ≠ receipt.inverse.boundDying := by
  simpa [RelationSeverConcreteReceipt.completeWireImage] using
    receipt.fullReconstructionState.representedWiresAvoidDying
      ⟨wire, by
        change BatchCoveredWire
          (receipt.extractions.entries.semanticEvidence.map
            WireQuantifierSemantics.RelationSeverOccurrence.site)
          occurrences wire
        rw [receipt.extractions.entries.semanticEvidence_sites]
        exact receipt.extractions.entries.wireCoverage wire⟩

/-- Exact source-wire landing after the exhausted inverse relation is
deleted from the completed bound reconstruction. -/
noncomputable def
    RelationSeverConcreteReceipt.completePlainWireImage
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    source.val.WireId → receipt.inverse.plainFinal.val.WireId :=
  fun wire => receipt.inverse.plainBoundWireImage
    (receipt.completeWireImage wire)
    (receipt.completeWireImage_ne_boundDying wire)

theorem
    RelationSeverConcreteReceipt.completePlainWireImage_injective
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    Function.Injective receipt.completePlainWireImage := by
  intro left right same
  apply receipt.completeWireImage_injective
  exact receipt.inverse.plainBoundWireImage_injective
    (receipt.completeWireImage_ne_boundDying left)
    (receipt.completeWireImage_ne_boundDying right) same

theorem
    RelationSeverConcreteReceipt.completePlainWireImage_signature
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (wire : source.val.WireId) :
    (receipt.inverse.plainFinal.val.wires
      (receipt.completePlainWireImage wire)).sig =
        (source.val.wires wire).sig :=
  (receipt.inverse.plainBoundWireImage_signature _
    (receipt.completeWireImage_ne_boundDying wire)).trans
      (receipt.completeWireImage_signature wire)

theorem
    RelationSeverConcreteReceipt.completePlainWireImage_scope
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (wire : source.val.WireId) :
    (receipt.inverse.plainFinal.val.wires
      (receipt.completePlainWireImage wire)).scope =
        receipt.completePlainRegionImage (source.val.wires wire).scope := by
  unfold RelationSeverConcreteReceipt.completePlainWireImage
    RelationSeverConcreteReceipt.completePlainRegionImage
  rw [receipt.inverse.plainBoundWireImage_scope _
    (receipt.completeWireImage_ne_boundDying wire)]
  rw [receipt.completeWireImage_scope]

theorem
    RelationSeverConcreteReceipt.completePlainEndpoint_mem
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (wire : source.val.WireId)
    (endpoint : CEndpoint source.val.nodeCount)
    (incident : endpoint ∈ (source.val.wires wire).endpoints) :
    ({ node := receipt.completePlainNodeImage endpoint.node
       port := receipt.completePortImage endpoint.node endpoint.port } :
        CEndpoint receipt.inverse.plainFinal.val.nodeCount) ∈
      (receipt.inverse.plainFinal.val.wires
        (receipt.completePlainWireImage wire)).endpoints := by
  have boundIncident :=
    receipt.fullReconstructionState.state.wireEndpointForward
      ⟨wire, by
        change BatchCoveredWire
          (receipt.extractions.entries.semanticEvidence.map
            WireQuantifierSemantics.RelationSeverOccurrence.site)
          occurrences wire
        rw [receipt.extractions.entries.semanticEvidence_sites]
        exact receipt.extractions.entries.wireCoverage wire⟩
      endpoint incident (by
        change BatchCoveredNode
          (receipt.extractions.entries.semanticEvidence.map
            WireQuantifierSemantics.RelationSeverOccurrence.site)
          occurrences endpoint.node
        rw [receipt.extractions.entries.semanticEvidence_sites]
        exact receipt.extractions.entries.nodeCoverage endpoint.node)
  have deleted := receipt.inverse.plainBoundWireImage_endpoint_mem
    (receipt.completeWireImage wire)
    (receipt.completeWireImage_ne_boundDying wire)
    { node := receipt.completeNodeImage endpoint.node
      port := receipt.completePortImage endpoint.node endpoint.port }
    boundIncident
  exact deleted

theorem
    RelationSeverConcreteReceipt.inverseSteps_identityRequestsEmpty
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    ∀ step ∈ receipt.inverse.steps,
      step.attachment.identityRequests = [] := by
  intro step member
  obtain ⟨position, stepExact⟩ := List.get_of_mem member
  subst step
  exact receipt.inverseStep_identityRequestsEmpty position

theorem
    RelationSeverConcreteReceipt.constructionRegionCount_eq
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    source.val.regionCount = receipt.inverse.plainFinal.val.regionCount := by
  have traceCounts := relationJoinTrace_count_exact
    receipt.inverse.semantic_trace receipt.inverseSteps_identityRequestsEmpty
  have removedLength :
      ((receipt.extractions.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site).flatMap
        ConcreteWireQuantifier.RelationSeverSite.removedRegions).length =
      occurrences.length *
        (pattern.val.diagram.regionsList.filter fun region =>
          decide (region ≠ pattern.val.diagram.root)).length := by
    change
      ((receipt.extractions.entries.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site).flatMap
        ConcreteWireQuantifier.RelationSeverSite.removedRegions).length = _
    rw [receipt.extractions.entries.semanticEvidence_sites]
    exact receipt.extractions.entries.removedRegions_length
  have stepsLength : receipt.inverse.steps.length = occurrences.length :=
    receipt.inverseSteps_sites_length.trans receipt.sites_occurrences_length
  have partition := receipt.result.retainedRegions_length_add_removedRegions_length
  have severCount := receipt.result.checkedRegionCount_eq_retainedRegions
  have finalCount := receipt.inverse.plainFinal_regionCount
  rcases traceCounts with ⟨traceRegion, _traceNode, _traceWire⟩
  rw [stepsLength, severCount, ← finalCount] at traceRegion
  rw [removedLength] at partition
  omega

theorem
    RelationSeverConcreteReceipt.constructionNodeCount_eq
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    source.val.nodeCount = receipt.inverse.plainFinal.val.nodeCount := by
  have traceCounts := relationJoinTrace_count_exact
    receipt.inverse.semantic_trace receipt.inverseSteps_identityRequestsEmpty
  have removedLength :
      ((receipt.extractions.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site).flatMap
        ConcreteWireQuantifier.RelationSeverSite.removedNodes).length =
      occurrences.length * pattern.val.diagram.nodeCount := by
    change
      ((receipt.extractions.entries.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site).flatMap
        ConcreteWireQuantifier.RelationSeverSite.removedNodes).length = _
    rw [receipt.extractions.entries.semanticEvidence_sites]
    exact receipt.extractions.entries.removedNodes_length
  have stepsLength : receipt.inverse.steps.length = occurrences.length :=
    receipt.inverseSteps_sites_length.trans receipt.sites_occurrences_length
  have sitesLength :
      (receipt.extractions.semanticEvidence.map
        WireQuantifierSemantics.RelationSeverOccurrence.site).length =
          occurrences.length := receipt.sites_occurrences_length
  have partition := receipt.result.retainedNodes_length_add_removedNodes_length
  have severCount := receipt.result.checkedNodeCount_eq_retainedNodes_add_sites
  have finalCount := receipt.inverse.plainFinal_nodeCount
  rcases traceCounts with ⟨_traceRegion, traceNode, _traceWire⟩
  rw [stepsLength, severCount, sitesLength, ← finalCount] at traceNode
  rw [removedLength] at partition
  omega

theorem
    RelationSeverConcreteReceipt.constructionWireCount_eq
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    source.val.wireCount = receipt.inverse.plainFinal.val.wireCount := by
  have traceCounts := relationJoinTrace_count_exact
    receipt.inverse.semantic_trace receipt.inverseSteps_identityRequestsEmpty
  have removedLength :
      ((receipt.extractions.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site).flatMap
        ConcreteWireQuantifier.RelationSeverSite.removedWires).length =
      occurrences.length *
        (pattern.val.diagram.wiresList.filter fun wire =>
          decide (wire ∉ pattern.val.boundary)).length := by
    change
      ((receipt.extractions.entries.semanticEvidence.map
          WireQuantifierSemantics.RelationSeverOccurrence.site).flatMap
        ConcreteWireQuantifier.RelationSeverSite.removedWires).length = _
    rw [receipt.extractions.entries.semanticEvidence_sites]
    exact receipt.extractions.entries.removedWires_length
  have stepsLength : receipt.inverse.steps.length = occurrences.length :=
    receipt.inverseSteps_sites_length.trans receipt.sites_occurrences_length
  have partition := receipt.result.retainedWires_length_add_removedWires_length
  have severCount := receipt.result.checkedWireCount_eq_retainedWires_add_one
  have finalCount := receipt.inverse.plainFinal_wireCount_add_one
  rcases traceCounts with ⟨_traceRegion, _traceNode, traceWire⟩
  rw [stepsLength, severCount, ← finalCount] at traceWire
  rw [removedLength] at partition
  omega

noncomputable def
    RelationSeverConcreteReceipt.constructionRegionEquiv
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    Data.Finite.FiniteEquiv source.val.RegionId
      receipt.inverse.plainFinal.val.RegionId :=
  Data.Finite.FiniteEquiv.ofBijectiveFin receipt.completePlainRegionImage
    ⟨receipt.completePlainRegionImage_injective,
      Data.Finite.fin_surjective_of_injective_of_card_eq
        receipt.completePlainRegionImage
        receipt.completePlainRegionImage_injective
        receipt.constructionRegionCount_eq⟩

theorem RelationSeverConcreteReceipt.constructionRegionRoot
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    receipt.constructionRegionEquiv source.val.root =
      receipt.inverse.plainFinal.val.root := by
  change receipt.completePlainRegionImage source.val.root =
    receipt.inverse.plainFinal.val.root
  have mappedSheet := receipt.completePlainRegionImage_sheet source.val.root
    source.property.root_is_sheet
  have onlyRoot :=
    (List.all_eq_true.mp
      receipt.inverse.plainFinal.property.only_root_is_sheet)
      (receipt.completePlainRegionImage source.val.root)
      (Data.Finite.mem_allFin _)
  exact (of_decide_eq_true onlyRoot) mappedSheet

theorem RelationSeverConcreteReceipt.constructionRegionTable
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (region : source.val.RegionId) :
    receipt.inverse.plainFinal.val.regions
        (receipt.constructionRegionEquiv region) =
      (source.val.regions region).rename receipt.constructionRegionEquiv := by
  change receipt.inverse.plainFinal.val.regions
      (receipt.completePlainRegionImage region) =
    (source.val.regions region).rename receipt.constructionRegionEquiv
  cases data : source.val.regions region with
  | sheet =>
      simpa [data, CRegion.rename] using
        receipt.completePlainRegionImage_sheet region data
  | cut parent =>
      simpa [data, CRegion.rename] using
        receipt.completePlainRegionImage_cut region parent data

noncomputable def
    RelationSeverConcreteReceipt.constructionNodeEquiv
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    Data.Finite.FiniteEquiv source.val.NodeId
      receipt.inverse.plainFinal.val.NodeId :=
  Data.Finite.FiniteEquiv.ofBijectiveFin receipt.completePlainNodeImage
    ⟨receipt.completePlainNodeImage_injective,
      Data.Finite.fin_surjective_of_injective_of_card_eq
        receipt.completePlainNodeImage
        receipt.completePlainNodeImage_injective
        receipt.constructionNodeCount_eq⟩

theorem RelationSeverConcreteReceipt.constructionNodeTable
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (node : source.val.NodeId) :
    receipt.inverse.plainFinal.val.nodes
        (receipt.constructionNodeEquiv node) =
      (source.val.nodes node).rename receipt.constructionRegionEquiv := by
  change receipt.inverse.plainFinal.val.nodes
      (receipt.completePlainNodeImage node) =
    (source.val.nodes node).rename receipt.constructionRegionEquiv
  rw [CNode.rename_eq_relocate]
  exact receipt.completePlainNodeImage_data node

noncomputable def
    RelationSeverConcreteReceipt.constructionWireEquiv
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    Data.Finite.FiniteEquiv source.val.WireId
      receipt.inverse.plainFinal.val.WireId :=
  Data.Finite.FiniteEquiv.ofBijectiveFin receipt.completePlainWireImage
    ⟨receipt.completePlainWireImage_injective,
      Data.Finite.fin_surjective_of_injective_of_card_eq
        receipt.completePlainWireImage
        receipt.completePlainWireImage_injective
        receipt.constructionWireCount_eq⟩

noncomputable def
    RelationSeverConcreteReceipt.constructionEndpointEquiv
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    Data.Finite.FiniteEquiv
      (CEndpoint source.val.nodeCount)
      (CEndpoint receipt.inverse.plainFinal.val.nodeCount) where
  toFun := fun endpoint =>
    { node := receipt.constructionNodeEquiv endpoint.node
      port := receipt.completePortImage endpoint.node endpoint.port }
  invFun := fun candidate =>
    let node := receipt.constructionNodeEquiv.symm candidate.node
    { node := node
      port := (receipt.completePortImage node).symm candidate.port }
  left_inv := by
    intro endpoint
    cases endpoint
    simp
  right_inv := by
    intro candidate
    cases candidate with
    | mk node port =>
        let sourceNode := receipt.constructionNodeEquiv.symm node
        have nodeExact :
            receipt.constructionNodeEquiv sourceNode = node :=
          receipt.constructionNodeEquiv.right_inv node
        have portExact :
            receipt.completePortImage sourceNode
                ((receipt.completePortImage sourceNode).symm port) = port :=
          (receipt.completePortImage sourceNode).right_inv port
        rw [CEndpoint.mk.injEq]
        exact ⟨nodeExact, portExact⟩

theorem
    RelationSeverConcreteReceipt.completePlainPortImage_required
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (node : source.val.NodeId) (port : CPort) :
    receipt.completePortImage node port ∈
        receipt.inverse.plainFinal.val.requiredPorts
          (receipt.constructionNodeEquiv node) ↔
      port ∈ source.val.requiredPorts node := by
  have preserved :=
    receipt.fullReconstructionState.state.portImageRequired
      ⟨node, by
        change BatchCoveredNode
          (receipt.extractions.entries.semanticEvidence.map
            WireQuantifierSemantics.RelationSeverOccurrence.site)
          occurrences node
        rw [receipt.extractions.entries.semanticEvidence_sites]
        exact receipt.extractions.entries.nodeCoverage node⟩ port
  have boundData := receipt.completeNodeImage_data node
  change receipt.completePortImage node port ∈
      requiredPortsForNode
        (receipt.inverse.boundFinal.val.nodes
          (receipt.completeNodeImage node)) ↔
    port ∈ requiredPortsForNode (source.val.nodes node) at preserved
  rw [boundData] at preserved
  simp only [requiredPortsForNode_relocate] at preserved
  simp only [ConcreteDiagram.requiredPorts]
  rw [receipt.constructionNodeTable node]
  rw [CNode.rename_eq_relocate]
  cases sourceData : source.val.nodes node <;>
    simpa [ConcreteDiagram.requiredPorts, requiredPortsForNode,
      sourceData, CNode.relocate] using preserved

theorem
    RelationSeverConcreteReceipt.completePlainPortCorresponds
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (node : source.val.NodeId) (port : CPort)
    (required : port ∈ source.val.requiredPorts node) :
    PortCorresponds source.val receipt.inverse.plainFinal.val
      receipt.constructionNodeEquiv
      { node := node, port := port }
      { node := receipt.constructionNodeEquiv node
        port := receipt.completePortImage node port } := by
  refine ⟨rfl, ?_⟩
  have corresponds :=
    receipt.fullReconstructionState.state.portImageCorresponds
      ⟨node, by
        change BatchCoveredNode
          (receipt.extractions.entries.semanticEvidence.map
            WireQuantifierSemantics.RelationSeverOccurrence.site)
          occurrences node
        rw [receipt.extractions.entries.semanticEvidence_sites]
        exact receipt.extractions.entries.nodeCoverage node⟩ port required
  change PortDataCorresponds (source.val.nodes node)
      (receipt.inverse.boundFinal.val.nodes
        (receipt.completeNodeImage node)) port
      (receipt.completePortImage node port) at corresponds
  rw [receipt.completeNodeImage_data] at corresponds
  rw [receipt.constructionNodeTable node]
  cases sourceData : source.val.nodes node <;>
    simp_all [PortDataCorresponds, sourceData, CNode.rename_eq_relocate,
      CNode.relocate]

theorem RelationSeverConcreteReceipt.constructionWireSignature
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (wire : source.val.WireId) :
    (receipt.inverse.plainFinal.val.wires
      (receipt.constructionWireEquiv wire)).sig =
        (source.val.wires wire).sig := by
  change (receipt.inverse.plainFinal.val.wires
    (receipt.completePlainWireImage wire)).sig = _
  exact receipt.completePlainWireImage_signature wire

theorem RelationSeverConcreteReceipt.constructionWireScope
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (wire : source.val.WireId) :
    (receipt.inverse.plainFinal.val.wires
      (receipt.constructionWireEquiv wire)).scope =
        receipt.constructionRegionEquiv (source.val.wires wire).scope := by
  change (receipt.inverse.plainFinal.val.wires
    (receipt.completePlainWireImage wire)).scope =
      receipt.completePlainRegionImage (source.val.wires wire).scope
  exact receipt.completePlainWireImage_scope wire

theorem
    RelationSeverConcreteReceipt.constructionEndpoint_mem_iff
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (wire : source.val.WireId)
    (endpoint : CEndpoint source.val.nodeCount) :
    receipt.constructionEndpointEquiv endpoint ∈
        (receipt.inverse.plainFinal.val.wires
          (receipt.constructionWireEquiv wire)).endpoints ↔
      endpoint ∈ (source.val.wires wire).endpoints := by
  constructor
  · intro mappedIncident
    have mappedRequired := ConcreteDiagram.incident_port_required _
      receipt.inverse.plainFinal.val receipt.inverse.plainFinal.property
      (receipt.constructionWireEquiv wire)
      (receipt.constructionEndpointEquiv endpoint) mappedIncident
    have sourceRequired :
        endpoint.port ∈ source.val.requiredPorts endpoint.node :=
      (receipt.completePlainPortImage_required endpoint.node endpoint.port).mp
        (by
          simpa [RelationSeverConcreteReceipt.constructionEndpointEquiv]
            using mappedRequired)
    obtain ⟨owner, ownerEquation⟩ :=
      ConcreteDiagram.endpointOwner?_complete _ source.val source.property
        endpoint.node endpoint.port sourceRequired
    have ownerIncident := ConcreteDiagram.endpointOwner?_incident
      source.val endpoint owner ownerEquation
    have mappedOwnerIncident := receipt.completePlainEndpoint_mem
      owner endpoint ownerIncident
    have mappedOwnerEquation := ConcreteDiagram.endpointOwner?_eq_of_incident _
      receipt.inverse.plainFinal.val receipt.inverse.plainFinal.property
      (receipt.constructionEndpointEquiv endpoint).node
      (receipt.constructionEndpointEquiv endpoint).port mappedRequired
      (receipt.constructionWireEquiv owner) (by
        simpa [RelationSeverConcreteReceipt.constructionEndpointEquiv]
          using mappedOwnerIncident)
    have mappedWireEquation := ConcreteDiagram.endpointOwner?_eq_of_incident _
      receipt.inverse.plainFinal.val receipt.inverse.plainFinal.property
      (receipt.constructionEndpointEquiv endpoint).node
      (receipt.constructionEndpointEquiv endpoint).port mappedRequired
      (receipt.constructionWireEquiv wire) mappedIncident
    have mappedWiresEqual :
        receipt.constructionWireEquiv owner =
          receipt.constructionWireEquiv wire :=
      Option.some.inj
        (mappedOwnerEquation.symm.trans mappedWireEquation)
    have ownerExact : owner = wire :=
      receipt.constructionWireEquiv.injective mappedWiresEqual
    simpa [ownerExact] using ownerIncident
  · intro incident
    simpa [RelationSeverConcreteReceipt.constructionEndpointEquiv] using
      receipt.completePlainEndpoint_mem wire endpoint incident

noncomputable def
    RelationSeverConcreteReceipt.constructionEndpointFiber
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target)
    (wire : source.val.WireId) :
    ConcreteIso.EndpointFiberEquiv receipt.constructionNodeEquiv
      receipt.constructionWireEquiv wire where
  equivalence :=
    { toFun := fun endpoint =>
        ⟨receipt.constructionEndpointEquiv endpoint.1,
          (receipt.constructionEndpoint_mem_iff wire endpoint.1).mpr endpoint.2⟩
      invFun := fun candidate =>
        let endpoint := receipt.constructionEndpointEquiv.symm candidate.1
        ⟨endpoint,
          (receipt.constructionEndpoint_mem_iff wire endpoint).mp (by
            dsimp [endpoint]
            rw [receipt.constructionEndpointEquiv.right_inv candidate.1]
            exact candidate.2)⟩
      left_inv := by
        intro endpoint
        apply Subtype.ext
        exact receipt.constructionEndpointEquiv.left_inv endpoint.1
      right_inv := by
        intro candidate
        apply Subtype.ext
        exact receipt.constructionEndpointEquiv.right_inv candidate.1 }
  corresponds := by
    intro endpoint
    have required := ConcreteDiagram.incident_port_required _ source.val
      source.property wire endpoint.1 endpoint.2
    simpa [RelationSeverConcreteReceipt.constructionEndpointEquiv] using
      receipt.completePlainPortCorresponds endpoint.1.node endpoint.1.port
        required

noncomputable def RelationSeverConcreteReceipt.constructionIso
    (receipt : RelationSeverConcreteReceipt source orientation scope pattern
      occurrences target) :
    ConcreteIso source.val receipt.inverse.plainFinal.val :=
  ConcreteIso.ofEquivs receipt.constructionRegionEquiv
    receipt.constructionNodeEquiv receipt.constructionWireEquiv
    receipt.constructionRegionRoot receipt.constructionRegionTable
    receipt.constructionNodeTable receipt.constructionWireSignature
    receipt.constructionWireScope receipt.constructionEndpointFiber


end Internal

end MonolithicWireQuantifier

end VisualProof
