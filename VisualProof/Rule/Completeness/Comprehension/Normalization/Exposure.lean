import VisualProof.Rule.Completeness.Comprehension.Normalization.Support

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

namespace EqualityNormalization

theorem identityBoundaryMaterial_scope
    (pattern : OpenDiagram arguments)
    (ports : Vars wires arguments) :
    ScopePreservation
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        pattern ports)
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        (identityBoundary pattern) ports) := by
  constructor
  · intro _
    exact
      _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate_canonical
        (identityBoundary pattern) ports
  · intro signature wire
    rw [instantiate_incidence_nonempty_iff,
      instantiate_incidence_nonempty_iff]
  · intro signature wire sourceRoot
    rw [instantiate_rootedTwo_iff] at sourceRoot ⊢
    exact sourceRoot

/-- One selected instantiation in its exact inferred retained host is
bidirectionally equivalent to the same application through the ordered
identity boundary. The normalized combined endpoint and both validity proofs
are constructed internally. -/
theorem equatesIdentityBoundary
    {boundary outer arguments : List Sig}
    (pattern : OpenDiagram arguments)
    {hostLocals : List Sig}
    {hostItems : ItemSeq (outer ++ hostLocals)}
    (ports : Vars (outer ++ hostLocals) arguments)
    {source : OpenDiagram boundary}
    (occurrence : Occurrence
      (Region.adjoinAt hostLocals hostItems
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern ports)) source) :
    ∃ targetCanonical :
        (occurrence.context.fill
          (Region.adjoinAt hostLocals hostItems
            (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
              (identityBoundary pattern) ports))).Canonical,
      ∃ targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems
              (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
                (identityBoundary pattern) ports))),
        Equates occurrence
          (Region.adjoinAt hostLocals hostItems
            (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
              (identityBoundary pattern) ports))
          targetCanonical targetExternalTwoEnded := by
  let sourceMaterial :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      pattern ports
  let targetMaterial :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      (identityBoundary pattern) ports
  let sourceRegion := Region.adjoinAt hostLocals hostItems sourceMaterial
  let targetRegion := Region.adjoinAt hostLocals hostItems targetMaterial
  have sourceLocalCanonical : sourceRegion.Canonical := by
    exact occurrence.context.holeCanonical _ occurrence.sourceCanonical
  have regionScope : ScopePreservation sourceRegion targetRegion := by
    exact adjoinAt_preserves_scope hostLocals hostItems sourceMaterial
      targetMaterial (identityBoundaryMaterial_scope pattern ports)
  have targetLocalCanonical : targetRegion.Canonical :=
    regionScope.canonical sourceLocalCanonical
  have replacement := occurrence.context.replaceCanonical sourceRegion
    targetRegion occurrence.sourceCanonical targetLocalCanonical
      regionScope.incidenceNonempty
  let targetCanonical := replacement.1
  let sourceEndpoint := occurrence.interface.withBody
    (occurrence.context.fill sourceRegion) occurrence.sourceCanonical
      occurrence.sourceExternalTwoEnded
  let targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill targetRegion) :=
    sourceEndpoint.externalTwoEnded_of_nonempty_iff _ replacement.2
  refine ⟨targetCanonical, targetExternalTwoEnded, ?_⟩
  by_cases nonempty : outer ++ hostLocals ≠ []
  · let pinnedItems := hostItems.append (contextPins outer hostLocals)
    let description := exposureDescriptionWithHost pattern hostLocals
      pinnedItems ports
    have sourceEq : description.source =
        Region.adjoinAt hostLocals pinnedItems sourceMaterial := by
      simpa only [description, sourceMaterial] using
        exposureDescriptionWithHost_source pattern hostLocals pinnedItems ports
    have targetEq : description.target =
        Region.mk hostLocals pinnedItems := by
      rfl
    have exposedEq : ∀ materialCanonical : description.material.Canonical,
        Erasure.Exposure.exposedRegion description materialCanonical =
          Region.adjoinAt hostLocals pinnedItems targetMaterial := by
      intro materialCanonical
      simpa only [description, targetMaterial] using
        exposureDescriptionWithHost_exposedRegion pattern hostLocals
          pinnedItems ports materialCanonical
    have strict := pinnedExposureStrict
      (occurrence := by simpa only [sourceMaterial] using occurrence)
      (targetCanonical := by
        simpa only [targetRegion, targetMaterial] using targetCanonical)
      (targetExternalTwoEnded := by
        intro signature wire
        simpa only [targetRegion, targetMaterial] using
          targetExternalTwoEnded wire)
      nonempty description sourceEq targetEq exposedEq
    simpa only [targetRegion, targetMaterial] using strict.toEquates
  · have empty : outer ++ hostLocals = [] :=
      Classical.not_not.mp nonempty
    have outerEmpty : outer = [] := (List.append_eq_nil_iff.mp empty).1
    have localsEmpty : hostLocals = [] :=
      (List.append_eq_nil_iff.mp empty).2
    subst outer
    subst hostLocals
    let description := exposureDescriptionWithHost pattern [] hostItems ports
    have sourceEq : description.source = sourceRegion := by
      simpa only [description, sourceRegion, sourceMaterial] using
        exposureDescriptionWithHost_source pattern [] hostItems ports
    let exposureOccurrence : Occurrence description.source source := {
      interface := occurrence.interface
      context := occurrence.context
      sourceCanonical := by
        rw [sourceEq]
        exact occurrence.sourceCanonical
      sourceExternalTwoEnded := by
        intro signature wire
        rw [sourceEq]
        exact occurrence.sourceExternalTwoEnded wire
      host_iso := by
        simpa only [sourceEq, sourceRegion, sourceMaterial] using
          occurrence.host_iso
    }
    have erasedLocalCanonical : description.target.Canonical := by
      have canonical := pinnedHostCanonical ([] : List Sig) hostItems
        sourceMaterial sourceLocalCanonical
      simpa only [description, exposureDescriptionWithHost,
        Rule.Erasure.Description.target, contextPins, allPins,
        List.nil_append, ItemSeq.pinWires, ItemSeq.nil_append,
        ItemSeq.append_nil] using canonical
    have erasedSameNonempty : ∀ {signature} (wire : Var [] signature),
        sourceRegion.incidencePaths wire.index.val ≠ [] ↔
          description.target.incidencePaths wire.index.val ≠ [] := by
      intro signature wire
      exact Fin.elim0 wire.index
    have erasedReplacement := occurrence.context.replaceCanonical
      sourceRegion description.target occurrence.sourceCanonical
        erasedLocalCanonical erasedSameNonempty
    have erasedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire
        (occurrence.context.fill description.target) :=
      sourceEndpoint.externalTwoEnded_of_nonempty_iff _
        erasedReplacement.2
    obtain ⟨materialCanonical, exposedCanonical,
        exposedExternalTwoEnded, exposedEquates⟩ :=
      Erasure.Exposure.equates description exposureOccurrence
        erasedReplacement.1 erasedExternalTwoEnded
    have exposedEq :
        Erasure.Exposure.exposedRegion description materialCanonical =
          targetRegion := by
      simpa only [description, targetRegion, targetMaterial] using
        exposureDescriptionWithHost_exposedRegion pattern [] hostItems ports
          materialCanonical
    simpa only [Equates, exposureOccurrence, sourceEq, exposedEq,
      sourceRegion, sourceMaterial, targetRegion, targetMaterial] using
      exposedEquates

mutual
  noncomputable def normalizedRegionStrict
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.RegionResult
          pattern frame.sourceKeep frame.selected sourceRegion result)
      (sites : RegionSites operation data evidence)
      (hasSelection : regionHasSelection sites = true) :
      ∀ (outer : List Sig) (rename : WireRenaming common outer)
        {boundary : List Sig} {source : OpenDiagram boundary}
        (occurrence : Occurrence (result.renameWires rename) source)
        (targetCanonical :
          (occurrence.context.fill
            (Region.renameWires rename
              (normalizedRegion pattern evidence sites).1)).Canonical)
        (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (Region.renameWires rename
              (normalizedRegion pattern evidence sites).1))),
        StrictEquates occurrence
          (Region.renameWires rename (normalizedRegion pattern evidence sites).1)
          targetCanonical (fun wire => targetExternalTwoEnded wire) :=
    match sites with
    | @RegionSites.mk _ _ _ _ _ _ _ _ locals items childResult childEvidence
        childSites => by
        intro outer rename boundary source occurrence targetCanonical
          targetExternalTwoEnded
        let childRename := rename.appendRight locals
        let childHostItems : ItemSeq (outer ++ locals) := .nil
        change Occurrence
          ((Region.adjoinAt locals .nil childResult).renameWires rename) source
          at occurrence
        have sourceEq := Region.renameWires_adjoinAt_nil childResult rename
        have childSourceCanonical :
            (Region.adjoinAt locals childHostItems
              (childResult.renameWires childRename)).Canonical := by
          rw [← sourceEq]
          exact occurrence.context.holeCanonical _ occurrence.sourceCanonical
        have sourceNonempty : ∀ {signature} (wire : Var outer signature),
            ((Region.adjoinAt locals .nil childResult).renameWires rename).incidencePaths
                  wire.index.val ≠ [] ↔
              (Region.adjoinAt locals childHostItems
                (childResult.renameWires childRename)).incidencePaths
                  wire.index.val ≠ [] := by
          intro signature wire
          rw [sourceEq]
        let childOccurrence : Occurrence
            (Region.adjoinAt locals childHostItems
              (childResult.renameWires childRename)) source :=
          presentationOccurrence occurrence childSourceCanonical sourceNonempty
            (by
              simpa only [childHostItems, childRename] using
                RegionIso.renameWiresAdjoinAtNil childResult rename)
        let normalizedChild :=
          (normalizedItems pattern childEvidence childSites).1
        let targetBefore :=
          (Region.adjoinAt locals (.nil : ItemSeq (common ++ locals))
            normalizedChild).renameWires rename
        let targetAfter := Region.adjoinAt locals childHostItems
          (normalizedChild.renameWires childRename)
        have targetEq : targetBefore = targetAfter := by
          simpa only [targetBefore, targetAfter, childHostItems, childRename] using
            Region.renameWires_adjoinAt_nil normalizedChild rename
        change (occurrence.context.fill targetBefore).Canonical at targetCanonical
        change OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
          (occurrence.context.fill targetBefore) at targetExternalTwoEnded
        have targetAfterCanonical : targetAfter.Canonical := by
          rw [← targetEq]
          exact occurrence.context.holeCanonical _ targetCanonical
        have targetNonempty : ∀ {signature} (wire : Var outer signature),
            targetBefore.incidencePaths wire.index.val ≠ [] ↔
              targetAfter.incidencePaths wire.index.val ≠ [] := by
          intro signature wire
          rw [targetEq]
        have targetReplacement := occurrence.context.replaceCanonical
          targetBefore targetAfter targetCanonical targetAfterCanonical
            targetNonempty
        let targetBeforeEndpoint := occurrence.interface.withBody
          (occurrence.context.fill targetBefore) targetCanonical
            targetExternalTwoEnded
        have targetAfterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            occurrence.interface.boundaryWire
            (occurrence.context.fill targetAfter) :=
          targetBeforeEndpoint.externalTwoEnded_of_nonempty_iff _
            targetReplacement.2
        have childTargetCanonical :
            (childOccurrence.context.fill
              (Region.adjoinAt locals childHostItems
                (Region.renameWires childRename
                  (normalizedItems pattern childEvidence childSites).1))).Canonical := by
          exact targetReplacement.1
        have childTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            childOccurrence.interface.boundaryWire
            (childOccurrence.context.fill
              (Region.adjoinAt locals childHostItems
                (Region.renameWires childRename
                  (normalizedItems pattern childEvidence childSites).1))) := by
          intro signature wire
          exact targetAfterExternalTwoEnded wire
        have childSelection : itemsHaveSelection childSites = true := by
          simpa only [regionHasSelection] using hasSelection
        have folded := normalizedItemsStrict pattern
          childEvidence childSites childSelection locals childRename childHostItems
          childOccurrence childTargetCanonical childTargetExternalTwoEnded
        have finalBodyIso : RegionIso (WireEquiv.refl outer) targetAfter
            targetBefore := by
          simpa only [targetAfter, targetBefore, childHostItems, childRename] using
            (RegionIso.renameWiresAdjoinAtNil normalizedChild rename).symm
        have finalIso : OpenDiagramIso
            (childOccurrence.interface.withBody
              (childOccurrence.context.fill targetAfter)
              childTargetCanonical childTargetExternalTwoEnded)
            (occurrence.interface.withBody
              (occurrence.context.fill targetBefore) targetCanonical
                targetExternalTwoEnded) :=
          OpenDiagram.withBody_iso childTargetCanonical targetCanonical
            childTargetExternalTwoEnded targetExternalTwoEnded
            (DiagramContext.fillIso occurrence.context finalBodyIso)
        have presented := StrictEquates.targetIso folded finalIso
        simpa only [normalizedRegion, normalizedChild, targetBefore, targetAfter,
          childHostItems, childRename, childOccurrence] using presented
  termination_by 5 * sizeOf sites

  noncomputable def normalizedItemsStrict
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected sourceItems result)
      (sites : ItemsSites operation data evidence)
      (hasSelection : itemsHaveSelection sites = true)
      (hostLocals : List Sig)
      (rename : WireRenaming common (outer ++ hostLocals))
      (hostItems : ItemSeq (outer ++ hostLocals))
      {boundary : List Sig} {source : OpenDiagram boundary}
      (occurrence : Occurrence
        (Region.adjoinAt hostLocals hostItems
          (result.renameWires rename)) source)
      (targetCanonical :
        (occurrence.context.fill
          (Region.adjoinAt hostLocals hostItems
            (Region.renameWires rename
              (normalizedItems pattern evidence sites).1))).Canonical)
      (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire
        (occurrence.context.fill
          (Region.adjoinAt hostLocals hostItems
            (Region.renameWires rename
              (normalizedItems pattern evidence sites).1)))) :
      StrictEquates occurrence
        (Region.adjoinAt hostLocals hostItems
          (Region.renameWires rename (normalizedItems pattern evidence sites).1))
        targetCanonical (fun wire => targetExternalTwoEnded wire) := by
    let sourceMaterial := result.renameWires rename
    let targetMaterial :=
      (Region.renameWires rename (normalizedItems pattern evidence sites).1)
    by_cases nonempty : outer ++ hostLocals ≠ []
    · exact (by
    obtain ⟨pinnedSourceCanonical, pinnedSourceExternalTwoEnded,
        sourcePins⟩ := adjoinPinsEquatesNonempty hostLocals
      hostItems sourceMaterial occurrence nonempty
    let pinnedItems := hostItems.append
      (contextPins outer hostLocals)
    let pinnedSource := Region.adjoinAt hostLocals pinnedItems sourceMaterial
    let pinnedSourceOccurrence : Occurrence pinnedSource
        (occurrence.interface.withBody
          (occurrence.context.fill pinnedSource) pinnedSourceCanonical
            pinnedSourceExternalTwoEnded) :=
      exactOccurrence occurrence.interface occurrence.context pinnedSource
        pinnedSourceCanonical pinnedSourceExternalTwoEnded
    have sourceLocalCanonical :
        (Region.adjoinAt hostLocals hostItems sourceMaterial).Canonical :=
      occurrence.context.holeCanonical _ occurrence.sourceCanonical
    have pinnedHostCanonical :
        (Region.mk hostLocals pinnedItems).Canonical := by
      exact pinnedHostCanonical hostLocals hostItems
        sourceMaterial sourceLocalCanonical
    have pinnedHostNonempty : ∀ {signature}
        (wire : Var outer signature),
        (Region.mk hostLocals pinnedItems).incidencePaths
          wire.index.val ≠ [] := by
      intro signature wire
      exact pinnedHost_incidence_nonempty hostLocals hostItems wire
    have targetLocalCanonical :
        (Region.adjoinAt hostLocals hostItems targetMaterial).Canonical :=
      occurrence.context.holeCanonical _ targetCanonical
    have targetMaterialCanonical : targetMaterial.Canonical :=
      Region.Canonical.material_of_adjoinAt hostLocals hostItems _
        targetLocalCanonical
    have pinnedTargetValidity := supportedAdjoinValidity hostLocals
      pinnedItems pinnedSourceOccurrence pinnedHostCanonical
      pinnedHostNonempty targetMaterialCanonical
    have folded := normalizedItemsSupportedStrict pattern evidence
      sites hasSelection outer hostLocals rename pinnedItems pinnedSourceOccurrence
      pinnedHostCanonical pinnedHostNonempty pinnedTargetValidity.1
      pinnedTargetValidity.2
    let targetOccurrence : Occurrence
        (Region.adjoinAt hostLocals hostItems targetMaterial)
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems targetMaterial))
          targetCanonical targetExternalTwoEnded) :=
      exactOccurrence occurrence.interface occurrence.context _
        targetCanonical targetExternalTwoEnded
    obtain ⟨pinnedTargetCanonical, pinnedTargetExternalTwoEnded,
        targetPins⟩ := adjoinPinsEquatesNonempty hostLocals
      hostItems targetMaterial targetOccurrence nonempty
    have forwardPins : Relation.TransGen Step source
        (occurrence.interface.withBody
          (occurrence.context.fill pinnedSource) pinnedSourceCanonical
            pinnedSourceExternalTwoEnded) := by
      simpa only [sourceMaterial, pinnedSource, pinnedItems] using sourcePins.1
    have reversePins : Relation.TransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill pinnedSource) pinnedSourceCanonical
            pinnedSourceExternalTwoEnded) source := by
      simpa only [sourceMaterial, pinnedSource, pinnedItems] using sourcePins.2
    have middleForward : Relation.TransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill pinnedSource) pinnedSourceCanonical
            pinnedSourceExternalTwoEnded)
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals pinnedItems targetMaterial))
          pinnedTargetValidity.1 pinnedTargetValidity.2) := by
      simpa only [pinnedSourceOccurrence, exactOccurrence] using folded.1
    have middleReverse : Relation.TransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals pinnedItems targetMaterial))
          pinnedTargetValidity.1 pinnedTargetValidity.2)
        (occurrence.interface.withBody
          (occurrence.context.fill pinnedSource) pinnedSourceCanonical
            pinnedSourceExternalTwoEnded) := by
      simpa only [pinnedSourceOccurrence, exactOccurrence] using folded.2
    have unpinForward : Relation.TransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals pinnedItems targetMaterial))
          pinnedTargetValidity.1 pinnedTargetValidity.2)
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems targetMaterial))
          targetCanonical targetExternalTwoEnded) := by
      simpa only [targetOccurrence, exactOccurrence, pinnedItems] using
        targetPins.2
    have unpinReverse : Relation.TransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems targetMaterial))
          targetCanonical targetExternalTwoEnded)
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals pinnedItems targetMaterial))
          pinnedTargetValidity.1 pinnedTargetValidity.2) := by
      simpa only [targetOccurrence, exactOccurrence, pinnedItems] using
        targetPins.1
    exact ⟨(forwardPins.trans middleForward).trans unpinForward,
      (unpinReverse.trans middleReverse).trans reversePins⟩)
    · have empty : outer ++ hostLocals = [] :=
        Classical.not_not.mp nonempty
      have outerEmpty : outer = [] := (List.append_eq_nil_iff.mp empty).1
      have localsEmpty : hostLocals = [] :=
        (List.append_eq_nil_iff.mp empty).2
      subst outer
      subst hostLocals
      have sourceLocalCanonical :
          (Region.adjoinAt [] hostItems sourceMaterial).Canonical :=
        occurrence.context.holeCanonical _ occurrence.sourceCanonical
      have hostCanonical : (Region.mk [] hostItems).Canonical := by
        have canonical := pinnedHostCanonical ([] : List Sig) hostItems
          sourceMaterial sourceLocalCanonical
        simpa only [contextPins, allPins, List.nil_append,
          ItemSeq.pinWires, ItemSeq.nil_append, ItemSeq.append_nil] using
          canonical
      have hostNonempty : ∀ {signature} (wire : Var [] signature),
          (Region.mk [] hostItems).incidencePaths wire.index.val ≠ [] := by
        intro signature wire
        exact Fin.elim0 wire.index
      have folded := normalizedItemsSupportedStrict pattern evidence sites
        hasSelection [] [] rename hostItems occurrence hostCanonical
          hostNonempty targetCanonical targetExternalTwoEnded
      simpa only [sourceMaterial, targetMaterial] using folded
  termination_by 5 * sizeOf sites + 4

  noncomputable def normalizedItemsSupportedStrict
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          pattern frame.sourceKeep frame.selected sourceItems result)
      (sites : ItemsSites operation data evidence)
      (hasSelection : itemsHaveSelection sites = true) :
      ∀ (outer : List Sig) (hostLocals : List Sig)
        (rename : WireRenaming common (outer ++ hostLocals))
        (hostItems : ItemSeq (outer ++ hostLocals))
        {boundary : List Sig} {source : OpenDiagram boundary}
        (occurrence : Occurrence
          (Region.adjoinAt hostLocals hostItems
            (result.renameWires rename)) source)
        (_hostCanonical : (Region.mk hostLocals hostItems).Canonical)
        (_hostNonempty : ∀ {signature} (wire : Var outer signature),
          (Region.mk hostLocals hostItems).incidencePaths wire.index.val ≠ [])
        (targetCanonical :
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems
              (Region.renameWires rename
                (normalizedItems pattern evidence sites).1))).Canonical)
        (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems
              (Region.renameWires rename
                (normalizedItems pattern evidence sites).1)))),
        StrictEquates occurrence
          (Region.adjoinAt hostLocals hostItems
            (Region.renameWires rename (normalizedItems pattern evidence sites).1))
          targetCanonical targetExternalTwoEnded :=
    match sites with
    | .nil _ => by
        simp only [itemsHaveSelection, Bool.false_eq_true] at hasSelection
    | @ItemsSites.cons _ _ _ _ _ _ _ _ item tail itemEndpoint tailResult
        itemEvidence tailEvidence itemSites tailSites => by
        intro outer hostLocals rename hostItems boundary source occurrence
          hostCanonical hostNonempty targetCanonical targetExternalTwoEnded
        let itemBefore := itemEndpoint.renameWires rename
        let tailBefore := tailResult.renameWires rename
        let itemAfter :=
          (Region.renameWires rename (normalizedItem pattern itemEvidence itemSites).1)
        let tailAfter :=
          (Region.renameWires rename (normalizedItems pattern tailEvidence tailSites).1)
        change Occurrence
          (Region.adjoinAt hostLocals hostItems
            ((itemEndpoint.conjoin tailResult).renameWires rename)) source
          at occurrence
        have sourceBeforeCanonical :
            ((itemEndpoint.conjoin tailResult).renameWires rename).Canonical :=
          Region.Canonical.material_of_adjoinAt hostLocals hostItems _
            (occurrence.context.holeCanonical _ occurrence.sourceCanonical)
        have sourceMaterialCanonical :
            (itemBefore.conjoin tailBefore).Canonical := by
          rw [← Region.renameWires_conjoin]
          exact sourceBeforeCanonical
        let sourceOccurrence : Occurrence
            (Region.adjoinAt hostLocals hostItems
              (itemBefore.conjoin tailBefore)) source :=
          supportedAdjoinOccurrence hostLocals hostItems occurrence hostCanonical
            hostNonempty sourceMaterialCanonical (by
              simpa only [itemBefore, tailBefore] using
                RegionIso.renameWiresConjoin itemEndpoint tailResult rename)
        have itemBeforeCanonical :=
          canonical_left_of_conjoin sourceMaterialCanonical
        have tailBeforeCanonical :=
          canonical_right_of_conjoin sourceMaterialCanonical
        let normalizedHead := (normalizedItem pattern itemEvidence itemSites).1
        let normalizedTail := (normalizedItems pattern tailEvidence tailSites).1
        let targetBefore :=
          (normalizedHead.conjoin normalizedTail).renameWires rename
        change (occurrence.context.fill
          (Region.adjoinAt hostLocals hostItems targetBefore)).Canonical
          at targetCanonical
        change OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems targetBefore))
          at targetExternalTwoEnded
        have presentedTargetCanonical :
            (sourceOccurrence.context.fill
              (Region.adjoinAt hostLocals hostItems targetBefore)).Canonical := by
          exact targetCanonical
        have presentedTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            sourceOccurrence.interface.boundaryWire
            (sourceOccurrence.context.fill
              (Region.adjoinAt hostLocals hostItems targetBefore)) := by
          intro signature wire
          exact targetExternalTwoEnded wire
        have targetBeforeCanonical : targetBefore.Canonical :=
          Region.Canonical.material_of_adjoinAt hostLocals hostItems _
            (occurrence.context.holeCanonical _ targetCanonical)
        have targetMaterialCanonical :
            (itemAfter.conjoin tailAfter).Canonical := by
          rw [← Region.renameWires_conjoin]
          exact targetBeforeCanonical
        have itemAfterCanonical :=
          canonical_left_of_conjoin targetMaterialCanonical
        have tailAfterCanonical :=
          canonical_right_of_conjoin targetMaterialCanonical
        by_cases itemSelected : itemHasSelection itemSites = true
        · by_cases tailSelected : itemsHaveSelection tailSites = true
          · exact (by
        have itemPhaseValidity := supportedAdjoinValidity hostLocals hostItems
          sourceOccurrence hostCanonical hostNonempty
          (canonical_conjoin itemAfterCanonical tailBeforeCanonical)
        have itemPhase := normalizedItemWithTailStrict pattern
          itemEvidence itemSites itemSelected hostLocals rename hostItems tailBefore
          sourceOccurrence hostCanonical hostNonempty itemBeforeCanonical
          tailBeforeCanonical itemAfterCanonical itemPhaseValidity.1
          itemPhaseValidity.2
        let afterItem := Region.adjoinAt hostLocals hostItems
          (itemAfter.conjoin tailBefore)
        let afterItemOccurrence : Occurrence afterItem
            (sourceOccurrence.interface.withBody
              (sourceOccurrence.context.fill afterItem) itemPhaseValidity.1
                itemPhaseValidity.2) :=
          exactOccurrence sourceOccurrence.interface sourceOccurrence.context afterItem
            itemPhaseValidity.1 itemPhaseValidity.2
        let flattened := flattenAdjoinOccurrence hostLocals hostItems
          itemAfter tailBefore afterItemOccurrence hostCanonical hostNonempty
          itemAfterCanonical tailBeforeCanonical
        let nextHostItems := Region.extendHostItems hostLocals hostItems
          itemAfter
        let hostWire :=
          Region.adjoinHostWire outer hostLocals itemAfter.locals
        let nextRename := WireRenaming.comp
          hostWire rename
        have nextHostCanonical := extendHostCanonical hostLocals hostItems
          itemAfter hostCanonical itemAfterCanonical
        have nextHostNonempty : ∀ {signature}
            (wire : Var outer signature),
            (Region.mk (hostLocals ++ itemAfter.locals) nextHostItems).incidencePaths
              wire.index.val ≠ [] := by
          intro signature wire
          exact extendHost_incidence_nonempty hostLocals hostItems itemAfter
            hostNonempty wire
        have tailResultCanonical : tailResult.Canonical :=
          (Region.Canonical.renameWires_iff tailResult rename).mp
            tailBeforeCanonical
        have alignedTailCanonical :
            (tailResult.renameWires nextRename).Canonical :=
          (Region.Canonical.renameWires_iff tailResult nextRename).mpr
            tailResultCanonical
        let alignedFlattened : Occurrence
            (Region.adjoinAt (hostLocals ++ itemAfter.locals) nextHostItems
              (tailResult.renameWires nextRename))
            (sourceOccurrence.interface.withBody
              (sourceOccurrence.context.fill afterItem) itemPhaseValidity.1
                itemPhaseValidity.2) :=
          supportedAdjoinOccurrence (hostLocals ++ itemAfter.locals)
            nextHostItems flattened nextHostCanonical nextHostNonempty
            alignedTailCanonical (by
              simpa only [tailBefore, hostWire, nextRename] using
                RegionIso.renameWiresComp tailResult rename hostWire)
        have normalizedTailCanonical : normalizedTail.Canonical :=
          (Region.Canonical.renameWires_iff normalizedTail rename).mp
            tailAfterCanonical
        let flatTargetMaterial := normalizedTail.renameWires nextRename
        have flatTargetMaterialCanonical : flatTargetMaterial.Canonical :=
          (Region.Canonical.renameWires_iff normalizedTail nextRename).mpr
            normalizedTailCanonical
        have tailTargetValidity := supportedAdjoinValidity
          (hostLocals ++ itemAfter.locals) nextHostItems alignedFlattened
          nextHostCanonical nextHostNonempty flatTargetMaterialCanonical
        have tailPhase := normalizedItemsSupportedStrict pattern
          tailEvidence tailSites tailSelected outer
          (hostLocals ++ itemAfter.locals) nextRename
          nextHostItems alignedFlattened nextHostCanonical nextHostNonempty
          tailTargetValidity.1 tailTargetValidity.2
        let flatTarget := Region.adjoinAt
          (hostLocals ++ itemAfter.locals) nextHostItems
          flatTargetMaterial
        let flatTargetEndpoint := alignedFlattened.interface.withBody
          (alignedFlattened.context.fill flatTarget) tailTargetValidity.1
            tailTargetValidity.2
        have finalBodyIso : RegionIso (WireEquiv.refl outer) flatTarget
            (Region.adjoinAt hostLocals hostItems targetBefore) := by
          exact (RegionIso.adjoinAt (hostLocals ++ itemAfter.locals)
            nextHostItems (by
            simpa only [flatTargetMaterial, tailAfter, normalizedTail,
              nextRename, hostWire] using
                (RegionIso.renameWiresComp normalizedTail rename hostWire).symm)).trans
            ((RegionIso.adjoinAtConjoinLeft hostLocals hostItems itemAfter
              tailAfter).symm.trans
              (RegionIso.adjoinAt hostLocals hostItems (by
                simpa only [itemAfter, tailAfter, normalizedHead,
                  normalizedTail, targetBefore] using
                  (RegionIso.renameWiresConjoin normalizedHead normalizedTail rename).symm)))
        have finalIso : OpenDiagramIso flatTargetEndpoint
            (sourceOccurrence.interface.withBody
              (sourceOccurrence.context.fill
                (Region.adjoinAt hostLocals hostItems
                  targetBefore))
              presentedTargetCanonical presentedTargetExternalTwoEnded) :=
          OpenDiagram.withBody_iso tailTargetValidity.1
            presentedTargetCanonical tailTargetValidity.2
            presentedTargetExternalTwoEnded
            (DiagramContext.fillIso sourceOccurrence.context finalBodyIso)
        have tailPhase' : StrictEquates alignedFlattened
            (Region.adjoinAt hostLocals hostItems targetBefore)
            presentedTargetCanonical presentedTargetExternalTwoEnded :=
          StrictEquates.targetIso tailPhase finalIso
        have itemPhase' : StrictEquates sourceOccurrence afterItem
            itemPhaseValidity.1 itemPhaseValidity.2 := by
          simpa only [afterItem, itemBefore, tailBefore, itemAfter,
            sourceOccurrence] using itemPhase
        have combined := StrictEquates.trans
          (targetExternalTwoEnded := presentedTargetExternalTwoEnded)
          itemPhase' tailPhase'
        have outputIso : OpenDiagramIso
            (sourceOccurrence.interface.withBody
              (sourceOccurrence.context.fill
                (Region.adjoinAt hostLocals hostItems targetBefore))
              presentedTargetCanonical presentedTargetExternalTwoEnded)
            (occurrence.interface.withBody
              (occurrence.context.fill
                (Region.adjoinAt hostLocals hostItems targetBefore))
              targetCanonical targetExternalTwoEnded) :=
          OpenDiagram.withBody_iso presentedTargetCanonical targetCanonical
            presentedTargetExternalTwoEnded targetExternalTwoEnded
            (RegionIso.refl _)
        have exactCombined : StrictEquates occurrence
            (Region.adjoinAt hostLocals hostItems targetBefore)
            targetCanonical targetExternalTwoEnded :=
          ⟨transGen_iso (OpenDiagramIso.refl source) combined.1 outputIso,
            transGen_iso outputIso combined.2 (OpenDiagramIso.refl source)⟩
        simpa only [itemBefore, tailBefore, itemAfter, tailAfter,
          sourceOccurrence, afterItem, afterItemOccurrence, flattened,
          alignedFlattened, nextHostItems, hostWire, nextRename,
          flatTargetMaterial, flatTarget, flatTargetEndpoint,
          normalizedHead, normalizedTail, targetBefore, normalizedItems]
          using exactCombined)
          · have tailNone : itemsHaveSelection tailSites = false := by
              cases selected : itemsHaveSelection tailSites with
              | false => rfl
              | true => exact False.elim (tailSelected selected)
            have normalizedTailEq : normalizedTail = tailResult := by
              simpa only [normalizedTail] using
                normalizedItems_eq_of_noSelection pattern tailEvidence
                  tailSites tailNone
            have tailAfterEq : tailAfter = tailBefore := by
              change Region.renameWires rename normalizedTail =
                Region.renameWires rename tailResult
              rw [normalizedTailEq]
            have itemPhaseValidity := supportedAdjoinValidity hostLocals
              hostItems sourceOccurrence hostCanonical hostNonempty
              (canonical_conjoin itemAfterCanonical tailBeforeCanonical)
            have itemPhase := normalizedItemWithTailStrict pattern
              itemEvidence itemSites itemSelected hostLocals rename hostItems
              tailBefore sourceOccurrence hostCanonical hostNonempty
              itemBeforeCanonical tailBeforeCanonical itemAfterCanonical
              itemPhaseValidity.1 itemPhaseValidity.2
            let afterItem := Region.adjoinAt hostLocals hostItems
              (itemAfter.conjoin tailBefore)
            have itemPhase' : StrictEquates sourceOccurrence afterItem
                itemPhaseValidity.1 itemPhaseValidity.2 := by
              simpa only [afterItem, itemBefore, tailBefore, itemAfter,
                sourceOccurrence] using itemPhase
            have materialIso : RegionIso
                (WireEquiv.refl (outer ++ hostLocals))
                (itemAfter.conjoin tailBefore) targetBefore := by
              rw [← tailAfterEq]
              simpa only [itemAfter, tailAfter, normalizedHead,
                normalizedTail, targetBefore] using
                (RegionIso.renameWiresConjoin normalizedHead normalizedTail
                  rename).symm
            have finalBodyIso : RegionIso (WireEquiv.refl outer) afterItem
                (Region.adjoinAt hostLocals hostItems targetBefore) := by
              exact RegionIso.adjoinAt hostLocals hostItems materialIso
            have finalIso : OpenDiagramIso
                (sourceOccurrence.interface.withBody
                  (sourceOccurrence.context.fill afterItem)
                  itemPhaseValidity.1 itemPhaseValidity.2)
                (sourceOccurrence.interface.withBody
                  (sourceOccurrence.context.fill
                    (Region.adjoinAt hostLocals hostItems targetBefore))
                  presentedTargetCanonical
                    presentedTargetExternalTwoEnded) :=
              OpenDiagram.withBody_iso itemPhaseValidity.1
                presentedTargetCanonical itemPhaseValidity.2
                presentedTargetExternalTwoEnded
                (DiagramContext.fillIso sourceOccurrence.context finalBodyIso)
            have presented := StrictEquates.targetIso itemPhase' finalIso
            have outputIso : OpenDiagramIso
                (sourceOccurrence.interface.withBody
                  (sourceOccurrence.context.fill
                    (Region.adjoinAt hostLocals hostItems targetBefore))
                  presentedTargetCanonical
                    presentedTargetExternalTwoEnded)
                (occurrence.interface.withBody
                  (occurrence.context.fill
                    (Region.adjoinAt hostLocals hostItems targetBefore))
                  targetCanonical targetExternalTwoEnded) :=
              OpenDiagram.withBody_iso presentedTargetCanonical
                targetCanonical presentedTargetExternalTwoEnded
                targetExternalTwoEnded (RegionIso.refl _)
            have exactPresented : StrictEquates occurrence
                (Region.adjoinAt hostLocals hostItems targetBefore)
                targetCanonical targetExternalTwoEnded :=
              ⟨transGen_iso (OpenDiagramIso.refl source) presented.1
                  outputIso,
                transGen_iso outputIso presented.2
                  (OpenDiagramIso.refl source)⟩
            simpa only [itemBefore, tailBefore, itemAfter, tailAfter,
              sourceOccurrence, afterItem, normalizedHead, normalizedTail,
              targetBefore, normalizedItems] using exactPresented
        · have itemNone : itemHasSelection itemSites = false := by
            cases selected : itemHasSelection itemSites with
            | false => rfl
            | true => exact False.elim (itemSelected selected)
          have tailSelected : itemsHaveSelection tailSites = true := by
            cases selected : itemsHaveSelection tailSites with
            | true => rfl
            | false =>
                simp only [itemsHaveSelection, itemNone, selected,
                  Bool.false_or, Bool.false_eq_true] at hasSelection
          have normalizedHeadEq : normalizedHead = itemEndpoint := by
            simpa only [normalizedHead] using
              normalizedItem_eq_of_noSelection pattern itemEvidence itemSites
                itemNone
          have itemAfterEq : itemAfter = itemBefore := by
            change Region.renameWires rename normalizedHead =
              Region.renameWires rename itemEndpoint
            rw [normalizedHeadEq]
          let flattened := flattenAdjoinOccurrence hostLocals hostItems
            itemBefore tailBefore sourceOccurrence hostCanonical hostNonempty
            itemBeforeCanonical tailBeforeCanonical
          let nextHostItems := Region.extendHostItems hostLocals hostItems
            itemBefore
          let hostWire :=
            Region.adjoinHostWire outer hostLocals itemBefore.locals
          let nextRename := WireRenaming.comp hostWire rename
          have nextHostCanonical := extendHostCanonical hostLocals hostItems
            itemBefore hostCanonical itemBeforeCanonical
          have nextHostNonempty : ∀ {signature}
              (wire : Var outer signature),
              (Region.mk (hostLocals ++ itemBefore.locals)
                nextHostItems).incidencePaths wire.index.val ≠ [] := by
            intro signature wire
            exact extendHost_incidence_nonempty hostLocals hostItems itemBefore
              hostNonempty wire
          have tailResultCanonical : tailResult.Canonical :=
            (Region.Canonical.renameWires_iff tailResult rename).mp
              tailBeforeCanonical
          have alignedTailCanonical :
              (tailResult.renameWires nextRename).Canonical :=
            (Region.Canonical.renameWires_iff tailResult nextRename).mpr
              tailResultCanonical
          let alignedFlattened : Occurrence
              (Region.adjoinAt (hostLocals ++ itemBefore.locals)
                nextHostItems (tailResult.renameWires nextRename)) source :=
            supportedAdjoinOccurrence (hostLocals ++ itemBefore.locals)
              nextHostItems flattened nextHostCanonical nextHostNonempty
              alignedTailCanonical (by
                simpa only [tailBefore, hostWire, nextRename] using
                  RegionIso.renameWiresComp tailResult rename hostWire)
          have normalizedTailCanonical : normalizedTail.Canonical :=
            (Region.Canonical.renameWires_iff normalizedTail rename).mp
              tailAfterCanonical
          let flatTargetMaterial := normalizedTail.renameWires nextRename
          have flatTargetMaterialCanonical : flatTargetMaterial.Canonical :=
            (Region.Canonical.renameWires_iff normalizedTail nextRename).mpr
              normalizedTailCanonical
          have tailTargetValidity := supportedAdjoinValidity
            (hostLocals ++ itemBefore.locals) nextHostItems alignedFlattened
            nextHostCanonical nextHostNonempty flatTargetMaterialCanonical
          have tailPhase := normalizedItemsSupportedStrict pattern
            tailEvidence tailSites tailSelected outer
            (hostLocals ++ itemBefore.locals) nextRename nextHostItems
            alignedFlattened nextHostCanonical nextHostNonempty
            tailTargetValidity.1 tailTargetValidity.2
          let flatTarget := Region.adjoinAt
            (hostLocals ++ itemBefore.locals) nextHostItems flatTargetMaterial
          let flatTargetEndpoint := alignedFlattened.interface.withBody
            (alignedFlattened.context.fill flatTarget) tailTargetValidity.1
              tailTargetValidity.2
          have finalBodyIso : RegionIso (WireEquiv.refl outer) flatTarget
              (Region.adjoinAt hostLocals hostItems targetBefore) := by
            exact (RegionIso.adjoinAt (hostLocals ++ itemBefore.locals)
              nextHostItems (by
                simpa only [flatTargetMaterial, tailAfter, normalizedTail,
                  nextRename, hostWire] using
                    (RegionIso.renameWiresComp normalizedTail rename hostWire).symm)).trans
              ((RegionIso.adjoinAtConjoinLeft hostLocals hostItems itemBefore
                tailAfter).symm.trans
                (RegionIso.adjoinAt hostLocals hostItems (by
                  rw [← itemAfterEq]
                  simpa only [itemAfter, tailAfter, normalizedHead,
                    normalizedTail, targetBefore] using
                    (RegionIso.renameWiresConjoin normalizedHead normalizedTail
                      rename).symm)))
          have finalIso : OpenDiagramIso flatTargetEndpoint
              (sourceOccurrence.interface.withBody
                (sourceOccurrence.context.fill
                  (Region.adjoinAt hostLocals hostItems targetBefore))
                presentedTargetCanonical
                  presentedTargetExternalTwoEnded) :=
            OpenDiagram.withBody_iso tailTargetValidity.1
              presentedTargetCanonical tailTargetValidity.2
              presentedTargetExternalTwoEnded
              (DiagramContext.fillIso sourceOccurrence.context finalBodyIso)
          have tailPhase' : StrictEquates alignedFlattened
              (Region.adjoinAt hostLocals hostItems targetBefore)
              presentedTargetCanonical presentedTargetExternalTwoEnded :=
            StrictEquates.targetIso tailPhase finalIso
          have presented : StrictEquates sourceOccurrence
              (Region.adjoinAt hostLocals hostItems targetBefore)
              presentedTargetCanonical presentedTargetExternalTwoEnded := by
            simpa only [sourceOccurrence, flattened, alignedFlattened,
              supportedAdjoinOccurrence] using tailPhase'
          have outputIso : OpenDiagramIso
              (sourceOccurrence.interface.withBody
                (sourceOccurrence.context.fill
                  (Region.adjoinAt hostLocals hostItems targetBefore))
                presentedTargetCanonical presentedTargetExternalTwoEnded)
              (occurrence.interface.withBody
                (occurrence.context.fill
                  (Region.adjoinAt hostLocals hostItems targetBefore))
                targetCanonical targetExternalTwoEnded) :=
            OpenDiagram.withBody_iso presentedTargetCanonical targetCanonical
              presentedTargetExternalTwoEnded targetExternalTwoEnded
              (RegionIso.refl _)
          have exactPresented : StrictEquates occurrence
              (Region.adjoinAt hostLocals hostItems targetBefore)
              targetCanonical targetExternalTwoEnded :=
            ⟨transGen_iso (OpenDiagramIso.refl source) presented.1 outputIso,
              transGen_iso outputIso presented.2
                (OpenDiagramIso.refl source)⟩
          simpa only [itemBefore, tailBefore, itemAfter, tailAfter,
            sourceOccurrence, flattened, alignedFlattened, nextHostItems,
            hostWire, nextRename, flatTargetMaterial, flatTarget,
            flatTargetEndpoint, normalizedHead, normalizedTail, targetBefore,
            normalizedItems] using exactPresented
  termination_by 5 * sizeOf sites + 3

  noncomputable def normalizedItemWithTailStrict
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected sourceItem result)
      (sites : ItemSites operation data evidence)
      (hasSelection : itemHasSelection sites = true)
      (hostLocals : List Sig)
      (rename : WireRenaming common (outer ++ hostLocals))
      (hostItems : ItemSeq (outer ++ hostLocals))
      (tail : Region (outer ++ hostLocals))
      {boundary : List Sig} {source : OpenDiagram boundary}
      (occurrence : Occurrence
        (Region.adjoinAt hostLocals hostItems
          ((result.renameWires rename).conjoin tail)) source)
      (hostCanonical : (Region.mk hostLocals hostItems).Canonical)
      (hostNonempty : ∀ {signature} (wire : Var outer signature),
        (Region.mk hostLocals hostItems).incidencePaths wire.index.val ≠ [])
      (itemBeforeCanonical : (result.renameWires rename).Canonical)
      (tailCanonical : tail.Canonical)
      (itemAfterCanonical :
        (Region.renameWires rename
          (normalizedItem pattern evidence sites).1).Canonical)
      (targetCanonical :
        (occurrence.context.fill
          (Region.adjoinAt hostLocals hostItems
            ((Region.renameWires rename
              (normalizedItem pattern evidence sites).1).conjoin
                tail))).Canonical)
      (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire
        (occurrence.context.fill
          (Region.adjoinAt hostLocals hostItems
            ((Region.renameWires rename
              (normalizedItem pattern evidence sites).1).conjoin tail)))) :
      StrictEquates occurrence
        (Region.adjoinAt hostLocals hostItems
          ((Region.renameWires rename
            (normalizedItem pattern evidence sites).1).conjoin tail))
        targetCanonical targetExternalTwoEnded := by
    let itemBefore := result.renameWires rename
    let itemAfter :=
      (Region.renameWires rename (normalizedItem pattern evidence sites).1)
    have swappedCanonical : (tail.conjoin itemBefore).Canonical :=
      canonical_conjoin tailCanonical itemBeforeCanonical
    let swapped := supportedAdjoinOccurrence hostLocals hostItems occurrence
      hostCanonical hostNonempty swappedCanonical
      (RegionIso.conjoinComm itemBefore tail)
    let flattened := flattenAdjoinOccurrence hostLocals hostItems tail
      itemBefore swapped hostCanonical hostNonempty tailCanonical
      itemBeforeCanonical
    let nextHostItems := Region.extendHostItems hostLocals hostItems tail
    let hostWire := Region.adjoinHostWire outer hostLocals tail.locals
    let nextRename := WireRenaming.comp
      hostWire rename
    have nextHostCanonical := extendHostCanonical hostLocals hostItems tail
      hostCanonical tailCanonical
    have nextHostNonempty : ∀ {signature} (wire : Var outer signature),
        (Region.mk (hostLocals ++ tail.locals) nextHostItems).incidencePaths
          wire.index.val ≠ [] := by
      intro signature wire
      exact extendHost_incidence_nonempty hostLocals hostItems tail
        hostNonempty wire
    have resultCanonical : result.Canonical :=
      (Region.Canonical.renameWires_iff result rename).mp itemBeforeCanonical
    have alignedSourceCanonical : (result.renameWires nextRename).Canonical :=
      (Region.Canonical.renameWires_iff result nextRename).mpr resultCanonical
    let alignedFlattened : Occurrence
        (Region.adjoinAt (hostLocals ++ tail.locals) nextHostItems
          (result.renameWires nextRename)) source :=
      supportedAdjoinOccurrence (hostLocals ++ tail.locals) nextHostItems
        flattened nextHostCanonical nextHostNonempty alignedSourceCanonical (by
          simpa only [itemBefore, hostWire, nextRename] using
            RegionIso.renameWiresComp result rename hostWire)
    let normalized := (normalizedItem pattern evidence sites).1
    have normalizedCanonical : normalized.Canonical :=
      (Region.Canonical.renameWires_iff normalized rename).mp
        itemAfterCanonical
    let flatTargetMaterial := normalized.renameWires nextRename
    have flatTargetMaterialCanonical : flatTargetMaterial.Canonical :=
      (Region.Canonical.renameWires_iff normalized nextRename).mpr
        normalizedCanonical
    have flatTargetValidity := supportedAdjoinValidity
      (hostLocals ++ tail.locals) nextHostItems alignedFlattened
      nextHostCanonical nextHostNonempty flatTargetMaterialCanonical
    have core := normalizedItemStrict pattern evidence sites hasSelection
      outer (hostLocals ++ tail.locals) nextRename nextHostItems alignedFlattened
      flatTargetValidity.1 flatTargetValidity.2
    let flatTarget := Region.adjoinAt (hostLocals ++ tail.locals)
      nextHostItems flatTargetMaterial
    let flatEndpoint := alignedFlattened.interface.withBody
      (alignedFlattened.context.fill flatTarget) flatTargetValidity.1
        flatTargetValidity.2
    have finalBodyIso : RegionIso (WireEquiv.refl outer) flatTarget
        (Region.adjoinAt hostLocals hostItems
          (itemAfter.conjoin tail)) := by
      exact (RegionIso.adjoinAt (hostLocals ++ tail.locals) nextHostItems (by
        simpa only [flatTargetMaterial, itemAfter, normalized, nextRename,
          hostWire] using
            (RegionIso.renameWiresComp normalized rename hostWire).symm)).trans
        ((RegionIso.adjoinAtConjoinLeft hostLocals hostItems tail
          itemAfter).symm.trans
          (RegionIso.adjoinAt hostLocals hostItems
            (RegionIso.conjoinComm tail itemAfter)))
    have presentedTargetCanonical :
        (alignedFlattened.context.fill
          (Region.adjoinAt hostLocals hostItems
            (itemAfter.conjoin tail))).Canonical := by
      exact targetCanonical
    have presentedTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        alignedFlattened.interface.boundaryWire
        (alignedFlattened.context.fill
          (Region.adjoinAt hostLocals hostItems
            (itemAfter.conjoin tail))) := by
      intro signature wire
      exact targetExternalTwoEnded wire
    have finalIso : OpenDiagramIso flatEndpoint
        (alignedFlattened.interface.withBody
          (alignedFlattened.context.fill
            (Region.adjoinAt hostLocals hostItems
              (itemAfter.conjoin tail))) presentedTargetCanonical
          presentedTargetExternalTwoEnded) :=
      OpenDiagram.withBody_iso flatTargetValidity.1 presentedTargetCanonical
        flatTargetValidity.2 presentedTargetExternalTwoEnded
        (DiagramContext.fillIso alignedFlattened.context finalBodyIso)
    have presented : StrictEquates alignedFlattened
        (Region.adjoinAt hostLocals hostItems (itemAfter.conjoin tail))
        presentedTargetCanonical presentedTargetExternalTwoEnded :=
      StrictEquates.targetIso core finalIso
    have outputIso : OpenDiagramIso
        (alignedFlattened.interface.withBody
          (alignedFlattened.context.fill
            (Region.adjoinAt hostLocals hostItems (itemAfter.conjoin tail)))
          presentedTargetCanonical presentedTargetExternalTwoEnded)
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems (itemAfter.conjoin tail)))
          targetCanonical targetExternalTwoEnded) :=
      OpenDiagram.withBody_iso presentedTargetCanonical targetCanonical
        presentedTargetExternalTwoEnded targetExternalTwoEnded (RegionIso.refl _)
    have exactPresented : StrictEquates occurrence
        (Region.adjoinAt hostLocals hostItems (itemAfter.conjoin tail))
        targetCanonical targetExternalTwoEnded :=
      ⟨transGen_iso (OpenDiagramIso.refl source) presented.1 outputIso,
        transGen_iso outputIso presented.2 (OpenDiagramIso.refl source)⟩
    simpa only [itemBefore, itemAfter, swapped, flattened, alignedFlattened,
      nextHostItems, hostWire, nextRename, normalized, flatTargetMaterial,
      flatTarget, flatEndpoint] using exactPresented
  termination_by 5 * sizeOf sites + 2

  noncomputable def normalizedItemStrict
      (pattern : OpenDiagram arguments)
      {operation : Transform.Operation arguments}
      {frame : Transform.Frame arguments common sourceWires targetWires}
      {data : operation.Data frame}
      (evidence :
        _root_.VisualProof.Rule.Comprehension.Instantiation.ItemResult
          pattern frame.sourceKeep frame.selected sourceItem result)
      (sites : ItemSites operation data evidence)
      (hasSelection : itemHasSelection sites = true) :
      ∀ (outer : List Sig) (hostLocals : List Sig)
        (rename : WireRenaming common (outer ++ hostLocals))
        (hostItems : ItemSeq (outer ++ hostLocals))
        {boundary : List Sig} {source : OpenDiagram boundary}
        (occurrence : Occurrence
          (Region.adjoinAt hostLocals hostItems
            (result.renameWires rename)) source)
        (targetCanonical :
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems
              (Region.renameWires rename
                (normalizedItem pattern evidence sites).1))).Canonical)
        (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (Region.adjoinAt hostLocals hostItems
              (Region.renameWires rename
                (normalizedItem pattern evidence sites).1)))),
        StrictEquates occurrence
          (Region.adjoinAt hostLocals hostItems
            (Region.renameWires rename (normalizedItem pattern evidence sites).1))
          targetCanonical targetExternalTwoEnded :=
    match sites with
    | .atom head ports => by
        simp only [itemHasSelection, Bool.false_eq_true] at hasSelection
    | .selectedAtom ports _ => by
        intro outer hostLocals rename hostItems boundary source occurrence
          targetCanonical targetExternalTwoEnded
        let mappedPorts := ports.map fun wire => rename wire
        let sourceBefore :=
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern ports).renameWires rename
        let sourceAfter :=
          _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            pattern mappedPorts
        let sourceHostBefore := Region.adjoinAt hostLocals hostItems
          sourceBefore
        let sourceHostAfter := Region.adjoinAt hostLocals hostItems sourceAfter
        change Occurrence sourceHostBefore source at occurrence
        have sourceHostEq : sourceHostBefore = sourceHostAfter := by
          simp only [sourceHostBefore, sourceHostAfter, sourceBefore,
            sourceAfter, mappedPorts, instantiate_renameWires]
        have sourceAfterCanonical : sourceHostAfter.Canonical := by
          rw [← sourceHostEq]
          exact occurrence.context.holeCanonical _ occurrence.sourceCanonical
        have sourceNonempty : ∀ {signature} (wire : Var outer signature),
            sourceHostBefore.incidencePaths wire.index.val ≠ [] ↔
              sourceHostAfter.incidencePaths wire.index.val ≠ [] := by
          intro signature wire
          rw [sourceHostEq]
        let presentedOccurrence : Occurrence sourceHostAfter source :=
          presentationOccurrence occurrence sourceAfterCanonical
            sourceNonempty
            (RegionIso.adjoinAt hostLocals hostItems
              (instantiateRenameIso pattern ports rename))
        let targetBefore := Region.adjoinAt hostLocals hostItems
          ((_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            (identityBoundary pattern) ports).renameWires rename)
        let targetAfter := Region.adjoinAt hostLocals hostItems
          (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
            (identityBoundary pattern) mappedPorts)
        change (occurrence.context.fill targetBefore).Canonical at targetCanonical
        change OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
          (occurrence.context.fill targetBefore) at targetExternalTwoEnded
        have targetEq : targetBefore = targetAfter := by
          simp only [targetBefore, targetAfter, mappedPorts,
            instantiate_renameWires]
        have targetAfterCanonical : targetAfter.Canonical := by
          rw [← targetEq]
          exact occurrence.context.holeCanonical _ targetCanonical
        have targetNonempty : ∀ {signature} (wire : Var outer signature),
            targetBefore.incidencePaths wire.index.val ≠ [] ↔
              targetAfter.incidencePaths wire.index.val ≠ [] := by
          intro signature wire
          rw [targetEq]
        have targetReplacement := occurrence.context.replaceCanonical
          targetBefore targetAfter targetCanonical targetAfterCanonical
            targetNonempty
        let targetBeforeEndpoint := occurrence.interface.withBody
          (occurrence.context.fill targetBefore) targetCanonical
            targetExternalTwoEnded
        have targetAfterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            occurrence.interface.boundaryWire
            (occurrence.context.fill targetAfter) :=
          targetBeforeEndpoint.externalTwoEnded_of_nonempty_iff _
            targetReplacement.2
        have presentedTargetCanonical :
            (presentedOccurrence.context.fill targetAfter).Canonical := by
          exact targetReplacement.1
        have presentedTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            presentedOccurrence.interface.boundaryWire
            (presentedOccurrence.context.fill targetAfter) := by
          intro signature wire
          exact targetAfterExternalTwoEnded wire
        obtain ⟨ownedTargetCanonical, ownedTargetExternalTwoEnded,
            equivalent⟩ :=
          equatesIdentityBoundary pattern mappedPorts presentedOccurrence
        have strict := strictEquates_of_equates presentedOccurrence equivalent
        have finalBodyIso : RegionIso (WireEquiv.refl outer) targetAfter
            targetBefore :=
          RegionIso.adjoinAt hostLocals hostItems
            (instantiateRenameIso (identityBoundary pattern) ports rename).symm
        have finalIso : OpenDiagramIso
            (presentedOccurrence.interface.withBody
              (presentedOccurrence.context.fill targetAfter)
              ownedTargetCanonical ownedTargetExternalTwoEnded)
            (occurrence.interface.withBody
              (occurrence.context.fill targetBefore) targetCanonical
                targetExternalTwoEnded) :=
          OpenDiagram.withBody_iso ownedTargetCanonical targetCanonical
            ownedTargetExternalTwoEnded targetExternalTwoEnded
            (DiagramContext.fillIso occurrence.context finalBodyIso)
        have presented := StrictEquates.targetIso strict finalIso
        simpa only [normalizedItem, targetBefore, sourceHostBefore,
          sourceBefore] using presented
    | .identity signature arity ports => by
        simp only [itemHasSelection, Bool.false_eq_true] at hasSelection
    | @ItemSites.cut _ _ _ _ _ _ _ _ body childResult childEvidence
        childSites => by
        intro outer hostLocals rename hostItems boundary source occurrence
          targetCanonical targetExternalTwoEnded
        let appendNil : WireRenaming common (common ++ []) :=
          ⟨fun wire => wire.appendLeft []⟩
        let materialRename := Region.adjoinMaterialWire outer hostLocals []
        let childRename := WireRenaming.comp materialRename
          (WireRenaming.comp (rename.appendRight []) appendNil)
        let retained := hostItems.renameWires
          (Region.adjoinHostWire outer hostLocals [])
        let inner : DiagramContext outer (outer ++ (hostLocals ++ [])) :=
          .cut (hostLocals ++ []) retained .nil .hole
        have childRename_eq (region : Region common) :
            Region.renameWires materialRename
                (Region.renameWires (rename.appendRight [])
                  (Region.renameWires appendNil region)) =
              Region.renameWires childRename region := by
          rw [Region.renameWires_comp, Region.renameWires_comp]
          apply congrArg (fun map => Region.renameWires map region)
          apply WireRenaming.ext
          intro signature wire
          rfl
        let sourceBefore := Region.adjoinAt hostLocals hostItems
          ((Region.singleton (.cut childResult)).renameWires rename)
        let sourceAfter := inner.fill (childResult.renameWires childRename)
        change Occurrence sourceBefore source at occurrence
        have sourceEq : sourceBefore = sourceAfter := by
          simp only [inner, retained, childRename, materialRename, appendNil,
            sourceBefore, sourceAfter, DiagramContext.fill,
            Region.renameWires, Region.singleton, Region.ofItems,
            Region.adjoinAt, ItemSeq.renameWires, Item.renameWires]
          rw [childRename_eq]
        have sourceAfterCanonical : sourceAfter.Canonical := by
          rw [← sourceEq]
          exact occurrence.context.holeCanonical _ occurrence.sourceCanonical
        have sourceNonempty : ∀ {signature} (wire : Var outer signature),
            sourceBefore.incidencePaths wire.index.val ≠ [] ↔
              sourceAfter.incidencePaths wire.index.val ≠ [] := by
          intro signature wire
          rw [sourceEq]
        let outerOccurrence : Occurrence sourceAfter source :=
          presentationOccurrence occurrence sourceAfterCanonical
            sourceNonempty (by
              rw [← sourceEq]
              exact RegionIso.refl _)
        let childOccurrence := Occurrence.nest outerOccurrence
        let normalizedChild :=
          (normalizedRegion pattern childEvidence childSites).1
        let targetBefore := Region.adjoinAt hostLocals hostItems
          (Region.renameWires rename
            (normalizedItem pattern evidence (.cut childSites)).1)
        let targetAfter := inner.fill
          (Region.renameWires childRename normalizedChild)
        change (occurrence.context.fill targetBefore).Canonical at targetCanonical
        change OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
          (occurrence.context.fill targetBefore) at targetExternalTwoEnded
        have targetEq : targetBefore = targetAfter := by
          simp only [normalizedItem, inner, retained, childRename,
            materialRename, appendNil, normalizedChild, targetBefore,
            targetAfter, DiagramContext.fill, Region.renameWires,
            Region.singleton, Region.ofItems, Region.adjoinAt,
            ItemSeq.renameWires, Item.renameWires]
          rw [childRename_eq]
        have targetAfterCanonical : targetAfter.Canonical := by
          rw [← targetEq]
          exact occurrence.context.holeCanonical _ targetCanonical
        have targetNonempty : ∀ {signature} (wire : Var outer signature),
            targetBefore.incidencePaths wire.index.val ≠ [] ↔
              targetAfter.incidencePaths wire.index.val ≠ [] := by
          intro signature wire
          rw [targetEq]
        have targetReplacement := occurrence.context.replaceCanonical
          targetBefore targetAfter targetCanonical targetAfterCanonical
            targetNonempty
        let targetBeforeEndpoint := occurrence.interface.withBody
          (occurrence.context.fill targetBefore) targetCanonical
            targetExternalTwoEnded
        have targetAfterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            occurrence.interface.boundaryWire
            (occurrence.context.fill targetAfter) :=
          targetBeforeEndpoint.externalTwoEnded_of_nonempty_iff _
            targetReplacement.2
        have outerTargetCanonical :
            (outerOccurrence.context.fill targetAfter).Canonical := by
          exact targetReplacement.1
        have outerTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            outerOccurrence.interface.boundaryWire
            (outerOccurrence.context.fill targetAfter) := by
          intro signature wire
          exact targetAfterExternalTwoEnded wire
        have childTargetCanonical :
            (childOccurrence.context.fill
              (Region.renameWires childRename normalizedChild)).Canonical := by
          simpa only [childOccurrence, Occurrence.nest,
            DiagramContext.fill_comp, targetAfter] using outerTargetCanonical
        have childTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
            childOccurrence.interface.boundaryWire
            (childOccurrence.context.fill
              (Region.renameWires childRename normalizedChild)) := by
          intro signature wire
          simpa only [childOccurrence, Occurrence.nest,
            DiagramContext.fill_comp, targetAfter] using
              outerTargetExternalTwoEnded wire
        have childSelection : regionHasSelection childSites = true := by
          simpa only [itemHasSelection] using hasSelection
        have child := normalizedRegionStrict pattern childEvidence
          childSites childSelection (outer ++ (hostLocals ++ [])) childRename
          childOccurrence
          childTargetCanonical
          childTargetExternalTwoEnded
        have finalBodyIso : RegionIso (WireEquiv.refl outer) targetAfter
            targetBefore := by
          rw [← targetEq]
          exact RegionIso.refl _
        have outerFinalIso : OpenDiagramIso
            (outerOccurrence.interface.withBody
              (outerOccurrence.context.fill targetAfter)
              outerTargetCanonical outerTargetExternalTwoEnded)
            (occurrence.interface.withBody
              (occurrence.context.fill targetBefore) targetCanonical
                targetExternalTwoEnded) :=
          OpenDiagram.withBody_iso outerTargetCanonical targetCanonical
            outerTargetExternalTwoEnded targetExternalTwoEnded
            (DiagramContext.fillIso occurrence.context finalBodyIso)
        have finalIso : OpenDiagramIso
            (childOccurrence.interface.withBody
              (childOccurrence.context.fill
                (Region.renameWires childRename normalizedChild))
              childTargetCanonical childTargetExternalTwoEnded)
            (occurrence.interface.withBody
              (occurrence.context.fill targetBefore) targetCanonical
                targetExternalTwoEnded) := by
          simpa only [childOccurrence, Occurrence.nest,
            DiagramContext.fill_comp, targetAfter] using outerFinalIso
        have exactChild : StrictEquates occurrence targetBefore targetCanonical
            targetExternalTwoEnded :=
          ⟨transGen_iso (OpenDiagramIso.refl source) child.1 finalIso,
            transGen_iso finalIso child.2 (OpenDiagramIso.refl source)⟩
        simpa only [targetBefore, normalizedItem, sourceBefore] using exactChild
  termination_by 5 * sizeOf sites + 1
end

/-- Normalize every selected application in one exact authoritative item
sequence and connect the actual occurrence bidirectionally to the generated
identity-boundary instantiation. -/
theorem normalizeItemsEquates
    {arguments outer hostLocals sourceWires targetWires : List Sig}
    (pattern : OpenDiagram arguments)
    {operation : Transform.Operation arguments}
    {frame : Transform.Frame arguments (outer ++ hostLocals) sourceWires
      targetWires}
    {data : operation.Data frame}
    {source : ItemSeq sourceWires}
    {result : Region (outer ++ hostLocals)}
    (evidence :
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        pattern frame.sourceKeep frame.selected source result)
    (sites : ItemsSites operation data evidence)
    {boundary : List Sig} {host : OpenDiagram boundary}
    (occurrence : Occurrence
      (Region.adjoinAt hostLocals .nil result) host) :
    ∃ normalized : Region (outer ++ hostLocals),
      _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          (identityBoundary pattern) frame.sourceKeep frame.selected source
            normalized ∧
        ∃ targetCanonical :
            (occurrence.context.fill
              (Region.adjoinAt hostLocals .nil normalized)).Canonical,
          ∃ targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
              occurrence.interface.boundaryWire
              (occurrence.context.fill
                (Region.adjoinAt hostLocals .nil normalized)),
            let reconstructed := occurrence.interface.withBody
              (occurrence.context.fill
                (Region.adjoinAt hostLocals .nil normalized))
              targetCanonical targetExternalTwoEnded
            let target := if itemsHaveSelection sites = false then host
              else reconstructed
            OpenDiagram.Isomorphic target reconstructed ∧
              Relation.ReflTransGen Step host target ∧
                Relation.ReflTransGen Step target host := by
  let output := normalizedItems pattern evidence sites
  by_cases noSelection : itemsHaveSelection sites = false
  · have outputEq : output.1 = result := by
      simpa only [output] using
        normalizedItems_eq_of_noSelection pattern evidence sites noSelection
    have targetCanonical :
        (occurrence.context.fill
          (Region.adjoinAt hostLocals .nil output.1)).Canonical := by
      rw [outputEq]
      exact occurrence.sourceCanonical
    have targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire
        (occurrence.context.fill
          (Region.adjoinAt hostLocals .nil output.1)) := by
      intro signature wire
      rw [outputEq]
      exact occurrence.sourceExternalTwoEnded wire
    have targetIsomorphic : OpenDiagram.Isomorphic host
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals .nil output.1))
          targetCanonical targetExternalTwoEnded) := by
      exact ⟨by simpa only [outputEq] using occurrence.host_iso⟩
    refine ⟨output.1, output.2, targetCanonical,
      targetExternalTwoEnded, ?_⟩
    dsimp only
    rw [if_pos noSelection]
    exact ⟨targetIsomorphic,
      Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  · exact (by
  let sourceRegion := Region.adjoinAt hostLocals .nil result
  let targetRegion := Region.adjoinAt hostLocals .nil output.1
  let materialScope := normalizedItems_scope pattern evidence sites
  let regionScope := adjoinAt_preserves_scope hostLocals
    (.nil : ItemSeq (outer ++ hostLocals)) result output.1 materialScope
  have sourceLocalCanonical : sourceRegion.Canonical := by
    exact occurrence.context.holeCanonical _ occurrence.sourceCanonical
  have targetLocalCanonical : targetRegion.Canonical :=
    regionScope.canonical sourceLocalCanonical
  have replacement := occurrence.context.replaceCanonical sourceRegion
    targetRegion occurrence.sourceCanonical targetLocalCanonical
      regionScope.incidenceNonempty
  let sourceEndpoint := occurrence.interface.withBody
    (occurrence.context.fill sourceRegion) occurrence.sourceCanonical
      occurrence.sourceExternalTwoEnded
  have targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill targetRegion) :=
    sourceEndpoint.externalTwoEnded_of_nonempty_iff
      (occurrence.context.fill targetRegion) replacement.2
  have targetCanonical : (occurrence.context.fill targetRegion).Canonical :=
    replacement.1
  have hasSelection : itemsHaveSelection sites = true := by
    cases selected : itemsHaveSelection sites with
    | false => exact False.elim (noSelection selected)
    | true => rfl
  let identity : WireRenaming (outer ++ hostLocals)
      (outer ++ hostLocals) := WireRenaming.id
  let presentedOccurrence : Occurrence
      (Region.adjoinAt hostLocals .nil (result.renameWires identity)) host := {
    interface := occurrence.interface
    context := occurrence.context
    sourceCanonical := by
      simpa only [identity, Region.renameWires_id] using occurrence.sourceCanonical
    sourceExternalTwoEnded := by
      intro signature wire
      simpa only [identity, Region.renameWires_id] using
        occurrence.sourceExternalTwoEnded wire
    host_iso := by
      simpa only [identity, Region.renameWires_id] using occurrence.host_iso
  }
  have folded := normalizedItemsStrict (outer := outer) pattern evidence sites
    hasSelection hostLocals identity (.nil : ItemSeq (outer ++ hostLocals))
      presentedOccurrence (by
        simpa only [presentedOccurrence, targetRegion, identity,
          Region.renameWires_id] using
          targetCanonical) (by
        intro signature wire
        simpa only [presentedOccurrence, targetRegion, identity,
          Region.renameWires_id] using
          targetExternalTwoEnded wire)
  have exactStrict : StrictEquates occurrence targetRegion targetCanonical
      targetExternalTwoEnded := by
    simpa only [presentedOccurrence, targetRegion, identity,
      Region.renameWires_id] using folded
  have equivalent := exactStrict.toEquates
  refine ⟨output.1, output.2, targetCanonical,
    targetExternalTwoEnded, ?_⟩
  dsimp only
  rw [if_neg noSelection]
  exact ⟨OpenDiagram.Isomorphic.refl _, equivalent.1, equivalent.2⟩)


end EqualityNormalization

end VisualProof.Rule.Completeness.Comprehension
