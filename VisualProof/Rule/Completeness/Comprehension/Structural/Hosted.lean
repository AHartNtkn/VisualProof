import VisualProof.Rule.Completeness.Comprehension.Normalization.Support

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

/-- A strict transformation stable under every surrounding supported item
host and every inherited-wire renaming. -/
def HostedStrict (before after : Region common) : Prop :=
  ∀ (outer hostLocals : List Sig)
    (rename : WireRenaming common (outer ++ hostLocals))
    (hostItems : ItemSeq (outer ++ hostLocals))
    {boundary : List Sig} {source : OpenDiagram boundary}
    (occurrence : Occurrence
      (Region.adjoinAt hostLocals hostItems
        (before.renameWires rename)) source)
    (targetCanonical :
      (occurrence.context.fill
        (Region.adjoinAt hostLocals hostItems
          (after.renameWires rename))).Canonical)
    (targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill
        (Region.adjoinAt hostLocals hostItems
          (after.renameWires rename)))),
    EqualityNormalization.StrictEquates occurrence
      (Region.adjoinAt hostLocals hostItems (after.renameWires rename))
      targetCanonical targetExternalTwoEnded

/-- The canonical nonempty loop witnesses hosted strict reflexivity. -/
theorem HostedStrict.refl (region : Region common) :
    HostedStrict region region := by
  intro outer hostLocals rename hostItems boundary source occurrence
    targetCanonical targetExternalTwoEnded
  exact EqualityNormalization.StrictEquates.refl occurrence

/-- Reverse a hosted strict equivalence without changing its host or wire
substitution. -/
theorem HostedStrict.symm
    {before after : Region common}
    (transformation : HostedStrict before after) :
    HostedStrict after before := by
  intro outer hostLocals rename hostItems boundary source occurrence
    targetCanonical targetExternalTwoEnded
  let hostedBefore := Region.adjoinAt hostLocals hostItems
    (before.renameWires rename)
  let hostedAfter := Region.adjoinAt hostLocals hostItems
    (after.renameWires rename)
  change Occurrence hostedAfter source at occurrence
  change (occurrence.context.fill hostedBefore).Canonical at targetCanonical
  change OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
    (occurrence.context.fill hostedBefore) at targetExternalTwoEnded
  let beforeEndpoint := occurrence.interface.withBody
    (occurrence.context.fill hostedBefore) targetCanonical
      targetExternalTwoEnded
  let beforeOccurrence : Occurrence hostedBefore beforeEndpoint :=
    exactOccurrence occurrence.interface occurrence.context hostedBefore
      targetCanonical targetExternalTwoEnded
  have core := transformation outer hostLocals rename hostItems
    beforeOccurrence occurrence.sourceCanonical
      occurrence.sourceExternalTwoEnded
  have forward := transGen_iso occurrence.host_iso.symm core.2
    (OpenDiagramIso.refl beforeEndpoint)
  have reverse := transGen_iso (OpenDiagramIso.refl beforeEndpoint) core.1
    occurrence.host_iso.symm
  exact ⟨forward, reverse⟩

/-- Transport a hosted strict equivalence across structural presentations of
both endpoints. -/
theorem HostedStrict.iso
    {before before' after after' : Region common}
    (sourceIso : RegionIso (WireEquiv.refl common) before' before)
    (targetIso : RegionIso (WireEquiv.refl common) after after')
    (transformation : HostedStrict before after) :
    HostedStrict before' after' := by
  intro outer hostLocals rename hostItems boundary source occurrence
    targetCanonical targetExternalTwoEnded
  let sourceBefore := Region.adjoinAt hostLocals hostItems
    (before'.renameWires rename)
  let sourceAfter := Region.adjoinAt hostLocals hostItems
    (before.renameWires rename)
  change Occurrence sourceBefore source at occurrence
  let mappedSourceIso : RegionIso (WireEquiv.refl (outer ++ hostLocals))
      (before'.renameWires rename) (before.renameWires rename) :=
    RegionIso.renameExisting sourceIso rename rename
      (WireEquiv.refl (outer ++ hostLocals)) (fun _ => rfl)
  let hostedSourceIso : RegionIso (WireEquiv.refl outer)
      sourceBefore sourceAfter :=
    RegionIso.adjoinAt hostLocals hostItems mappedSourceIso
  have sourceAfterCanonical : sourceAfter.Canonical :=
    hostedSourceIso.canonical_iff.mp
      (occurrence.context.holeCanonical sourceBefore
        occurrence.sourceCanonical)
  let sourceScope := ScopePreservation.ofIso hostedSourceIso
  let presentedOccurrence : Occurrence sourceAfter source :=
    EqualityNormalization.presentationOccurrence occurrence
      sourceAfterCanonical sourceScope.incidenceNonempty hostedSourceIso
  let targetBefore := Region.adjoinAt hostLocals hostItems
    (after'.renameWires rename)
  let targetAfter := Region.adjoinAt hostLocals hostItems
    (after.renameWires rename)
  change (occurrence.context.fill targetBefore).Canonical at targetCanonical
  change OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
    (occurrence.context.fill targetBefore) at targetExternalTwoEnded
  let mappedTargetIso : RegionIso (WireEquiv.refl (outer ++ hostLocals))
      (after.renameWires rename) (after'.renameWires rename) :=
    RegionIso.renameExisting targetIso rename rename
      (WireEquiv.refl (outer ++ hostLocals)) (fun _ => rfl)
  let hostedTargetIso : RegionIso (WireEquiv.refl outer)
      targetAfter targetBefore :=
    RegionIso.adjoinAt hostLocals hostItems mappedTargetIso
  have targetAfterCanonical : targetAfter.Canonical :=
    hostedTargetIso.canonical_iff.mpr
      (occurrence.context.holeCanonical targetBefore targetCanonical)
  let targetScope := ScopePreservation.ofIso hostedTargetIso.symm
  have targetReplacement := occurrence.context.replaceCanonical
    targetBefore targetAfter targetCanonical targetAfterCanonical
      targetScope.incidenceNonempty
  let targetBeforeEndpoint := occurrence.interface.withBody
    (occurrence.context.fill targetBefore) targetCanonical
      targetExternalTwoEnded
  have targetAfterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill targetAfter) :=
    targetBeforeEndpoint.externalTwoEnded_of_nonempty_iff _
      targetReplacement.2
  have core := transformation outer hostLocals rename hostItems
    presentedOccurrence targetReplacement.1 targetAfterExternalTwoEnded
  let finalIso : OpenDiagramIso
      (presentedOccurrence.interface.withBody
        (presentedOccurrence.context.fill targetAfter)
        targetReplacement.1 targetAfterExternalTwoEnded)
      (occurrence.interface.withBody
        (occurrence.context.fill targetBefore)
        targetCanonical targetExternalTwoEnded) :=
    OpenDiagram.withBody_iso targetReplacement.1 targetCanonical
      targetAfterExternalTwoEnded targetExternalTwoEnded
      (DiagramContext.fillIso occurrence.context hostedTargetIso)
  exact ⟨transGen_iso (OpenDiagramIso.refl source) core.1 finalIso,
    transGen_iso finalIso core.2 (OpenDiagramIso.refl source)⟩

/-- Every structural presentation is a hosted strict equivalence. -/
theorem HostedStrict.ofIso
    {before after : Region common}
    (presentation : RegionIso (WireEquiv.refl common) before after) :
    HostedStrict before after := by
  exact HostedStrict.iso (RegionIso.refl before) presentation
    (HostedStrict.refl before)

/-- Compose hosted strict equivalences when the final endpoint supplies the
scope facts needed to validate the shared middle endpoint in every host. -/
theorem HostedStrict.trans
    {before middle after : Region common}
    (first : HostedStrict before middle)
    (second : HostedStrict middle after)
    (middleScope : ∀ (outer hostLocals : List Sig)
      (rename : WireRenaming common (outer ++ hostLocals))
      (hostItems : ItemSeq (outer ++ hostLocals)),
      ScopePreservation
        (Region.adjoinAt hostLocals hostItems (after.renameWires rename))
        (Region.adjoinAt hostLocals hostItems (middle.renameWires rename))) :
    HostedStrict before after := by
  intro outer hostLocals rename hostItems boundary source occurrence
    targetCanonical targetExternalTwoEnded
  let hostedBefore := Region.adjoinAt hostLocals hostItems
    (before.renameWires rename)
  let hostedMiddle := Region.adjoinAt hostLocals hostItems
    (middle.renameWires rename)
  let hostedAfter := Region.adjoinAt hostLocals hostItems
    (after.renameWires rename)
  change Occurrence hostedBefore source at occurrence
  change (occurrence.context.fill hostedAfter).Canonical at targetCanonical
  change OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
    (occurrence.context.fill hostedAfter) at targetExternalTwoEnded
  have reverseScope : ScopePreservation hostedAfter hostedMiddle :=
    middleScope outer hostLocals rename hostItems
  have middleCanonical : hostedMiddle.Canonical :=
    reverseScope.canonical
      (occurrence.context.holeCanonical hostedAfter targetCanonical)
  have middleReplacement := occurrence.context.replaceCanonical
    hostedAfter hostedMiddle targetCanonical middleCanonical
      reverseScope.incidenceNonempty
  let afterEndpoint := occurrence.interface.withBody
    (occurrence.context.fill hostedAfter) targetCanonical
      targetExternalTwoEnded
  have middleExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill hostedMiddle) :=
    afterEndpoint.externalTwoEnded_of_nonempty_iff _ middleReplacement.2
  have firstCore := first outer hostLocals rename hostItems occurrence
    middleReplacement.1 middleExternalTwoEnded
  let middleEndpoint := occurrence.interface.withBody
    (occurrence.context.fill hostedMiddle) middleReplacement.1
      middleExternalTwoEnded
  let middleOccurrence : Occurrence hostedMiddle middleEndpoint :=
    exactOccurrence occurrence.interface occurrence.context hostedMiddle
      middleReplacement.1 middleExternalTwoEnded
  have secondCore := second outer hostLocals rename hostItems middleOccurrence
    targetCanonical targetExternalTwoEnded
  exact EqualityNormalization.StrictEquates.trans firstCore secondCore

/-- Specialize a hosted transformation along one fixed wire substitution. -/
theorem HostedStrict.specialize
    {before after : Region sourceWires}
    (transformation : HostedStrict before after)
    (baseRename : WireRenaming sourceWires common)
    {mappedBefore mappedAfter : Region common}
    (beforeEq : before.renameWires baseRename = mappedBefore)
    (afterEq : after.renameWires baseRename = mappedAfter) :
    HostedStrict mappedBefore mappedAfter := by
  intro outer hostLocals rename hostItems boundary source occurrence
    targetCanonical targetExternalTwoEnded
  let combined := WireRenaming.comp rename baseRename
  let sourceBefore := Region.adjoinAt hostLocals hostItems
    (mappedBefore.renameWires rename)
  let sourceAfter := Region.adjoinAt hostLocals hostItems
    (before.renameWires combined)
  change Occurrence sourceBefore source at occurrence
  have sourceEq : sourceBefore = sourceAfter := by
    simp only [sourceBefore, sourceAfter, combined, ← beforeEq,
      Region.renameWires_comp]
  have sourceAfterCanonical : sourceAfter.Canonical := by
    rw [← sourceEq]
    exact occurrence.context.holeCanonical sourceBefore
      occurrence.sourceCanonical
  have sourceNonempty : ∀ {signature} (wire : Var outer signature),
      sourceBefore.incidencePaths wire.index.val ≠ [] ↔
        sourceAfter.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    rw [sourceEq]
  let presentedOccurrence : Occurrence sourceAfter source :=
    EqualityNormalization.presentationOccurrence occurrence
      sourceAfterCanonical sourceNonempty (RegionIso.ofEq sourceEq)
  let targetBefore := Region.adjoinAt hostLocals hostItems
    (mappedAfter.renameWires rename)
  let targetAfter := Region.adjoinAt hostLocals hostItems
    (after.renameWires combined)
  change (occurrence.context.fill targetBefore).Canonical at targetCanonical
  change OpenDiagram.ExternalTwoEnded occurrence.interface.boundaryWire
    (occurrence.context.fill targetBefore) at targetExternalTwoEnded
  have targetEq : targetBefore = targetAfter := by
    simp only [targetBefore, targetAfter, combined, ← afterEq,
      Region.renameWires_comp]
  have targetAfterCanonical : targetAfter.Canonical := by
    rw [← targetEq]
    exact occurrence.context.holeCanonical targetBefore targetCanonical
  have targetNonempty : ∀ {signature} (wire : Var outer signature),
      targetBefore.incidencePaths wire.index.val ≠ [] ↔
        targetAfter.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    rw [targetEq]
  have targetReplacement := occurrence.context.replaceCanonical
    targetBefore targetAfter targetCanonical targetAfterCanonical targetNonempty
  let targetBeforeEndpoint := occurrence.interface.withBody
    (occurrence.context.fill targetBefore) targetCanonical
      targetExternalTwoEnded
  have targetAfterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill targetAfter) :=
    targetBeforeEndpoint.externalTwoEnded_of_nonempty_iff _
      targetReplacement.2
  have core := transformation outer hostLocals combined hostItems
    presentedOccurrence targetReplacement.1 targetAfterExternalTwoEnded
  let targetIso : OpenDiagramIso
      (presentedOccurrence.interface.withBody
        (presentedOccurrence.context.fill targetAfter)
        targetReplacement.1 targetAfterExternalTwoEnded)
      (occurrence.interface.withBody
        (occurrence.context.fill targetBefore)
        targetCanonical targetExternalTwoEnded) :=
    OpenDiagram.withBody_iso targetReplacement.1 targetCanonical
      targetAfterExternalTwoEnded targetExternalTwoEnded
      (DiagramContext.fillIso occurrence.context
        (RegionIso.ofEq targetEq.symm))
  exact ⟨transGen_iso (OpenDiagramIso.refl source) core.1 targetIso,
    transGen_iso targetIso core.2 (OpenDiagramIso.refl source)⟩

/-- Lift a hosted strict transformation beneath one locally bound region. -/
theorem HostedStrict.adjoinAt
    {common : List Sig} (locals : List Sig)
    (before after : Region (common ++ locals))
    (transformation : HostedStrict before after) :
    HostedStrict (Region.adjoinAt locals .nil before)
      (Region.adjoinAt locals .nil after) := by
  intro outer hostLocals rename hostItems boundary source
    hostedOccurrence targetCanonical targetExternalTwoEnded
  let childRename := rename.appendRight locals
  let assoc := WireEquiv.adjoinMaterialAssoc outer hostLocals
    locals
  let nextRename := WireRenaming.comp assoc.toRenaming childRename
  let nextHostItems := Region.extendHostItems hostLocals hostItems
    (.mk locals .nil)
  let sourceBefore := Region.adjoinAt hostLocals hostItems
    ((Region.adjoinAt locals .nil before).renameWires rename)
  let sourceAfter := Region.adjoinAt (hostLocals ++ locals)
    nextHostItems (before.renameWires nextRename)
  change Occurrence sourceBefore source at hostedOccurrence
  let sourceNested := RegionIso.adjoinAt hostLocals hostItems
    (RegionIso.renameWiresAdjoinAtNil before rename)
  let sourceAssociated :=
    (RegionIso.adjoinAtAssoc hostLocals hostItems locals .nil
      (before.renameWires childRename)).symm
  let sourceCombined := RegionIso.adjoinAt
    (hostLocals ++ locals) nextHostItems
    (RegionIso.renameWiresComp before childRename
      assoc.toRenaming)
  let sourcePresentation : RegionIso (WireEquiv.refl outer)
      sourceBefore sourceAfter :=
    (sourceNested.trans sourceAssociated).trans sourceCombined
  have sourceAfterCanonical : sourceAfter.Canonical :=
    sourcePresentation.canonical_iff.mp
      (hostedOccurrence.context.holeCanonical _
        hostedOccurrence.sourceCanonical)
  have sourceSameNonempty : ∀ {signature} (wire : Var outer signature),
      sourceBefore.incidencePaths wire.index.val ≠ [] ↔
        sourceAfter.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    have lengthEq := sourcePresentation.incidencePaths_length_eq wire
    exact ⟨fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [← lengthEq], fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [lengthEq]⟩
  let presentedOccurrence : Occurrence sourceAfter source :=
    EqualityNormalization.presentationOccurrence hostedOccurrence
      sourceAfterCanonical sourceSameNonempty sourcePresentation
  let targetBefore := Region.adjoinAt hostLocals hostItems
    ((Region.adjoinAt locals .nil after).renameWires rename)
  let targetAfter := Region.adjoinAt (hostLocals ++ locals)
    nextHostItems (after.renameWires nextRename)
  let targetNested := RegionIso.adjoinAt hostLocals hostItems
    (RegionIso.renameWiresAdjoinAtNil after rename)
  let targetAssociated :=
    (RegionIso.adjoinAtAssoc hostLocals hostItems locals .nil
      (after.renameWires childRename)).symm
  let targetCombined := RegionIso.adjoinAt
    (hostLocals ++ locals) nextHostItems
    (RegionIso.renameWiresComp after childRename
      assoc.toRenaming)
  let targetPresentation : RegionIso (WireEquiv.refl outer)
      targetBefore targetAfter :=
    (targetNested.trans targetAssociated).trans targetCombined
  have targetAfterLocalCanonical : targetAfter.Canonical :=
    targetPresentation.canonical_iff.mp
      (hostedOccurrence.context.holeCanonical _ targetCanonical)
  have targetSameNonempty : ∀ {signature} (wire : Var outer signature),
      targetBefore.incidencePaths wire.index.val ≠ [] ↔
        targetAfter.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    have lengthEq := targetPresentation.incidencePaths_length_eq wire
    exact ⟨fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [← lengthEq], fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [lengthEq]⟩
  have targetReplacement := hostedOccurrence.context.replaceCanonical
    targetBefore targetAfter targetCanonical targetAfterLocalCanonical
    targetSameNonempty
  let targetBeforeEndpoint := hostedOccurrence.interface.withBody
    (hostedOccurrence.context.fill targetBefore) targetCanonical
    targetExternalTwoEnded
  have targetAfterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      hostedOccurrence.interface.boundaryWire
      (hostedOccurrence.context.fill targetAfter) :=
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
  have childStrict := transformation outer
    (hostLocals ++ locals) nextRename nextHostItems
    presentedOccurrence presentedTargetCanonical
    presentedTargetExternalTwoEnded
  let finalBodyIso := DiagramContext.fillIso
    presentedOccurrence.context targetPresentation.symm
  let finalIso : OpenDiagramIso
      (presentedOccurrence.interface.withBody
        (presentedOccurrence.context.fill targetAfter)
        presentedTargetCanonical presentedTargetExternalTwoEnded)
      (hostedOccurrence.interface.withBody
        (hostedOccurrence.context.fill targetBefore)
        targetCanonical targetExternalTwoEnded) :=
    OpenDiagram.withBody_iso presentedTargetCanonical targetCanonical
      presentedTargetExternalTwoEnded targetExternalTwoEnded finalBodyIso
  exact ⟨transGen_iso (OpenDiagramIso.refl source) childStrict.1
      finalIso,
    transGen_iso finalIso childStrict.2 (OpenDiagramIso.refl source)⟩

/-- Combine hosted strict transformations under region conjunction. -/
theorem HostedStrict.conjoin
    {common : List Sig}
    (firstBefore secondBefore firstAfter secondAfter : Region common)
    (firstTransformation : HostedStrict firstBefore firstAfter)
    (secondTransformation : HostedStrict secondBefore secondAfter) :
    HostedStrict (firstBefore.conjoin secondBefore)
      (firstAfter.conjoin secondAfter) := by
  intro outer hostLocals rename hostItems boundary source occurrence
    targetCanonical targetExternalTwoEnded
  let sourceMaterial :=
    (firstBefore.conjoin secondBefore).renameWires rename
  let targetMaterial :=
    (firstAfter.conjoin secondAfter).renameWires rename
  have supportedSequence : ∀
      (activeHostItems : ItemSeq (outer ++ hostLocals))
      {activeSource : OpenDiagram boundary}
      (activeOccurrence : Occurrence
        (Region.adjoinAt hostLocals activeHostItems sourceMaterial)
        activeSource)
      (_hostCanonical :
        (Region.mk hostLocals activeHostItems).Canonical)
      (_hostNonempty : ∀ {signature} (wire : Var outer signature),
        (Region.mk hostLocals activeHostItems).incidencePaths
          wire.index.val ≠ [])
      (activeTargetCanonical :
        (activeOccurrence.context.fill
          (Region.adjoinAt hostLocals activeHostItems
            targetMaterial)).Canonical)
      (activeTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
        activeOccurrence.interface.boundaryWire
        (activeOccurrence.context.fill
          (Region.adjoinAt hostLocals activeHostItems
            targetMaterial))),
      EqualityNormalization.StrictEquates activeOccurrence
        (Region.adjoinAt hostLocals activeHostItems targetMaterial)
        activeTargetCanonical activeTargetExternalTwoEnded := by
    intro activeHostItems activeSource activeOccurrence hostCanonical
      hostNonempty activeTargetCanonical activeTargetExternalTwoEnded
    let itemBefore := firstBefore.renameWires rename
    let tailBefore := secondBefore.renameWires rename
    let itemAfter := firstAfter.renameWires rename
    let tailAfter := secondAfter.renameWires rename
    change Occurrence
      (Region.adjoinAt hostLocals activeHostItems
        ((firstBefore.conjoin secondBefore).renameWires rename))
      activeSource at activeOccurrence
    have sourceBeforeCanonical :
        ((firstBefore.conjoin secondBefore).renameWires rename).Canonical :=
      Region.Canonical.material_of_adjoinAt hostLocals activeHostItems _
        (activeOccurrence.context.holeCanonical _
          activeOccurrence.sourceCanonical)
    have sourceMaterialCanonical :
        (itemBefore.conjoin tailBefore).Canonical := by
      rw [← Region.renameWires_conjoin]
      exact sourceBeforeCanonical
    let sourceOccurrence : Occurrence
        (Region.adjoinAt hostLocals activeHostItems
          (itemBefore.conjoin tailBefore)) activeSource :=
      EqualityNormalization.supportedAdjoinOccurrence hostLocals
        activeHostItems activeOccurrence hostCanonical hostNonempty
        sourceMaterialCanonical (by
          simpa only [itemBefore, tailBefore] using
            RegionIso.renameWiresConjoin firstBefore secondBefore rename)
    have itemBeforeCanonical :=
      EqualityNormalization.canonical_left_of_conjoin
        sourceMaterialCanonical
    have tailBeforeCanonical :=
      EqualityNormalization.canonical_right_of_conjoin
        sourceMaterialCanonical
    let targetBefore :=
      (firstAfter.conjoin secondAfter).renameWires rename
    change (activeOccurrence.context.fill
      (Region.adjoinAt hostLocals activeHostItems
        targetBefore)).Canonical at activeTargetCanonical
    change OpenDiagram.ExternalTwoEnded
      activeOccurrence.interface.boundaryWire
      (activeOccurrence.context.fill
        (Region.adjoinAt hostLocals activeHostItems targetBefore)) at activeTargetExternalTwoEnded
    have targetBeforeCanonical : targetBefore.Canonical :=
      Region.Canonical.material_of_adjoinAt hostLocals activeHostItems _
        (activeOccurrence.context.holeCanonical _
          activeTargetCanonical)
    have targetMaterialCanonical :
        (itemAfter.conjoin tailAfter).Canonical := by
      rw [← Region.renameWires_conjoin]
      exact targetBeforeCanonical
    have itemAfterCanonical :=
      EqualityNormalization.canonical_left_of_conjoin
        targetMaterialCanonical
    have tailAfterCanonical :=
      EqualityNormalization.canonical_right_of_conjoin
        targetMaterialCanonical
    have presentedTargetCanonical :
        (sourceOccurrence.context.fill
          (Region.adjoinAt hostLocals activeHostItems
            targetBefore)).Canonical := by
      exact activeTargetCanonical
    have presentedTargetExternalTwoEnded :
        OpenDiagram.ExternalTwoEnded
          sourceOccurrence.interface.boundaryWire
          (sourceOccurrence.context.fill
            (Region.adjoinAt hostLocals activeHostItems
              targetBefore)) := by
      intro signature wire
      exact activeTargetExternalTwoEnded wire
    have itemPhaseValidity :=
      EqualityNormalization.supportedAdjoinValidity hostLocals
        activeHostItems sourceOccurrence hostCanonical hostNonempty
        (EqualityNormalization.canonical_conjoin itemAfterCanonical
          tailBeforeCanonical)
    let afterItem := Region.adjoinAt hostLocals activeHostItems
      (itemAfter.conjoin tailBefore)
    have itemPhase : EqualityNormalization.StrictEquates
        sourceOccurrence afterItem itemPhaseValidity.1
          itemPhaseValidity.2 := by
      have swappedCanonical :
          (tailBefore.conjoin itemBefore).Canonical :=
        EqualityNormalization.canonical_conjoin tailBeforeCanonical
          itemBeforeCanonical
      let swapped :=
        EqualityNormalization.supportedAdjoinOccurrence hostLocals
          activeHostItems sourceOccurrence hostCanonical hostNonempty
          swappedCanonical
          (RegionIso.conjoinComm itemBefore tailBefore)
      let flattened := EqualityNormalization.flattenAdjoinOccurrence
        hostLocals activeHostItems tailBefore itemBefore swapped
        hostCanonical hostNonempty tailBeforeCanonical
        itemBeforeCanonical
      let nextHostItems := Region.extendHostItems hostLocals
        activeHostItems tailBefore
      let hostWire := Region.adjoinHostWire outer hostLocals
        tailBefore.locals
      let nextRename := WireRenaming.comp hostWire rename
      have nextHostCanonical :=
        EqualityNormalization.extendHostCanonical hostLocals
          activeHostItems tailBefore hostCanonical tailBeforeCanonical
      have nextHostNonempty : ∀ {signature}
          (wire : Var outer signature),
          (Region.mk (hostLocals ++ tailBefore.locals)
            nextHostItems).incidencePaths wire.index.val ≠ [] := by
        intro signature wire
        exact EqualityNormalization.extendHost_incidence_nonempty
          hostLocals activeHostItems tailBefore hostNonempty wire
      have firstBeforeCanonical : firstBefore.Canonical :=
        (Region.Canonical.renameWires_iff firstBefore rename).mp
          itemBeforeCanonical
      have alignedSourceCanonical :
          (firstBefore.renameWires nextRename).Canonical :=
        (Region.Canonical.renameWires_iff firstBefore nextRename).mpr
          firstBeforeCanonical
      let alignedFlattened : Occurrence
          (Region.adjoinAt (hostLocals ++ tailBefore.locals)
            nextHostItems (firstBefore.renameWires nextRename))
          activeSource :=
        EqualityNormalization.supportedAdjoinOccurrence
          (hostLocals ++ tailBefore.locals) nextHostItems flattened
          nextHostCanonical nextHostNonempty alignedSourceCanonical (by
            simpa only [itemBefore, hostWire, nextRename] using
              RegionIso.renameWiresComp firstBefore rename hostWire)
      have firstAfterCanonical : firstAfter.Canonical :=
        (Region.Canonical.renameWires_iff firstAfter rename).mp
          itemAfterCanonical
      let flatTargetMaterial := firstAfter.renameWires nextRename
      have flatTargetMaterialCanonical :
          flatTargetMaterial.Canonical :=
        (Region.Canonical.renameWires_iff firstAfter nextRename).mpr
          firstAfterCanonical
      have flatTargetValidity :=
        EqualityNormalization.supportedAdjoinValidity
          (hostLocals ++ tailBefore.locals) nextHostItems
          alignedFlattened nextHostCanonical nextHostNonempty
          flatTargetMaterialCanonical
      have core := firstTransformation outer
        (hostLocals ++ tailBefore.locals) nextRename nextHostItems
        alignedFlattened flatTargetValidity.1 flatTargetValidity.2
      let flatTarget := Region.adjoinAt
        (hostLocals ++ tailBefore.locals) nextHostItems
        flatTargetMaterial
      let flatEndpoint := alignedFlattened.interface.withBody
        (alignedFlattened.context.fill flatTarget)
        flatTargetValidity.1 flatTargetValidity.2
      have finalBodyIso : RegionIso (WireEquiv.refl outer) flatTarget
          afterItem := by
        exact (RegionIso.adjoinAt
          (hostLocals ++ tailBefore.locals) nextHostItems (by
            simpa only [flatTargetMaterial, itemAfter, nextRename,
              hostWire] using
              (RegionIso.renameWiresComp firstAfter rename
                hostWire).symm)).trans
          ((RegionIso.adjoinAtConjoinLeft hostLocals activeHostItems
            tailBefore itemAfter).symm.trans
            (RegionIso.adjoinAt hostLocals activeHostItems
              (RegionIso.conjoinComm tailBefore itemAfter)))
      have flatPresentedTargetCanonical :
          (alignedFlattened.context.fill afterItem).Canonical := by
        exact itemPhaseValidity.1
      have flatPresentedTargetExternalTwoEnded :
          OpenDiagram.ExternalTwoEnded
            alignedFlattened.interface.boundaryWire
            (alignedFlattened.context.fill afterItem) := by
        intro signature wire
        exact itemPhaseValidity.2 wire
      have finalIso : OpenDiagramIso flatEndpoint
          (alignedFlattened.interface.withBody
            (alignedFlattened.context.fill afterItem)
            flatPresentedTargetCanonical
            flatPresentedTargetExternalTwoEnded) :=
        OpenDiagram.withBody_iso flatTargetValidity.1
          flatPresentedTargetCanonical flatTargetValidity.2
          flatPresentedTargetExternalTwoEnded
          (DiagramContext.fillIso alignedFlattened.context
            finalBodyIso)
      have presented : EqualityNormalization.StrictEquates
          alignedFlattened afterItem flatPresentedTargetCanonical
            flatPresentedTargetExternalTwoEnded :=
        EqualityNormalization.StrictEquates.targetIso core finalIso
      have outputIso : OpenDiagramIso
          (alignedFlattened.interface.withBody
            (alignedFlattened.context.fill afterItem)
            flatPresentedTargetCanonical
            flatPresentedTargetExternalTwoEnded)
          (sourceOccurrence.interface.withBody
            (sourceOccurrence.context.fill afterItem)
            itemPhaseValidity.1 itemPhaseValidity.2) :=
        OpenDiagram.withBody_iso flatPresentedTargetCanonical
          itemPhaseValidity.1 flatPresentedTargetExternalTwoEnded
          itemPhaseValidity.2 (RegionIso.refl _)
      have exactPresented : EqualityNormalization.StrictEquates
          sourceOccurrence afterItem itemPhaseValidity.1
            itemPhaseValidity.2 :=
        ⟨transGen_iso (OpenDiagramIso.refl activeSource)
            presented.1 outputIso,
          transGen_iso outputIso presented.2
            (OpenDiagramIso.refl activeSource)⟩
      simpa only [itemBefore, itemAfter, swapped, flattened,
        alignedFlattened, nextHostItems, hostWire, nextRename,
        flatTargetMaterial, flatTarget, flatEndpoint] using
          exactPresented
    let afterItemOccurrence : Occurrence afterItem
        (sourceOccurrence.interface.withBody
          (sourceOccurrence.context.fill afterItem)
          itemPhaseValidity.1 itemPhaseValidity.2) :=
      exactOccurrence sourceOccurrence.interface sourceOccurrence.context
        afterItem itemPhaseValidity.1 itemPhaseValidity.2
    let flattened := EqualityNormalization.flattenAdjoinOccurrence
      hostLocals activeHostItems itemAfter tailBefore
      afterItemOccurrence hostCanonical hostNonempty itemAfterCanonical
      tailBeforeCanonical
    let nextHostItems := Region.extendHostItems hostLocals
      activeHostItems itemAfter
    let hostWire := Region.adjoinHostWire outer hostLocals
      itemAfter.locals
    let nextRename := WireRenaming.comp hostWire rename
    have nextHostCanonical :=
      EqualityNormalization.extendHostCanonical hostLocals
        activeHostItems itemAfter hostCanonical itemAfterCanonical
    have nextHostNonempty : ∀ {signature}
        (wire : Var outer signature),
        (Region.mk (hostLocals ++ itemAfter.locals)
          nextHostItems).incidencePaths wire.index.val ≠ [] := by
      intro signature wire
      exact EqualityNormalization.extendHost_incidence_nonempty
        hostLocals activeHostItems itemAfter hostNonempty wire
    have secondBeforeCanonical : secondBefore.Canonical :=
      (Region.Canonical.renameWires_iff secondBefore rename).mp
        tailBeforeCanonical
    have alignedTailCanonical :
        (secondBefore.renameWires nextRename).Canonical :=
      (Region.Canonical.renameWires_iff secondBefore nextRename).mpr
        secondBeforeCanonical
    let alignedFlattened : Occurrence
        (Region.adjoinAt (hostLocals ++ itemAfter.locals)
          nextHostItems (secondBefore.renameWires nextRename))
        (sourceOccurrence.interface.withBody
          (sourceOccurrence.context.fill afterItem)
          itemPhaseValidity.1 itemPhaseValidity.2) :=
      EqualityNormalization.supportedAdjoinOccurrence
        (hostLocals ++ itemAfter.locals) nextHostItems flattened
        nextHostCanonical nextHostNonempty alignedTailCanonical (by
          simpa only [tailBefore, hostWire, nextRename] using
            RegionIso.renameWiresComp secondBefore rename hostWire)
    have secondAfterCanonical : secondAfter.Canonical :=
      (Region.Canonical.renameWires_iff secondAfter rename).mp
        tailAfterCanonical
    let flatTargetMaterial := secondAfter.renameWires nextRename
    have flatTargetMaterialCanonical : flatTargetMaterial.Canonical :=
      (Region.Canonical.renameWires_iff secondAfter nextRename).mpr
        secondAfterCanonical
    have tailTargetValidity :=
      EqualityNormalization.supportedAdjoinValidity
        (hostLocals ++ itemAfter.locals) nextHostItems
        alignedFlattened nextHostCanonical nextHostNonempty
        flatTargetMaterialCanonical
    have tailPhase := secondTransformation outer
      (hostLocals ++ itemAfter.locals) nextRename nextHostItems
      alignedFlattened tailTargetValidity.1 tailTargetValidity.2
    let flatTarget := Region.adjoinAt
      (hostLocals ++ itemAfter.locals) nextHostItems
      flatTargetMaterial
    let flatTargetEndpoint := alignedFlattened.interface.withBody
      (alignedFlattened.context.fill flatTarget)
      tailTargetValidity.1 tailTargetValidity.2
    have finalBodyIso : RegionIso (WireEquiv.refl outer) flatTarget
        (Region.adjoinAt hostLocals activeHostItems targetBefore) := by
      exact (RegionIso.adjoinAt
        (hostLocals ++ itemAfter.locals) nextHostItems (by
          simpa only [flatTargetMaterial, tailAfter, nextRename,
            hostWire] using
            (RegionIso.renameWiresComp secondAfter rename
              hostWire).symm)).trans
        ((RegionIso.adjoinAtConjoinLeft hostLocals activeHostItems
          itemAfter tailAfter).symm.trans
          (RegionIso.adjoinAt hostLocals activeHostItems (by
            simpa only [itemAfter, tailAfter, targetBefore] using
              (RegionIso.renameWiresConjoin firstAfter secondAfter
                rename).symm)))
    have finalIso : OpenDiagramIso flatTargetEndpoint
        (sourceOccurrence.interface.withBody
          (sourceOccurrence.context.fill
            (Region.adjoinAt hostLocals activeHostItems targetBefore))
          presentedTargetCanonical
          presentedTargetExternalTwoEnded) :=
      OpenDiagram.withBody_iso tailTargetValidity.1
        presentedTargetCanonical tailTargetValidity.2
        presentedTargetExternalTwoEnded
        (DiagramContext.fillIso sourceOccurrence.context finalBodyIso)
    have tailPhase' : EqualityNormalization.StrictEquates
        alignedFlattened
        (Region.adjoinAt hostLocals activeHostItems targetBefore)
        presentedTargetCanonical presentedTargetExternalTwoEnded :=
      EqualityNormalization.StrictEquates.targetIso tailPhase finalIso
    have itemPhase' : EqualityNormalization.StrictEquates
        sourceOccurrence afterItem itemPhaseValidity.1
          itemPhaseValidity.2 := by
      simpa only [afterItem, itemBefore, tailBefore, itemAfter,
        sourceOccurrence] using itemPhase
    have combined := EqualityNormalization.StrictEquates.trans
      (targetExternalTwoEnded := presentedTargetExternalTwoEnded)
      itemPhase' tailPhase'
    have outputIso : OpenDiagramIso
        (sourceOccurrence.interface.withBody
          (sourceOccurrence.context.fill
            (Region.adjoinAt hostLocals activeHostItems targetBefore))
          presentedTargetCanonical presentedTargetExternalTwoEnded)
        (activeOccurrence.interface.withBody
          (activeOccurrence.context.fill
            (Region.adjoinAt hostLocals activeHostItems targetBefore))
          activeTargetCanonical activeTargetExternalTwoEnded) :=
      OpenDiagram.withBody_iso presentedTargetCanonical
        activeTargetCanonical presentedTargetExternalTwoEnded
        activeTargetExternalTwoEnded (RegionIso.refl _)
    have exactCombined : EqualityNormalization.StrictEquates
        activeOccurrence
        (Region.adjoinAt hostLocals activeHostItems targetBefore)
        activeTargetCanonical activeTargetExternalTwoEnded :=
      ⟨transGen_iso (OpenDiagramIso.refl activeSource) combined.1
          outputIso,
        transGen_iso outputIso combined.2
          (OpenDiagramIso.refl activeSource)⟩
    simpa only [sourceMaterial, targetMaterial, itemBefore,
      tailBefore, itemAfter, tailAfter, sourceOccurrence, afterItem,
      afterItemOccurrence, flattened, alignedFlattened, nextHostItems,
      hostWire, nextRename, flatTargetMaterial, flatTarget,
      flatTargetEndpoint, targetBefore] using exactCombined
  by_cases nonempty : outer ++ hostLocals ≠ []
  · obtain ⟨pinnedSourceCanonical, pinnedSourceExternalTwoEnded,
        sourcePins⟩ :=
      EqualityNormalization.adjoinPinsEquatesNonempty hostLocals
        hostItems sourceMaterial occurrence nonempty
    let pinnedItems := hostItems.append
      (EqualityNormalization.contextPins outer hostLocals)
    let pinnedSource := Region.adjoinAt hostLocals pinnedItems
      sourceMaterial
    let pinnedSourceOccurrence : Occurrence pinnedSource
        (occurrence.interface.withBody
          (occurrence.context.fill pinnedSource)
          pinnedSourceCanonical pinnedSourceExternalTwoEnded) :=
      exactOccurrence occurrence.interface occurrence.context
        pinnedSource pinnedSourceCanonical pinnedSourceExternalTwoEnded
    have sourceLocalCanonical :
        (Region.adjoinAt hostLocals hostItems
          sourceMaterial).Canonical :=
      occurrence.context.holeCanonical _ occurrence.sourceCanonical
    have pinnedHostCanonical :
        (Region.mk hostLocals pinnedItems).Canonical :=
      EqualityNormalization.pinnedHostCanonical hostLocals hostItems
        sourceMaterial sourceLocalCanonical
    have pinnedHostNonempty : ∀ {signature}
        (wire : Var outer signature),
        (Region.mk hostLocals pinnedItems).incidencePaths
          wire.index.val ≠ [] := by
      intro signature wire
      exact EqualityNormalization.pinnedHost_incidence_nonempty
        hostLocals hostItems wire
    have targetLocalCanonical :
        (Region.adjoinAt hostLocals hostItems
          targetMaterial).Canonical :=
      occurrence.context.holeCanonical _ targetCanonical
    have targetMaterialCanonical : targetMaterial.Canonical :=
      Region.Canonical.material_of_adjoinAt hostLocals hostItems _
        targetLocalCanonical
    have pinnedTargetValidity :=
      EqualityNormalization.supportedAdjoinValidity hostLocals
        pinnedItems pinnedSourceOccurrence pinnedHostCanonical
        pinnedHostNonempty targetMaterialCanonical
    have folded := supportedSequence pinnedItems pinnedSourceOccurrence
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
        targetPins⟩ :=
      EqualityNormalization.adjoinPinsEquatesNonempty hostLocals
        hostItems targetMaterial targetOccurrence nonempty
    have forwardPins : Relation.TransGen Step source
        (occurrence.interface.withBody
          (occurrence.context.fill pinnedSource)
          pinnedSourceCanonical pinnedSourceExternalTwoEnded) := by
      simpa only [sourceMaterial, pinnedSource, pinnedItems] using
        sourcePins.1
    have reversePins : Relation.TransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill pinnedSource)
          pinnedSourceCanonical pinnedSourceExternalTwoEnded) source := by
      simpa only [sourceMaterial, pinnedSource, pinnedItems] using
        sourcePins.2
    have middleForward : Relation.TransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill pinnedSource)
          pinnedSourceCanonical pinnedSourceExternalTwoEnded)
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals pinnedItems targetMaterial))
          pinnedTargetValidity.1 pinnedTargetValidity.2) := by
      simpa only [pinnedSourceOccurrence, exactOccurrence] using
        folded.1
    have middleReverse : Relation.TransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals pinnedItems targetMaterial))
          pinnedTargetValidity.1 pinnedTargetValidity.2)
        (occurrence.interface.withBody
          (occurrence.context.fill pinnedSource)
          pinnedSourceCanonical pinnedSourceExternalTwoEnded) := by
      simpa only [pinnedSourceOccurrence, exactOccurrence] using
        folded.2
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
      (unpinReverse.trans middleReverse).trans reversePins⟩
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
      have canonical := EqualityNormalization.pinnedHostCanonical
        ([] : List Sig) hostItems sourceMaterial sourceLocalCanonical
      simpa only [EqualityNormalization.contextPins,
        EqualityNormalization.allPins, List.nil_append,
        ItemSeq.pinWires, ItemSeq.nil_append,
        ItemSeq.append_nil] using canonical
    have hostNonempty : ∀ {signature} (wire : Var [] signature),
        (Region.mk [] hostItems).incidencePaths wire.index.val ≠ [] := by
      intro signature wire
      exact Fin.elim0 wire.index
    simpa only [sourceMaterial, targetMaterial] using
      supportedSequence hostItems occurrence hostCanonical hostNonempty
        targetCanonical targetExternalTwoEnded

/-- Lift a hosted strict transformation beneath one cut. -/
theorem HostedStrict.cut
    {common : List Sig} (before after : Region common)
    (transformation : HostedStrict before after) :
    HostedStrict (Region.singleton (.cut before))
      (Region.singleton (.cut after)) := by
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
    ((Region.singleton (.cut before)).renameWires rename)
  let sourceAfter := inner.fill
    (before.renameWires childRename)
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
    EqualityNormalization.presentationOccurrence occurrence
      sourceAfterCanonical sourceNonempty (by
        rw [← sourceEq]
        exact RegionIso.refl _)
  let childOccurrence := EqualityNormalization.Occurrence.nest
    outerOccurrence
  let targetBefore := Region.adjoinAt hostLocals hostItems
    ((Region.singleton (.cut after)).renameWires rename)
  let targetAfter := inner.fill
    (after.renameWires childRename)
  change (occurrence.context.fill targetBefore).Canonical at targetCanonical
  change OpenDiagram.ExternalTwoEnded
    occurrence.interface.boundaryWire
    (occurrence.context.fill targetBefore) at targetExternalTwoEnded
  have targetEq : targetBefore = targetAfter := by
    simp only [inner, retained, childRename, materialRename,
      appendNil, targetBefore, targetAfter, DiagramContext.fill,
      Region.renameWires, Region.singleton, Region.ofItems,
      Region.adjoinAt, ItemSeq.renameWires, Item.renameWires]
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
  have childTargetCanonical :
      (childOccurrence.context.fill
        (after.renameWires childRename)).Canonical := by
    simpa only [childOccurrence, EqualityNormalization.Occurrence.nest,
      DiagramContext.fill_comp, targetAfter] using
        targetReplacement.1
  have childTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      childOccurrence.interface.boundaryWire
      (childOccurrence.context.fill
        (after.renameWires childRename)) := by
    intro signature wire
    simpa only [childOccurrence, EqualityNormalization.Occurrence.nest,
      DiagramContext.fill_comp, targetAfter] using
        targetAfterExternalTwoEnded wire
  let childOuter := outer ++ (hostLocals ++ [])
  let childEmptyEquiv := WireEquiv.appendNil childOuter
  let childAppend : WireRenaming childOuter (childOuter ++ []) :=
    childEmptyEquiv.symm.toRenaming
  let hostedChildRename := WireRenaming.comp childAppend childRename
  let emptyHostIso (region : Region common) :
      RegionIso (WireEquiv.refl childOuter)
        (region.renameWires childRename)
        (Region.adjoinAt [] .nil
          (region.renameWires hostedChildRename)) := by
    let directToCollapsed := RegionIso.renameWires region childRename
      (WireRenaming.comp childEmptyEquiv.toRenaming
        hostedChildRename)
      (WireEquiv.refl childOuter) (by
        intro signature wire
        exact (childEmptyEquiv.right_inv (childRename wire)).symm)
    let collapsedFromHosted :=
      (RegionIso.renameWiresComp region hostedChildRename
        childEmptyEquiv.toRenaming).symm
    exact (directToCollapsed.trans collapsedFromHosted).trans
      (RegionIso.adjoinAtNil
        (region.renameWires hostedChildRename))
  let sourceHosted := Region.adjoinAt [] .nil
    (before.renameWires hostedChildRename)
  let sourcePresentation : RegionIso (WireEquiv.refl childOuter)
      (before.renameWires childRename) sourceHosted :=
    emptyHostIso before
  have sourceHostedCanonical : sourceHosted.Canonical :=
    sourcePresentation.canonical_iff.mp
      (childOccurrence.context.holeCanonical _
        childOccurrence.sourceCanonical)
  have sourceHostedNonempty : ∀ {signature}
      (wire : Var childOuter signature),
      (before.renameWires childRename).incidencePaths
          wire.index.val ≠ [] ↔
        sourceHosted.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    have lengthEq := sourcePresentation.incidencePaths_length_eq wire
    exact ⟨fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [← lengthEq], fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [lengthEq]⟩
  let presentedChildOccurrence : Occurrence sourceHosted source :=
    EqualityNormalization.presentationOccurrence childOccurrence
      sourceHostedCanonical sourceHostedNonempty sourcePresentation
  let targetHosted := Region.adjoinAt [] .nil
    (after.renameWires hostedChildRename)
  let targetPresentation : RegionIso (WireEquiv.refl childOuter)
      (after.renameWires childRename) targetHosted :=
    emptyHostIso after
  have targetHostedCanonical : targetHosted.Canonical :=
    targetPresentation.canonical_iff.mp
      (childOccurrence.context.holeCanonical _ childTargetCanonical)
  have targetHostedNonempty : ∀ {signature}
      (wire : Var childOuter signature),
      (after.renameWires childRename).incidencePaths
          wire.index.val ≠ [] ↔
        targetHosted.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    have lengthEq := targetPresentation.incidencePaths_length_eq wire
    exact ⟨fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [← lengthEq], fun nonempty => by
      rw [← List.length_pos_iff] at nonempty ⊢
      rwa [lengthEq]⟩
  have targetHostedReplacement :=
    childOccurrence.context.replaceCanonical
      (after.renameWires childRename) targetHosted
      childTargetCanonical targetHostedCanonical targetHostedNonempty
  let childTargetEndpoint := childOccurrence.interface.withBody
    (childOccurrence.context.fill
      (after.renameWires childRename))
    childTargetCanonical childTargetExternalTwoEnded
  have targetHostedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      childOccurrence.interface.boundaryWire
      (childOccurrence.context.fill targetHosted) :=
    childTargetEndpoint.externalTwoEnded_of_nonempty_iff _
      targetHostedReplacement.2
  have presentedTargetCanonical :
      (presentedChildOccurrence.context.fill targetHosted).Canonical := by
    exact targetHostedReplacement.1
  have presentedTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      presentedChildOccurrence.interface.boundaryWire
      (presentedChildOccurrence.context.fill targetHosted) := by
    intro signature wire
    exact targetHostedExternalTwoEnded wire
  have childStrict := transformation childOuter [] hostedChildRename .nil
    presentedChildOccurrence presentedTargetCanonical
      presentedTargetExternalTwoEnded
  let hostedToDirect : OpenDiagramIso
      (presentedChildOccurrence.interface.withBody
        (presentedChildOccurrence.context.fill targetHosted)
        presentedTargetCanonical presentedTargetExternalTwoEnded)
      (childOccurrence.interface.withBody
        (childOccurrence.context.fill
          (after.renameWires childRename))
        childTargetCanonical childTargetExternalTwoEnded) :=
    OpenDiagram.withBody_iso presentedTargetCanonical
      childTargetCanonical presentedTargetExternalTwoEnded
      childTargetExternalTwoEnded
      (DiagramContext.fillIso childOccurrence.context
        targetPresentation.symm)
  have finalBodyIso : RegionIso (WireEquiv.refl outer) targetAfter
      targetBefore := by
    rw [← targetEq]
    exact RegionIso.refl _
  have outerFinalIso : OpenDiagramIso
      (outerOccurrence.interface.withBody
        (outerOccurrence.context.fill targetAfter)
        targetReplacement.1 targetAfterExternalTwoEnded)
      (occurrence.interface.withBody
        (occurrence.context.fill targetBefore) targetCanonical
          targetExternalTwoEnded) :=
    OpenDiagram.withBody_iso targetReplacement.1 targetCanonical
      targetAfterExternalTwoEnded targetExternalTwoEnded
      (DiagramContext.fillIso occurrence.context finalBodyIso)
  have directToOuter : OpenDiagramIso
      (childOccurrence.interface.withBody
        (childOccurrence.context.fill
          (after.renameWires childRename))
        childTargetCanonical childTargetExternalTwoEnded)
      (occurrence.interface.withBody
        (occurrence.context.fill targetBefore) targetCanonical
          targetExternalTwoEnded) := by
    simpa only [childOccurrence, EqualityNormalization.Occurrence.nest,
      DiagramContext.fill_comp, targetAfter] using outerFinalIso
  let finalIso := hostedToDirect.trans directToOuter
  exact ⟨transGen_iso (OpenDiagramIso.refl source) childStrict.1
      finalIso,
    transGen_iso finalIso childStrict.2
      (OpenDiagramIso.refl source)⟩



/-- Move the support completion of a singleton cut from outside the cut to
the child body. The equivalence is stable under every enclosing host and wire
substitution used by the structural accumulator. -/
theorem supportCutHosted
    (body : Region materialWires) (bodyCanonical : body.Canonical) :
    HostedStrict
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        (Erasure.Exposure.supportPattern
          (Region.singleton (.cut body))
          ((Region.singleton_cut_canonical_iff body).mpr bodyCanonical))
        (EqualityNormalization.formalPorts materialWires))
      (Region.singleton (.cut
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (Erasure.Exposure.supportPattern body bodyCanonical)
          (EqualityNormalization.formalPorts materialWires)))) := by
  intro outer hostLocals rename hostItems boundary source occurrence
    targetCanonical targetExternalTwoEnded
  apply EqualityNormalization.withPinnedEnvelope occurrence targetCanonical
    targetExternalTwoEnded
  intro pinnedSourceCanonical pinnedSourceExternalTwoEnded
  let outerMaterial := Region.singleton (.cut body)
  let outerCanonical : outerMaterial.Canonical :=
    (Region.singleton_cut_canonical_iff body).mpr bodyCanonical
  let outerPattern := Erasure.Exposure.supportPattern outerMaterial
    outerCanonical
  let childPattern := Erasure.Exposure.supportPattern body bodyCanonical
  let before :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      outerPattern (EqualityNormalization.formalPorts materialWires)
  let after := Region.singleton (.cut
    (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      childPattern (EqualityNormalization.formalPorts materialWires)))
  let pinnedItems := hostItems.append
    (EqualityNormalization.contextPins outer hostLocals)
  let pinnedOccurrence := exactOccurrence
    occurrence.interface occurrence.context
    (Region.adjoinAt hostLocals pinnedItems (before.renameWires rename))
    pinnedSourceCanonical pinnedSourceExternalTwoEnded
  have sourceLocalCanonical :
      (Region.adjoinAt hostLocals hostItems
        (before.renameWires rename)).Canonical := by
    simpa only [before, outerPattern, outerCanonical, outerMaterial] using
      occurrence.context.holeCanonical _ occurrence.sourceCanonical
  have pinnedHostCanonical :
      (Region.mk hostLocals pinnedItems).Canonical := by
    simpa only [pinnedItems] using
      EqualityNormalization.pinnedHostCanonical hostLocals hostItems
        (before.renameWires rename) sourceLocalCanonical
  have pinnedHostNonempty : ∀ {signature} (wire : Var outer signature),
      (Region.mk hostLocals pinnedItems).incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    simpa only [pinnedItems] using
      EqualityNormalization.pinnedHost_incidence_nonempty hostLocals
        hostItems wire
  have mappedBodyCanonical : (body.renameWires rename).Canonical :=
    (Region.Canonical.renameWires_iff body rename).mpr bodyCanonical
  let directMaterial := Region.singleton (.cut (body.renameWires rename))
  have directMaterialCanonical : directMaterial.Canonical := by
    exact (Region.singleton_cut_canonical_iff _).mpr mappedBodyCanonical
  obtain ⟨directCanonical, directExternalTwoEnded⟩ :=
    EqualityNormalization.supportedAdjoinValidity hostLocals pinnedItems
      pinnedOccurrence pinnedHostCanonical pinnedHostNonempty
      directMaterialCanonical
  let direct := Region.adjoinAt hostLocals pinnedItems directMaterial
  let directOccurrence := exactOccurrence
    occurrence.interface occurrence.context direct directCanonical
      directExternalTwoEnded
  let outerDescription : Rule.Erasure.Description outer := {
    materialWires := materialWires
    hostLocals := hostLocals
    hostItems := pinnedItems
    material := outerMaterial
    wireMap := rename
  }
  have outerSourceEq : outerDescription.source = direct := by
    simp [outerDescription, Rule.Erasure.Description.source,
      Region.spliceAt, direct, directMaterial, outerMaterial,
      Region.singleton_renameWires, Item.renameWires]
  have outerTargetEq : outerDescription.target =
      Region.mk hostLocals pinnedItems := by
    rfl
  have outerExposedEq : ∀ materialCanonical :
      outerDescription.material.Canonical,
      Erasure.Exposure.exposedRegion outerDescription materialCanonical =
        Region.adjoinAt hostLocals pinnedItems
          (before.renameWires rename) := by
    intro materialCanonical
    simp only [Erasure.Exposure.exposedRegion, outerDescription,
      Erasure.Exposure.applicationPorts]
    change Region.adjoinAt hostLocals pinnedItems
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (Erasure.Exposure.supportPattern outerMaterial materialCanonical)
          ((Erasure.Exposure.identityBoundary materialWires).map
            (fun wire => rename wire))) = _
    have canonicalEq : materialCanonical = outerCanonical :=
      Subsingleton.elim _ _
    subst materialCanonical
    simpa only [before, outerPattern, EqualityNormalization.formalPorts,
      EqualityNormalization.instantiate_renameWires]
  obtain ⟨outerExposedCanonical, outerExposedExternalTwoEnded,
      outerEquates⟩ := EqualityNormalization.pinnedExposureCore
    directOccurrence outerDescription outerSourceEq outerTargetEq
      outerExposedEq
  let innerContext : DiagramContext outer (outer ++ hostLocals) :=
    .cut hostLocals pinnedItems .nil .hole
  let innerDirect := innerContext.fill (body.renameWires rename)
  let directPresentation : RegionIso (WireEquiv.refl outer)
      direct innerDirect := by
    simpa only [direct, directMaterial, innerDirect, innerContext,
      DiagramContext.fill, ItemSeq.append_nil] using
      RegionIso.adjoinAtSingleton hostLocals pinnedItems
        (.cut (body.renameWires rename))
  let fullDirectPresentation :=
    occurrence.context.fillIso directPresentation
  have innerDirectCanonical :
      (occurrence.context.fill innerDirect).Canonical :=
    fullDirectPresentation.canonical_iff.mp directCanonical
  have innerDirectExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
        (occurrence.context.fill innerDirect) := by
    intro signature wire
    rw [← fullDirectPresentation.incidencePaths_length_eq wire]
    exact directExternalTwoEnded wire
  let nestedContext := occurrence.context.comp innerContext
  let directEndpoint := occurrence.interface.withBody
    (occurrence.context.fill direct) directCanonical directExternalTwoEnded
  let childOccurrence : Occurrence (body.renameWires rename)
      directEndpoint := {
    interface := occurrence.interface
    context := nestedContext
    sourceCanonical := by
      simpa only [nestedContext, DiagramContext.fill_comp, innerDirect,
        directEndpoint] using innerDirectCanonical
    sourceExternalTwoEnded := by
      intro signature wire
      simpa only [nestedContext, DiagramContext.fill_comp, innerDirect,
        directEndpoint] using innerDirectExternalTwoEnded wire
    host_iso := by
      simpa only [nestedContext, DiagramContext.fill_comp, innerDirect,
        directEndpoint] using
        OpenDiagram.withBody_iso directCanonical innerDirectCanonical
          directExternalTwoEnded innerDirectExternalTwoEnded
          fullDirectPresentation
  }
  let childWireMap : WireRenaming materialWires
      ((outer ++ hostLocals) ++ []) :=
    WireRenaming.comp
      (WireEquiv.appendNil (outer ++ hostLocals)).symm.toRenaming rename
  have spliceNilRename (material : Region materialWires) :
      Region.spliceAt [] .nil material childWireMap =
        material.renameWires rename := by
    cases material with
    | mk locals items =>
        simp only [Region.spliceAt, Region.adjoinAt, Region.renameWires,
          ItemSeq.renameWires, ItemSeq.nil_append]
        rw [ItemSeq.renameWires_comp]
        have mapEq : WireRenaming.comp
            (Region.adjoinMaterialWire (outer ++ hostLocals) [] locals)
            (childWireMap.appendRight locals) =
              rename.appendRight locals := by
          apply WireRenaming.ext
          intro signature wire
          apply Var.appendCases (left := materialWires) (right := locals)
            (motive := fun wire =>
              WireRenaming.comp
                (Region.adjoinMaterialWire (outer ++ hostLocals) [] locals)
                (childWireMap.appendRight locals) wire =
                  rename.appendRight locals wire)
            (fun inherited => by
              simp [childWireMap, WireRenaming.appendRight,
                WireRenaming.comp, Region.adjoinMaterialWire])
            (fun localWire => by
              simp only [childWireMap, WireRenaming.appendRight,
                WireRenaming.comp, Region.adjoinMaterialWire,
                Var.appendMap_right]
              change Var.appendRight (outer ++ hostLocals)
                  (Var.appendRight [] localWire) =
                Var.appendRight (outer ++ hostLocals) localWire
              rfl) wire
        rw [mapEq]
        simp only [List.nil_append]
  let childDescription : Rule.Erasure.Description (outer ++ hostLocals) := {
    materialWires := materialWires
    hostLocals := []
    hostItems := .nil
    material := body
    wireMap := childWireMap
  }
  have childSourceEq : childDescription.source = body.renameWires rename := by
    simpa only [childDescription, Rule.Erasure.Description.source] using
      spliceNilRename body
  let erasedChildMaterial :=
    Region.singleton (.cut (Region.blank (outer ++ hostLocals)))
  have erasedChildMaterialCanonical : erasedChildMaterial.Canonical := by
    apply (Region.singleton_cut_canonical_iff _).mpr
    exact ⟨fun localIndex => Fin.elim0 localIndex, True.intro⟩
  obtain ⟨erasedChildCanonical, erasedChildExternalTwoEnded⟩ :=
    EqualityNormalization.supportedAdjoinValidity hostLocals pinnedItems
      pinnedOccurrence pinnedHostCanonical pinnedHostNonempty
      erasedChildMaterialCanonical
  let erasedChild := Region.adjoinAt hostLocals pinnedItems erasedChildMaterial
  let innerErased := innerContext.fill childDescription.target
  let erasedPresentation : RegionIso (WireEquiv.refl outer)
      erasedChild innerErased := by
    simpa only [erasedChild, erasedChildMaterial, innerErased, innerContext,
      childDescription, Rule.Erasure.Description.target,
      DiagramContext.fill, ItemSeq.append_nil] using
      RegionIso.adjoinAtSingleton hostLocals pinnedItems
        (.cut (Region.blank (outer ++ hostLocals)))
  let fullErasedPresentation :=
    occurrence.context.fillIso erasedPresentation
  have erasedChildCanonical' :
      (childOccurrence.context.fill childDescription.target).Canonical := by
    have presented := fullErasedPresentation.canonical_iff.mp
      erasedChildCanonical
    simpa only [childOccurrence, nestedContext, DiagramContext.fill_comp,
      innerErased] using presented
  have erasedChildExternalTwoEnded' : OpenDiagram.ExternalTwoEnded
      childOccurrence.interface.boundaryWire
      (childOccurrence.context.fill childDescription.target) := by
    have presented : OpenDiagram.ExternalTwoEnded
        occurrence.interface.boundaryWire
        (occurrence.context.fill innerErased) := by
      intro signature wire
      rw [← fullErasedPresentation.incidencePaths_length_eq wire]
      exact erasedChildExternalTwoEnded wire
    intro signature wire
    simpa only [childOccurrence, nestedContext, DiagramContext.fill_comp,
      innerErased] using presented wire
  let childAfter :=
    (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      childPattern (EqualityNormalization.formalPorts materialWires)).renameWires
        rename
  let childExposed :=
    Erasure.Exposure.exposedRegion childDescription bodyCanonical
  have childExposedEq : ∀ materialCanonical :
      childDescription.material.Canonical,
      Erasure.Exposure.exposedRegion childDescription materialCanonical =
        childExposed := by
    intro materialCanonical
    have canonicalEq : materialCanonical = bodyCanonical := Subsingleton.elim _ _
    subst materialCanonical
    rfl
  obtain ⟨childExposedCanonical, childExposedExternalTwoEnded,
      childEquates⟩ := EqualityNormalization.exposureCore childOccurrence
    childDescription childSourceEq erasedChildCanonical'
      erasedChildExternalTwoEnded' childExposedEq
  let rawChildExposed :=
    _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
      childPattern
      ((Erasure.Exposure.identityBoundary materialWires).map
        (fun wire => childWireMap wire))
  let collapse := WireEquiv.appendNil (outer ++ hostLocals)
  have rawChildExposedEq : rawChildExposed.renameWires collapse.toRenaming =
      childAfter := by
    rw [EqualityNormalization.instantiate_renameWires]
    simp only [childAfter]
    rw [EqualityNormalization.instantiate_renameWires]
    simp only [rawChildExposed, childPattern,
      EqualityNormalization.formalPorts, collapse, Vars.map_map]
    congr 1
    apply Vars.map_congr
    intro signature wire
    exact collapse.right_inv (rename wire)
  let childExposedPresentation : RegionIso
      (WireEquiv.refl (outer ++ hostLocals)) childExposed childAfter := by
    let adjoining := RegionIso.adjoinAtNil rawChildExposed
    simpa only [childExposed, Erasure.Exposure.exposedRegion,
      childDescription, Erasure.Exposure.applicationPorts,
      rawChildExposed, collapse] using
      adjoining.symm.trans (RegionIso.ofEq rawChildExposedEq)
  let pinnedAfter := Region.adjoinAt hostLocals pinnedItems
    (after.renameWires rename)
  let innerAfter := innerContext.fill childAfter
  let afterPresentation : RegionIso (WireEquiv.refl outer)
      pinnedAfter innerAfter := by
    simpa only [pinnedAfter, after, Region.singleton_renameWires,
      Item.renameWires, childAfter, innerAfter, innerContext,
      DiagramContext.fill, ItemSeq.append_nil] using
      RegionIso.adjoinAtSingleton hostLocals pinnedItems (.cut childAfter)
  let fullAfterPresentation :=
    occurrence.context.fillIso afterPresentation
  let fullChildPresentation :=
    nestedContext.fillIso childExposedPresentation
  let targetPresentation : RegionIso
      (WireEquiv.refl occurrence.interface.external)
      (occurrence.context.fill pinnedAfter)
      (nestedContext.fill childExposed) := by
    let alignedAfter : RegionIso
        (WireEquiv.refl occurrence.interface.external)
        (occurrence.context.fill pinnedAfter)
        (nestedContext.fill childAfter) := by
      simpa only [nestedContext, DiagramContext.fill_comp, innerAfter] using
        fullAfterPresentation
    exact alignedAfter.trans fullChildPresentation.symm
  have pinnedTargetCanonical :
      (occurrence.context.fill pinnedAfter).Canonical := by
    apply targetPresentation.canonical_iff.mpr
    simpa only [childOccurrence] using childExposedCanonical
  have pinnedTargetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      occurrence.interface.boundaryWire
      (occurrence.context.fill pinnedAfter) := by
    intro signature wire
    rw [targetPresentation.incidencePaths_length_eq wire]
    simpa only [childOccurrence] using childExposedExternalTwoEnded wire
  let pinnedTargetEndpoint := occurrence.interface.withBody
    (occurrence.context.fill pinnedAfter) pinnedTargetCanonical
      pinnedTargetExternalTwoEnded
  let childTargetEndpoint := occurrence.interface.withBody
    (nestedContext.fill childExposed) childExposedCanonical
      childExposedExternalTwoEnded
  let afterIso : OpenDiagramIso pinnedTargetEndpoint childTargetEndpoint :=
    OpenDiagram.withBody_iso pinnedTargetCanonical childExposedCanonical
      pinnedTargetExternalTwoEnded childExposedExternalTwoEnded
      targetPresentation
  refine ⟨pinnedTargetCanonical, pinnedTargetExternalTwoEnded, ?_⟩
  constructor
  · have first : Relation.ReflTransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals pinnedItems (before.renameWires rename)))
          pinnedSourceCanonical pinnedSourceExternalTwoEnded)
        directEndpoint := by
      simpa only [pinnedOccurrence, exactOccurrence, directOccurrence,
        directEndpoint, before, outerPattern, outerCanonical, outerMaterial]
        using outerEquates.2
    have second : Relation.ReflTransGen Step directEndpoint
        (occurrence.interface.withBody
          (occurrence.context.fill pinnedAfter) pinnedTargetCanonical
            pinnedTargetExternalTwoEnded) := by
      have raw : Relation.ReflTransGen Step directEndpoint
          childTargetEndpoint := by
        simpa only [childOccurrence, directEndpoint, childTargetEndpoint,
          nestedContext] using
          childEquates.1
      simpa only [pinnedTargetEndpoint] using
        EqualityNormalization.reflTransGen_iso (OpenDiagramIso.refl _)
          raw afterIso.symm
    exact first.trans second
  · have first : Relation.ReflTransGen Step
        (occurrence.interface.withBody
          (occurrence.context.fill pinnedAfter) pinnedTargetCanonical
            pinnedTargetExternalTwoEnded) directEndpoint := by
      have raw : Relation.ReflTransGen Step childTargetEndpoint
          directEndpoint := by
        simpa only [childOccurrence, directEndpoint, childTargetEndpoint,
          nestedContext] using
          childEquates.2
      simpa only [pinnedTargetEndpoint] using
        EqualityNormalization.reflTransGen_iso afterIso.symm raw
          (OpenDiagramIso.refl _)
    have second : Relation.ReflTransGen Step directEndpoint
        (occurrence.interface.withBody
          (occurrence.context.fill
            (Region.adjoinAt hostLocals pinnedItems (before.renameWires rename)))
          pinnedSourceCanonical pinnedSourceExternalTwoEnded) := by
      simpa only [pinnedOccurrence, exactOccurrence, directOccurrence,
        directEndpoint, before, outerPattern, outerCanonical, outerMaterial]
        using outerEquates.1
    exact first.trans second

/-- The support-cut bridge at an arbitrary selected application. -/
theorem supportCutInstantiatedHosted
    (body : Region materialWires) (bodyCanonical : body.Canonical)
    (application : Vars wires materialWires) :
    HostedStrict
      (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
        (Erasure.Exposure.supportPattern
          (Region.singleton (.cut body))
          ((Region.singleton_cut_canonical_iff body).mpr bodyCanonical))
        application)
      (Region.singleton (.cut
        (_root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          (Erasure.Exposure.supportPattern body bodyCanonical)
          application))) := by
  let baseRename := EqualityNormalization.formalSubstitution application
  apply HostedStrict.specialize (supportCutHosted body bodyCanonical)
    baseRename
  · simpa only [baseRename,
      EqualityNormalization.instantiate_renameWires,
      EqualityNormalization.formalPorts_map_substitution]
  · simp only [Region.singleton_renameWires, Item.renameWires]
    congr 2
    simpa only [baseRename,
      EqualityNormalization.instantiate_renameWires,
      EqualityNormalization.formalPorts_map_substitution]


end VisualProof.Rule.Completeness.Comprehension
