import VisualProof.Rule.Completeness.Erasure.Duplication
import VisualProof.Rule.Completeness.Erasure.TwoSite
import VisualProof.Rule.Completeness.Comprehension.Normalization.Support
import VisualProof.Rule.Step

namespace VisualProof.Rule.UncappedErasure

open Diagram

/-- Every declarative erasure step is derivable by a nonempty chain of
primitive HOL-calculus steps. -/
theorem complete
    {boundary : List Theory.Sig}
    {source target : OpenDiagram boundary}
    (step : UncappedErasure source target) :
    Relation.TransGen Step source target := by
  rcases step with ⟨outer, before, after, occurrence, targetCanonical,
    targetExternalTwoEnded, targetIso, localEvidence⟩
  cases polarityEq : occurrence.context.polarity with
  | positive =>
      have localStep : UncappedErasure.Local before after := by
        simpa only [atPolarity, polarityEq] using localEvidence
      cases localStep with
      | erase description =>
          obtain ⟨materialCanonical, exposedCanonical,
              exposedExternalTwoEnded, exposedEquates⟩ :=
            Completeness.Erasure.Exposure.equates description occurrence
              targetCanonical targetExternalTwoEnded
          let exposedOccurrence : Occurrence
              (Completeness.Erasure.Exposure.exposedRegion description
                materialCanonical)
              (occurrence.interface.withBody
                (occurrence.context.fill
                  (Completeness.Erasure.Exposure.exposedRegion description
                    materialCanonical))
                exposedCanonical exposedExternalTwoEnded) :=
            Completeness.exactOccurrence occurrence.interface
              occurrence.context
              (Completeness.Erasure.Exposure.exposedRegion description
                materialCanonical)
              exposedCanonical exposedExternalTwoEnded
          have specializedValidity :=
            Completeness.Erasure.TwoSite.specializedFilledValidity description
              materialCanonical occurrence targetCanonical
              targetExternalTwoEnded
          have specializedCanonical : (occurrence.context.fill
              (Completeness.Erasure.TwoSite.specialized description
                materialCanonical)).Canonical := specializedValidity.1
          have specializedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
              occurrence.interface.boundaryWire
              (occurrence.context.fill
                (Completeness.Erasure.TwoSite.specialized description
                  materialCanonical)) := specializedValidity.2
          let specializedEndpoint := occurrence.interface.withBody
            (occurrence.context.fill
              (Completeness.Erasure.TwoSite.specialized description
                materialCanonical))
            specializedCanonical specializedExternalTwoEnded
          let nested :=
            Completeness.Erasure.Duplication.exposedNestedOccurrence
              description materialCanonical exposedOccurrence
          let duplicationPresentation : RegionIso
              (WireEquiv.refl occurrence.interface.external)
              (nested.targetBody
                ((nested.selected.renameWires
                    nested.descendant.outerWire).conjoin nested.before))
              (occurrence.context.fill
                (Completeness.Erasure.TwoSite.specialized description
                  materialCanonical)) := by
            rw [show nested.targetBody
                ((nested.selected.renameWires
                    nested.descendant.outerWire).conjoin nested.before) =
                  occurrence.context.fill
                    (Completeness.Erasure.TwoSite.targetPresentation description
                      materialCanonical) by
              simp only [nested, exposedOccurrence,
                Completeness.exactOccurrence,
                Completeness.Erasure.Duplication.exposedNestedOccurrence,
                NestedOccurrence.targetBody, nestedBody,
                DiagramContext.fill, DiagramContext.outerWire,
                Completeness.Erasure.TwoSite.targetPresentation,
                Completeness.Erasure.TwoSite.baseInstance,
                Completeness.Erasure.TwoSite.pattern]
              rw [Region.renameWires_id]]
            exact occurrence.context.fillIso
              (Completeness.Erasure.TwoSite.specializedTargetIso
                description materialCanonical).symm
          have duplication : Iteration
              (occurrence.interface.withBody
                (occurrence.context.fill
                  (Completeness.Erasure.Exposure.exposedRegion description
                    materialCanonical))
                exposedCanonical exposedExternalTwoEnded)
              specializedEndpoint := by
            exact Completeness.Erasure.Duplication.exposedCopyStep description
              materialCanonical exposedOccurrence
              (occurrence.context.fill
                (Completeness.Erasure.TwoSite.specialized description
                  materialCanonical))
              duplicationPresentation specializedCanonical
              specializedExternalTwoEnded
          have quantifiedValidity :=
            Completeness.Erasure.TwoSite.quantifiedFilledValidity description
              occurrence targetCanonical targetExternalTwoEnded
          have quantifiedCanonical : (occurrence.context.fill
              (Completeness.Erasure.TwoSite.quantified description)).Canonical :=
            quantifiedValidity.1
          have quantifiedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
              occurrence.interface.boundaryWire
              (occurrence.context.fill
                (Completeness.Erasure.TwoSite.quantified description)) :=
            quantifiedValidity.2
          let quantifiedEndpoint := occurrence.interface.withBody
            (occurrence.context.fill
              (Completeness.Erasure.TwoSite.quantified description))
            quantifiedCanonical quantifiedExternalTwoEnded
          let comprehensionOccurrence : Occurrence
              (Completeness.Erasure.TwoSite.specialized description
                materialCanonical) specializedEndpoint :=
            Completeness.exactOccurrence occurrence.interface
              occurrence.context
              (Completeness.Erasure.TwoSite.specialized description
                materialCanonical)
              specializedCanonical specializedExternalTwoEnded
          let continuation :=
            Completeness.Comprehension.Telescope.refl .positive
              occurrence.interface occurrence.context
              quantifiedCanonical quantifiedExternalTwoEnded polarityEq
          let request : Completeness.Comprehension.Telescope.Request
              (Completeness.Erasure.TwoSite.specialized description
                materialCanonical)
              (Completeness.Erasure.TwoSite.quantified description) := {
            boundary := boundary
            source := specializedEndpoint
            endpoint := Completeness.Erasure.TwoSite.quantified description
            polarity := .positive
            occurrence := comprehensionOccurrence
            instantiatedCanonical := specializedCanonical
            instantiatedExternalTwoEnded := specializedExternalTwoEnded
            pendingCanonical := quantifiedCanonical
            pendingExternalTwoEnded := quantifiedExternalTwoEnded
            endpointCanonical := quantifiedCanonical
            endpointExternalTwoEnded := quantifiedExternalTwoEnded
            continuation := continuation
          }
          have comprehension : Relation.TransGen Step specializedEndpoint
              quantifiedEndpoint := by
            simpa only [request,
              Completeness.Comprehension.Telescope.Request.Result,
              Completeness.Comprehension.Telescope.StrictDerives,
              Completeness.Comprehension.polarityTarget,
              quantifiedEndpoint] using
              Completeness.Comprehension.complete
                (Completeness.Erasure.TwoSite.pattern description
                  materialCanonical)
                (Completeness.Erasure.TwoSite.instantiates description
                  materialCanonical)
                request
          have absorbedValidity :=
            Completeness.Erasure.TwoSite.absorbedFilledValidity description
              materialCanonical occurrence targetCanonical
              targetExternalTwoEnded
          have absorbedCanonical : (occurrence.context.fill
              (Completeness.Erasure.TwoSite.absorbed description
                materialCanonical)).Canonical := absorbedValidity.1
          have absorbedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
              occurrence.interface.boundaryWire
              (occurrence.context.fill
                (Completeness.Erasure.TwoSite.absorbed description
                  materialCanonical)) := absorbedValidity.2
          let absorbedEndpoint := occurrence.interface.withBody
            (occurrence.context.fill
              (Completeness.Erasure.TwoSite.absorbed description
                materialCanonical))
            absorbedCanonical absorbedExternalTwoEnded
          let quantifiedOccurrence : Occurrence
              (Completeness.Erasure.TwoSite.quantified description)
              quantifiedEndpoint :=
            Completeness.exactOccurrence occurrence.interface
              occurrence.context
              (Completeness.Erasure.TwoSite.quantified description)
              quantifiedCanonical quantifiedExternalTwoEnded
          have ends : WirePrimitive.Ends quantifiedEndpoint absorbedEndpoint := by
            exact ⟨outer,
              Completeness.Erasure.TwoSite.quantified description,
              Completeness.Erasure.TwoSite.absorbed description
                materialCanonical,
              quantifiedOccurrence, absorbedCanonical,
              absorbedExternalTwoEnded, OpenDiagramIso.refl _, by
                simpa only [quantifiedOccurrence,
                  Completeness.exactOccurrence, polarityEq, atPolarity] using
                  (WirePrimitive.Content.Ends.Local.absorb
                    (Completeness.Erasure.TwoSite.absorbEvidence description
                      materialCanonical))⟩
          have mandatory : Relation.TransGen Step
              (occurrence.interface.withBody
                (occurrence.context.fill
                  (Completeness.Erasure.Exposure.exposedRegion description
                    materialCanonical))
                exposedCanonical exposedExternalTwoEnded)
              absorbedEndpoint :=
            ((Relation.TransGen.single (Step.iteration duplication)).trans
              comprehension).tail (Step.ends ends)
          have exact := exposedEquates.1.transGen mandatory
          let absorbedFilledIso := occurrence.context.fillIso
            (Completeness.Erasure.TwoSite.absorbedTargetIso description
              materialCanonical)
          let absorbedOpenIso : OpenDiagramIso absorbedEndpoint target :=
            (OpenDiagram.withBody_iso absorbedCanonical targetCanonical
              absorbedExternalTwoEnded targetExternalTwoEnded
              absorbedFilledIso).trans targetIso.symm
          exact Completeness.transGen_iso (OpenDiagramIso.refl source) exact
            absorbedOpenIso
  | negative =>
      have localStep : UncappedErasure.Local after before := by
        simpa only [atPolarity, converse, polarityEq] using localEvidence
      cases localStep with
      | erase description =>
          let materialOccurrence : Occurrence description.source target := {
            interface := occurrence.interface
            context := occurrence.context
            sourceCanonical := targetCanonical
            sourceExternalTwoEnded := targetExternalTwoEnded
            host_iso := targetIso
          }
          obtain ⟨materialCanonical, exposedCanonical,
              exposedExternalTwoEnded, exposedEquates⟩ :=
            Completeness.Erasure.Exposure.equates description
              materialOccurrence occurrence.sourceCanonical
              occurrence.sourceExternalTwoEnded
          have specializedValidity :=
            Completeness.Erasure.TwoSite.specializedFilledValidity description
              materialCanonical materialOccurrence occurrence.sourceCanonical
              occurrence.sourceExternalTwoEnded
          have specializedCanonical : (occurrence.context.fill
              (Completeness.Erasure.TwoSite.specialized description
                materialCanonical)).Canonical := specializedValidity.1
          have specializedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
              occurrence.interface.boundaryWire
              (occurrence.context.fill
                (Completeness.Erasure.TwoSite.specialized description
                  materialCanonical)) := specializedValidity.2
          let specializedEndpoint := occurrence.interface.withBody
            (occurrence.context.fill
              (Completeness.Erasure.TwoSite.specialized description
                materialCanonical))
            specializedCanonical specializedExternalTwoEnded
          have quantifiedValidity :=
            Completeness.Erasure.TwoSite.quantifiedFilledValidity description
              materialOccurrence occurrence.sourceCanonical
              occurrence.sourceExternalTwoEnded
          have quantifiedCanonical : (occurrence.context.fill
              (Completeness.Erasure.TwoSite.quantified description)).Canonical :=
            quantifiedValidity.1
          have quantifiedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
              occurrence.interface.boundaryWire
              (occurrence.context.fill
                (Completeness.Erasure.TwoSite.quantified description)) :=
            quantifiedValidity.2
          let quantifiedEndpoint := occurrence.interface.withBody
            (occurrence.context.fill
              (Completeness.Erasure.TwoSite.quantified description))
            quantifiedCanonical quantifiedExternalTwoEnded
          have absorbedValidity :=
            Completeness.Erasure.TwoSite.absorbedFilledValidity description
              materialCanonical materialOccurrence occurrence.sourceCanonical
              occurrence.sourceExternalTwoEnded
          have absorbedCanonical : (occurrence.context.fill
              (Completeness.Erasure.TwoSite.absorbed description
                materialCanonical)).Canonical := absorbedValidity.1
          have absorbedExternalTwoEnded : OpenDiagram.ExternalTwoEnded
              occurrence.interface.boundaryWire
              (occurrence.context.fill
                (Completeness.Erasure.TwoSite.absorbed description
                  materialCanonical)) := absorbedValidity.2
          let absorbedEndpoint := occurrence.interface.withBody
            (occurrence.context.fill
              (Completeness.Erasure.TwoSite.absorbed description
                materialCanonical))
            absorbedCanonical absorbedExternalTwoEnded
          let absorbedOccurrence : Occurrence
              (Completeness.Erasure.TwoSite.absorbed description
                materialCanonical) absorbedEndpoint :=
            Completeness.exactOccurrence occurrence.interface
              occurrence.context
              (Completeness.Erasure.TwoSite.absorbed description
                materialCanonical)
              absorbedCanonical absorbedExternalTwoEnded
          have ends : WirePrimitive.Ends absorbedEndpoint quantifiedEndpoint := by
            exact ⟨outer,
              Completeness.Erasure.TwoSite.absorbed description
                materialCanonical,
              Completeness.Erasure.TwoSite.quantified description,
              absorbedOccurrence, quantifiedCanonical,
              quantifiedExternalTwoEnded, OpenDiagramIso.refl _, by
                simpa only [absorbedOccurrence,
                  Completeness.exactOccurrence, polarityEq, atPolarity,
                  converse] using
                  (WirePrimitive.Content.Ends.Local.absorb
                    (Completeness.Erasure.TwoSite.absorbEvidence description
                      materialCanonical))⟩
          let comprehensionOccurrence : Occurrence
              (Completeness.Erasure.TwoSite.quantified description)
              quantifiedEndpoint :=
            Completeness.exactOccurrence occurrence.interface
              occurrence.context
              (Completeness.Erasure.TwoSite.quantified description)
              quantifiedCanonical quantifiedExternalTwoEnded
          let continuation :=
            Completeness.Comprehension.Telescope.refl .negative
              occurrence.interface occurrence.context
              (Completeness.Erasure.TwoSite.quantifiedFilledValidity description
                materialOccurrence occurrence.sourceCanonical
                occurrence.sourceExternalTwoEnded).1
              (Completeness.Erasure.TwoSite.quantifiedFilledValidity description
                materialOccurrence occurrence.sourceCanonical
                occurrence.sourceExternalTwoEnded).2
              polarityEq
          let request : Completeness.Comprehension.Telescope.Request
              (Completeness.Erasure.TwoSite.specialized description
                materialCanonical)
              (Completeness.Erasure.TwoSite.quantified description) := {
            boundary := boundary
            source := quantifiedEndpoint
            endpoint := Completeness.Erasure.TwoSite.quantified description
            polarity := .negative
            occurrence := comprehensionOccurrence
            instantiatedCanonical := specializedCanonical
            instantiatedExternalTwoEnded := specializedExternalTwoEnded
            pendingCanonical := quantifiedCanonical
            pendingExternalTwoEnded := quantifiedExternalTwoEnded
            endpointCanonical := quantifiedCanonical
            endpointExternalTwoEnded := quantifiedExternalTwoEnded
            continuation := continuation
          }
          have comprehension : Relation.TransGen Step quantifiedEndpoint
              specializedEndpoint := by
            simpa only [request,
              Completeness.Comprehension.Telescope.Request.Result,
              Completeness.Comprehension.Telescope.StrictDerives,
              Completeness.Comprehension.polarityTarget,
              quantifiedEndpoint, specializedEndpoint] using
              Completeness.Comprehension.complete
                (Completeness.Erasure.TwoSite.pattern description
                  materialCanonical)
                (Completeness.Erasure.TwoSite.instantiates description
                  materialCanonical)
                request
          let exposedEndpoint := occurrence.interface.withBody
            (occurrence.context.fill
              (Completeness.Erasure.Exposure.exposedRegion description
                materialCanonical))
            exposedCanonical exposedExternalTwoEnded
          let exposedOccurrence : Occurrence
              (Completeness.Erasure.Exposure.exposedRegion description
                materialCanonical) exposedEndpoint :=
            Completeness.exactOccurrence occurrence.interface
              occurrence.context
              (Completeness.Erasure.Exposure.exposedRegion description
                materialCanonical)
              exposedCanonical exposedExternalTwoEnded
          let nested :=
            Completeness.Erasure.Duplication.exposedNestedOccurrence
              description materialCanonical exposedOccurrence
          let duplicationPresentation : RegionIso
              (WireEquiv.refl occurrence.interface.external)
              (nested.targetBody
                ((nested.selected.renameWires
                    nested.descendant.outerWire).conjoin nested.before))
              (occurrence.context.fill
                (Completeness.Erasure.TwoSite.specialized description
                  materialCanonical)) := by
            rw [show nested.targetBody
                ((nested.selected.renameWires
                    nested.descendant.outerWire).conjoin nested.before) =
                  occurrence.context.fill
                    (Completeness.Erasure.TwoSite.targetPresentation description
                      materialCanonical) by
              simp only [nested, exposedOccurrence,
                Completeness.exactOccurrence,
                Completeness.Erasure.Duplication.exposedNestedOccurrence,
                NestedOccurrence.targetBody, nestedBody,
                DiagramContext.fill, DiagramContext.outerWire,
                Completeness.Erasure.TwoSite.targetPresentation,
                Completeness.Erasure.TwoSite.baseInstance,
                Completeness.Erasure.TwoSite.pattern]
              rw [Region.renameWires_id]]
            exact occurrence.context.fillIso
              (Completeness.Erasure.TwoSite.specializedTargetIso
                description materialCanonical).symm
          have duplication : Iteration exposedEndpoint specializedEndpoint := by
            exact Completeness.Erasure.Duplication.exposedCopyStep description
              materialCanonical exposedOccurrence
              (occurrence.context.fill
                (Completeness.Erasure.TwoSite.specialized description
                  materialCanonical))
              duplicationPresentation specializedCanonical
              specializedExternalTwoEnded
          have mandatory : Relation.TransGen Step absorbedEndpoint
              exposedEndpoint :=
            ((Relation.TransGen.single (Step.ends ends)).trans
              comprehension).tail (Step.iteration duplication.symm)
          let absorbedFilledIso := occurrence.context.fillIso
            (Completeness.Erasure.TwoSite.absorbedTargetIso description
              materialCanonical)
          let sourceIso : OpenDiagramIso absorbedEndpoint source :=
            (OpenDiagram.withBody_iso absorbedCanonical
              occurrence.sourceCanonical absorbedExternalTwoEnded
              occurrence.sourceExternalTwoEnded absorbedFilledIso).trans
                occurrence.host_iso.symm
          have presented := Completeness.transGen_iso sourceIso mandatory
            (OpenDiagramIso.refl exposedEndpoint)
          exact presented.reflTransGen exposedEquates.2

end VisualProof.Rule.UncappedErasure

namespace VisualProof.Rule.Erasure

open Diagram
open Theory

/-- Add the strong erasure's selected cap block while the material is still
present, then move that block into the surviving host presentation. -/
theorem capEquates
    {boundary outer : List Theory.Sig}
    (description : Erasure.Description outer)
    {source : OpenDiagram boundary}
    (occurrence : Occurrence description.source source) :
    let cappedSource := Region.spliceAt description.hostLocals
      (description.hostItems.append description.caps)
      description.material description.wireMap
    ∃ targetCanonical :
        (occurrence.context.fill cappedSource).Canonical,
      ∃ targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill cappedSource),
        Completeness.Equates occurrence cappedSource targetCanonical
          targetExternalTwoEnded := by
  dsimp only
  generalize materialEq :
    description.material.renameWires description.wireMap = material
  cases material with
  | mk materialLocals materialItems =>
      let hostRename := Region.adjoinHostWire outer
        description.hostLocals materialLocals
      let materialRename := Region.adjoinMaterialWire outer
        description.hostLocals materialLocals
      let selected : ∀ {signature},
          Var (outer ++ description.hostLocals) signature → Bool :=
        fun wire => decide
          ((description.hostItems.incidencePaths wire.index.val 0).length = 1)
      let host := description.hostItems.renameWires hostRename
      let materialItems' := materialItems.renameWires materialRename
      let pins := ItemSeq.pinWires (outer ++ description.hostLocals)
        hostRename selected
      let base := host.append materialItems'
      have directCanonical :
          (occurrence.context.fill
            (.mk (description.hostLocals ++ materialLocals) base)).Canonical := by
        simpa only [Erasure.Description.source,
          UncappedErasure.Description.source, Region.spliceAt,
          Region.adjoinAt, materialEq, hostRename, materialRename, host,
          materialItems', base] using occurrence.sourceCanonical
      have directExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill
            (.mk (description.hostLocals ++ materialLocals) base)) := by
        intro signature wire
        simpa only [Erasure.Description.source,
          UncappedErasure.Description.source, Region.spliceAt,
          Region.adjoinAt, materialEq, hostRename, materialRename, host,
          materialItems', base] using occurrence.sourceExternalTwoEnded wire
      obtain ⟨rawCanonical, rawExternalTwoEnded, rawEquates⟩ :=
        Completeness.pinWiresExact occurrence.interface occurrence.context
          base hostRename selected directCanonical directExternalTwoEnded
      let raw := Region.mk (description.hostLocals ++ materialLocals)
        (base.append pins)
      have rawCanonical' : (occurrence.context.fill raw).Canonical := by
        simpa only [pins, base, raw] using rawCanonical
      have rawExternalTwoEnded' : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill raw) := by
        intro signature wire
        simpa only [pins, base, raw] using rawExternalTwoEnded wire
      have compId : WireRenaming.comp hostRename WireRenaming.id =
          hostRename := by
        apply WireRenaming.ext
        intro signature wire
        rfl
      have pinsRename :
          description.caps.renameWires hostRename = pins := by
        simp only [Erasure.Description.caps,
          ItemSeq.pinWires_renameWires, compId, pins, selected]
      have rawEq : raw =
          Completeness.Comprehension.EqualityNormalization.appendAdjoinedPins
            description.hostLocals description.hostItems description.caps
            (.mk materialLocals materialItems) := by
        simp only [raw,
          Completeness.Comprehension.EqualityNormalization.appendAdjoinedPins,
          hostRename, materialRename, host, materialItems', base, pinsRename,
          ItemSeq.append_assoc]
      let cappedSource := Region.adjoinAt description.hostLocals
        (description.hostItems.append description.caps)
        (.mk materialLocals materialItems)
      let presentation : RegionIso (WireEquiv.refl outer) raw cappedSource := by
        rw [rawEq]
        exact
          Completeness.Comprehension.EqualityNormalization.adjoinPinsIso
            description.hostLocals description.hostItems description.caps
            (.mk materialLocals materialItems)
      have rawLocalCanonical : raw.Canonical :=
        occurrence.context.holeCanonical raw rawCanonical'
      have cappedLocalCanonical : cappedSource.Canonical :=
        presentation.canonical_iff.mp rawLocalCanonical
      have sameNonempty : ∀ {signature} (wire : Var outer signature),
          raw.incidencePaths wire.index.val ≠ [] ↔
            cappedSource.incidencePaths wire.index.val ≠ [] := by
        intro signature wire
        rw [← List.length_pos_iff, ← List.length_pos_iff,
          presentation.incidencePaths_length_eq wire]
      have replacement := occurrence.context.replaceCanonical raw cappedSource
        rawCanonical' cappedLocalCanonical sameNonempty
      let targetCanonical := replacement.1
      let rawEndpoint := occurrence.interface.withBody
        (occurrence.context.fill raw) rawCanonical' rawExternalTwoEnded'
      let directEndpoint := occurrence.interface.withBody
        (occurrence.context.fill
          (.mk (description.hostLocals ++ materialLocals) base))
        directCanonical directExternalTwoEnded
      let sourceIso : OpenDiagramIso source directEndpoint := by
        simpa only [directEndpoint, Erasure.Description.source,
          UncappedErasure.Description.source, Region.spliceAt,
          Region.adjoinAt, materialEq, hostRename, materialRename, host,
          materialItems', base] using occurrence.host_iso
      have targetExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          occurrence.interface.boundaryWire
          (occurrence.context.fill cappedSource) :=
        rawEndpoint.externalTwoEnded_of_nonempty_iff _ replacement.2
      let targetEndpoint := occurrence.interface.withBody
        (occurrence.context.fill cappedSource) targetCanonical
          targetExternalTwoEnded
      let endpointIso : OpenDiagramIso rawEndpoint targetEndpoint :=
        OpenDiagram.withBody_iso rawCanonical' targetCanonical
          rawExternalTwoEnded' targetExternalTwoEnded
          (occurrence.context.fillIso presentation)
      have rawForward : Relation.ReflTransGen Step source rawEndpoint := by
        exact
          Completeness.Comprehension.EqualityNormalization.reflTransGen_iso
            sourceIso.symm (by
              simpa only [pins, base, raw, rawEndpoint, directEndpoint,
                Completeness.exactOccurrence] using rawEquates.1)
            (OpenDiagramIso.refl rawEndpoint)
      have rawReverse : Relation.ReflTransGen Step rawEndpoint source := by
        exact
          Completeness.Comprehension.EqualityNormalization.reflTransGen_iso
            (OpenDiagramIso.refl rawEndpoint) (by
              simpa only [pins, base, raw, rawEndpoint, directEndpoint,
                Completeness.exactOccurrence] using rawEquates.2)
            sourceIso.symm
      have presented : Completeness.Equates occurrence cappedSource
          targetCanonical targetExternalTwoEnded := ⟨
        Completeness.Comprehension.EqualityNormalization.reflTransGen_iso
          (OpenDiagramIso.refl source) rawForward endpointIso,
        Completeness.Comprehension.EqualityNormalization.reflTransGen_iso
          endpointIso rawReverse (OpenDiagramIso.refl source)⟩
      simpa only [cappedSource, materialEq, Erasure.Description.source,
        UncappedErasure.Description.source, Region.spliceAt] using
          ⟨targetCanonical, targetExternalTwoEnded, presented⟩

/-- Every strong capping erasure is derivable by a nonempty chain of
primitive HOL-calculus steps. -/
theorem complete
    {boundary : List Theory.Sig}
    {source target : OpenDiagram boundary}
    (step : Erasure source target) :
    Relation.TransGen Step source target := by
  rcases step with ⟨outer, before, after, occurrence, targetCanonical,
    targetExternalTwoEnded, targetIso, localEvidence⟩
  cases polarityEq : occurrence.context.polarity with
  | positive =>
      have localStep : Erasure.Local before after := by
        simpa only [atPolarity, polarityEq] using localEvidence
      cases localStep with
      | erase description =>
          obtain ⟨cappedCanonical, cappedExternalTwoEnded, caps⟩ :=
            capEquates description occurrence
          let cappedSource := Region.spliceAt description.hostLocals
            (description.hostItems.append description.caps)
            description.material description.wireMap
          let cappedEndpoint := occurrence.interface.withBody
            (occurrence.context.fill cappedSource) cappedCanonical
              cappedExternalTwoEnded
          let cappedDescription : UncappedErasure.Description outer := {
            description with
            hostItems := description.hostItems.append description.caps
          }
          let cappedOccurrence : Occurrence cappedDescription.source
              cappedEndpoint := by
            simpa only [cappedDescription, cappedSource,
              UncappedErasure.Description.source] using
              Completeness.exactOccurrence occurrence.interface
                occurrence.context cappedSource cappedCanonical
                cappedExternalTwoEnded
          have uncapped : UncappedErasure cappedEndpoint target := by
            refine ⟨outer, cappedDescription.source,
              cappedDescription.target, cappedOccurrence, ?_, ?_, ?_, ?_⟩
            · simpa only [cappedDescription,
                UncappedErasure.Description.target,
                Erasure.Description.target] using targetCanonical
            · intro signature wire
              simpa only [cappedDescription,
                  UncappedErasure.Description.target,
                  Erasure.Description.target] using
                targetExternalTwoEnded wire
            · simpa only [cappedDescription,
                UncappedErasure.Description.target,
                Erasure.Description.target] using targetIso
            · rw [show cappedOccurrence.context.polarity = .positive by
                simpa only [cappedOccurrence, Completeness.exactOccurrence]
                  using polarityEq]
              exact UncappedErasure.Local.erase cappedDescription
          have core : Relation.TransGen Step cappedEndpoint target :=
            UncappedErasure.complete uncapped
          have pinPrefix : Relation.ReflTransGen Step source cappedEndpoint := by
            simpa only [cappedSource, cappedEndpoint,
              Completeness.Equates] using caps.1
          exact pinPrefix.transGen core
  | negative =>
      have localStep : Erasure.Local after before := by
        simpa only [atPolarity, converse, polarityEq] using localEvidence
      cases localStep with
      | erase description =>
          let materialOccurrence : Occurrence description.source target := {
            interface := occurrence.interface
            context := occurrence.context
            sourceCanonical := targetCanonical
            sourceExternalTwoEnded := targetExternalTwoEnded
            host_iso := targetIso
          }
          obtain ⟨cappedCanonical, cappedExternalTwoEnded, caps⟩ :=
            capEquates description materialOccurrence
          let cappedSource := Region.spliceAt description.hostLocals
            (description.hostItems.append description.caps)
            description.material description.wireMap
          let cappedEndpoint := occurrence.interface.withBody
            (occurrence.context.fill cappedSource) cappedCanonical
              cappedExternalTwoEnded
          let cappedDescription : UncappedErasure.Description outer := {
            description with
            hostItems := description.hostItems.append description.caps
          }
          let cappedTargetOccurrence : Occurrence cappedDescription.target
              source := by
            simpa only [cappedDescription,
              UncappedErasure.Description.target,
              Erasure.Description.target] using occurrence
          have uncapped : UncappedErasure source cappedEndpoint := by
            refine ⟨outer, cappedDescription.target,
              cappedDescription.source, cappedTargetOccurrence, ?_, ?_, ?_, ?_⟩
            · simpa only [cappedDescription, cappedSource,
                UncappedErasure.Description.source] using cappedCanonical
            · intro signature wire
              simpa only [cappedDescription, cappedSource,
                  UncappedErasure.Description.source] using
                cappedExternalTwoEnded wire
            · simpa only [cappedDescription, cappedSource,
                UncappedErasure.Description.source, cappedEndpoint] using
                (OpenDiagramIso.refl cappedEndpoint)
            · rw [show cappedTargetOccurrence.context.polarity = .negative by
                simpa only [cappedTargetOccurrence] using polarityEq]
              exact UncappedErasure.Local.erase cappedDescription
          have core : Relation.TransGen Step source cappedEndpoint :=
            UncappedErasure.complete uncapped
          have suffix : Relation.ReflTransGen Step cappedEndpoint target := by
            simpa only [cappedSource, cappedEndpoint,
              Completeness.Equates, materialOccurrence] using caps.2
          exact core.reflTransGen suffix

end VisualProof.Rule.Erasure
