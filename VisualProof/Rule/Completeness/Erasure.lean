import VisualProof.Rule.Completeness.Erasure.Duplication
import VisualProof.Rule.Completeness.Erasure.TwoSite
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
