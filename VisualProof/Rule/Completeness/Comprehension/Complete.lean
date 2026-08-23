import VisualProof.Rule.Completeness.Comprehension.Leaf.Complete

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory
open WirePrimitive

/-- Canonicality of the endpoint selected by an occurrence polarity. -/
theorem polaritySourceCanonicalAt
    {outer holeWires : List Sig}
    (polarity : Polarity)
    (context : DiagramContext outer holeWires)
    (before after : Region holeWires)
    (beforeCanonical : (context.fill before).Canonical)
    (afterCanonical : (context.fill after).Canonical) :
    (context.fill (polaritySource polarity before after)).Canonical := by
  cases polarity
  · exact beforeCanonical
  · exact afterCanonical

/-- External two-endedness of the endpoint selected by an occurrence
polarity. -/
theorem polaritySourceExternalTwoEndedAt
    {boundary holeWires : List Sig}
    (polarity : Polarity)
    (interface : OpenDiagram boundary)
    (context : DiagramContext interface.external holeWires)
    (before after : Region holeWires)
    (beforeExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill before))
    (afterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      interface.boundaryWire (context.fill after)) :
    OpenDiagram.ExternalTwoEnded interface.boundaryWire
      (context.fill (polaritySource polarity before after)) := by
  cases polarity
  · exact beforeExternalTwoEnded
  · exact afterExternalTwoEnded

/-- Derive authoritative comprehension evidence directly into the exact
occurrence-indexed step chain requested by the caller.  The pattern and its
`Instantiates` witness determine every structural branch and all selected
sites; the caller supplies only the actual telescope request whose pending
endpoint is the quantified region. -/
theorem complete
    {arguments before after outer : List Sig}
    (pattern : OpenDiagram arguments)
    {quantified specialized : Region outer}
    (instantiates :
      _root_.VisualProof.Rule.Comprehension.Instantiates pattern before after
        quantified specialized)
    (request : Telescope.Request specialized quantified) :
    request.Result := by
  have compileSupportPattern :
      ∀ {materialWires structuralOuter structuralBefore structuralAfter :
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
        (structuralRequest : Telescope.Request
          (Region.adjoinAt (structuralBefore ++ structuralAfter) .nil result)
          (.mk (structuralBefore ++ .rel materialWires :: structuralAfter)
            items)),
        structuralRequest.Result := by
    intro materialWires structuralOuter structuralBefore structuralAfter
      material materialCanonical items result evidence structuralRequest
    cases materialWires with
    | nil =>
        cases material with
        | mk materialLocals materialItems =>
            cases materialLocals with
            | nil =>
                cases materialItems with
                | nil =>
                    have patternEq :
                        Erasure.Exposure.supportPattern
                          (Region.mk [] ItemSeq.nil)
                            materialCanonical =
                          _root_.VisualProof.Rule.Completeness.Comprehension.blankPattern := by
                      apply EqualityNormalization.OpenDiagram.eq_of_data
                      · rfl
                      · rfl
                      · rfl
                    rw [patternEq] at evidence
                    exact
                      _root_.VisualProof.Rule.Completeness.Comprehension.itemsEnds
                        evidence structuralRequest
                | cons materialHead materialTail =>
                    sorry
            | cons materialLocal materialLocals =>
                sorry
    | cons materialWire materialWires =>
        sorry
  cases instantiates with
  | @mk items result evidence =>
      let sites := normalizationSites
        (frame := normalizationFrame outer before after arguments) evidence
      let originalEndpoint := request.occurrence.interface.withBody
        (request.occurrence.context.fill
          (Region.adjoinAt (before ++ after) .nil result))
        request.instantiatedCanonical request.instantiatedExternalTwoEnded
      let normalizationOccurrence : Occurrence
          (Region.adjoinAt (before ++ after) .nil result)
          originalEndpoint :=
        exactOccurrence request.occurrence.interface
          request.occurrence.context
          (Region.adjoinAt (before ++ after) .nil result)
          request.instantiatedCanonical request.instantiatedExternalTwoEnded
      obtain ⟨normalized, normalizedEvidence, normalizedCanonical,
          normalizedExternalTwoEnded, normalizedIsomorphic, forward,
          reverse⟩ :=
        EqualityNormalization.normalizeItemsEquates pattern evidence sites
          normalizationOccurrence
      obtain ⟨normalizedIso⟩ := normalizedIsomorphic
      let normalizedInstantiated : Region outer :=
        Region.adjoinAt (before ++ after) .nil normalized
      let normalizedEndpoint := request.occurrence.interface.withBody
        (request.occurrence.context.fill normalizedInstantiated)
        normalizedCanonical normalizedExternalTwoEnded
      let phaseTarget :=
        if EqualityNormalization.itemsHaveSelection sites = false then
          originalEndpoint
        else
          normalizedEndpoint
      have normalizedSourceCanonical :
          (request.occurrence.context.fill
            (polaritySource request.polarity normalizedInstantiated
              request.endpoint)).Canonical := by
        exact polaritySourceCanonicalAt request.polarity
          request.occurrence.context normalizedInstantiated request.endpoint
          normalizedCanonical request.endpointCanonical
      have normalizedSourceExternalTwoEnded : OpenDiagram.ExternalTwoEnded
          request.occurrence.interface.boundaryWire
          (request.occurrence.context.fill
            (polaritySource request.polarity normalizedInstantiated
              request.endpoint)) := by
        exact polaritySourceExternalTwoEndedAt request.polarity
          request.occurrence.interface request.occurrence.context
          normalizedInstantiated request.endpoint normalizedExternalTwoEnded
          request.endpointExternalTwoEnded
      let normalizedRequest : Telescope.Request normalizedInstantiated
          (.mk (before ++ .rel arguments :: after) items) := {
        boundary := request.boundary
        source := request.occurrence.interface.withBody
          (request.occurrence.context.fill
            (polaritySource request.polarity normalizedInstantiated
              request.endpoint))
          normalizedSourceCanonical normalizedSourceExternalTwoEnded
        endpoint := request.endpoint
        polarity := request.polarity
        occurrence := exactOccurrence request.occurrence.interface
          request.occurrence.context
          (polaritySource request.polarity normalizedInstantiated
            request.endpoint)
          normalizedSourceCanonical normalizedSourceExternalTwoEnded
        instantiatedCanonical := normalizedCanonical
        instantiatedExternalTwoEnded := normalizedExternalTwoEnded
        pendingCanonical := request.pendingCanonical
        pendingExternalTwoEnded := request.pendingExternalTwoEnded
        endpointCanonical := request.endpointCanonical
        endpointExternalTwoEnded := request.endpointExternalTwoEnded
        continuation := request.continuation
      }
      let material :=
        _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate
          pattern (EqualityNormalization.formalPorts arguments)
      have materialCanonical : material.Canonical := by
        exact _root_.VisualProof.Rule.Comprehension.Instantiation.instantiate_canonical
          pattern (EqualityNormalization.formalPorts arguments)
      have supportEvidence :
          _root_.VisualProof.Rule.Comprehension.Instantiation.ItemsResult
            (Erasure.Exposure.supportPattern material materialCanonical)
            (_root_.VisualProof.Rule.Comprehension.retain outer before after
              arguments)
            (_root_.VisualProof.Rule.Comprehension.selected outer before after
              arguments)
            items normalized := by
        rw [EqualityNormalization.supportPattern_eq_identityBoundary pattern
          materialCanonical]
        exact normalizedEvidence
      have core : normalizedRequest.Result :=
        compileSupportPattern material materialCanonical supportEvidence
          normalizedRequest
      cases polarityEq : request.polarity with
      | positive =>
          have coreSteps : Relation.TransGen Step normalizedEndpoint
              (request.occurrence.interface.withBody
                (request.occurrence.context.fill request.endpoint)
                request.endpointCanonical request.endpointExternalTwoEnded) := by
            simpa only [normalizedRequest, Telescope.Request.Result,
              Telescope.Compiles, polarityEq, polaritySource, polarityTarget,
              exactOccurrence, normalizedEndpoint] using core
          have phaseIso : OpenDiagramIso phaseTarget normalizedEndpoint := by
            simpa only [phaseTarget, normalizedEndpoint] using normalizedIso
          have forwardSteps : Relation.ReflTransGen Step originalEndpoint
              phaseTarget := by
            simpa only [phaseTarget, normalizedEndpoint] using forward
          have exact : Relation.TransGen Step originalEndpoint
              (request.occurrence.interface.withBody
                (request.occurrence.context.fill request.endpoint)
                request.endpointCanonical request.endpointExternalTwoEnded) :=
            forwardSteps.transGen
              (transGen_iso phaseIso.symm coreSteps (OpenDiagramIso.refl _))
          have sourceIso : OpenDiagramIso originalEndpoint request.source := by
            simpa only [originalEndpoint, polarityEq, polaritySource] using
              request.occurrence.host_iso.symm
          have presented :=
            transGen_iso sourceIso exact (OpenDiagramIso.refl _)
          simpa only [Telescope.Request.Result, Telescope.Compiles,
            polarityEq, polarityTarget] using presented
      | negative =>
          have coreSteps : Relation.TransGen Step
              (request.occurrence.interface.withBody
                (request.occurrence.context.fill request.endpoint)
                request.endpointCanonical request.endpointExternalTwoEnded)
              normalizedEndpoint := by
            simpa only [normalizedRequest, Telescope.Request.Result,
              Telescope.Compiles, polarityEq, polaritySource, polarityTarget,
              exactOccurrence, normalizedEndpoint] using core
          have phaseIso : OpenDiagramIso phaseTarget normalizedEndpoint := by
            simpa only [phaseTarget, normalizedEndpoint] using normalizedIso
          have reverseSteps : Relation.ReflTransGen Step phaseTarget
              originalEndpoint := by
            simpa only [phaseTarget, normalizedEndpoint] using reverse
          have exact : Relation.TransGen Step
              (request.occurrence.interface.withBody
                (request.occurrence.context.fill request.endpoint)
                request.endpointCanonical request.endpointExternalTwoEnded)
              originalEndpoint :=
            (transGen_iso (OpenDiagramIso.refl _) coreSteps phaseIso.symm)
              |>.reflTransGen reverseSteps
          have sourceIso : OpenDiagramIso
              (request.occurrence.interface.withBody
                (request.occurrence.context.fill request.endpoint)
                request.endpointCanonical request.endpointExternalTwoEnded)
              request.source := by
            simpa only [polarityEq, polaritySource] using
              request.occurrence.host_iso.symm
          have presented :=
            transGen_iso sourceIso exact (OpenDiagramIso.refl _)
          simpa only [Telescope.Request.Result, Telescope.Compiles,
            polarityEq, polarityTarget, originalEndpoint] using presented


end VisualProof.Rule.Completeness.Comprehension
