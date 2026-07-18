import VisualProof.Rule.Soundness.Iteration.DeiterationSpliceMap

namespace VisualProof.Rule.IterationSoundness

open VisualProof
open VisualProof.Data.Finite
open VisualProof.Diagram

private theorem finCount_eq_of_equiv
    (equiv : FiniteEquiv (Fin left) (Fin right)) : left = right := by
  apply Nat.le_antisymm
  · exact fin_card_le_of_injective equiv equiv.injective
  · exact fin_card_le_of_injective equiv.symm equiv.symm.injective

private theorem deiterationMapFrameRegion_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (region : CRegion (deiterationRemoved input selection).val.regionCount) :
    (((deiterationReinsertInput input selection witness).plugLayout
      |>.mapFrameRegion region).rename
        (deiterationOutputRegionEquiv input selection witness)) =
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout.mapFrameRegion region := by
  cases region <;>
    simp [Splice.Input.PlugLayout.mapFrameRegion,
      CRegion.rename, deiterationOutputRegionEquiv_frame] <;> rfl

theorem deiterationMapPatternRegion_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (region : CRegion
      (deiterationReinsertInput input selection witness).pattern.val.diagram.regionCount) :
    (((deiterationReinsertInput input selection witness).plugLayout
      |>.mapPatternRegion region).rename
        (deiterationOutputRegionEquiv input selection witness)) =
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout.mapPatternRegion
          (region.rename
            (deiterationPatternOccurrenceEquiv input selection witness).diagram.regions) := by
  cases region with
  | sheet =>
      simp only [Splice.Input.PlugLayout.mapPatternRegion, CRegion.rename]
      rw [deiterationOutputRegionEquiv_frame]
      rfl
  | cut parent =>
      simp only [Splice.Input.PlugLayout.mapPatternRegion, CRegion.rename]
      rw [deiterationOutputRegionEquiv_body]
      rfl
  | bubble parent arity =>
      simp only [Splice.Input.PlugLayout.mapPatternRegion, CRegion.rename]
      rw [deiterationOutputRegionEquiv_body]
      rfl

theorem deiterationOutputRegion_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (region : Fin
      (deiterationReinsertInput input selection witness).plugLayout.plugRaw.regionCount) :
    ((deiterationReinsertInput input selection witness).plugLayout.plugRaw.regions
        region).rename (deiterationOutputRegionEquiv input selection witness) =
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout.plugRaw.regions
          (deiterationOutputRegionEquiv input selection witness region) := by
  let source := deiterationReinsertInput input selection witness
  let target := Splice.Decomposition.originalFragmentInput
    (deiterationDecomposition input selection)
  let occurrence := deiterationPatternOccurrenceEquiv input selection witness
  let sourceLayout := source.plugLayout
  let targetLayout := target.plugLayout
  refine Fin.addCases (m := source.frame.val.regionCount)
    (n := sourceLayout.materialRegions.count) (fun frameRegion => ?_)
      (fun material => ?_) region
  · change (sourceLayout.plugRegion (sourceLayout.frameRegion frameRegion)).rename
        (deiterationOutputRegionEquiv input selection witness) =
      targetLayout.plugRegion
        (deiterationOutputRegionEquiv input selection witness
          (sourceLayout.frameRegion frameRegion))
    rw [sourceLayout.plugRegion_frameRegion,
      deiterationOutputRegionEquiv_frame,
      targetLayout.plugRegion_frameRegion]
    exact deiterationMapFrameRegion_eq input selection witness
      (source.frame.val.regions frameRegion)
  · change (sourceLayout.plugRegion (sourceLayout.materialRegion material)).rename
        (deiterationOutputRegionEquiv input selection witness) =
      targetLayout.plugRegion
        (deiterationOutputRegionEquiv input selection witness
          (sourceLayout.materialRegion material))
    rw [sourceLayout.plugRegion_materialRegion,
      deiterationOutputRegionEquiv_material,
      targetLayout.plugRegion_materialRegion,
      deiterationMaterialEquiv_origin]
    calc
      (sourceLayout.mapPatternRegion
          (source.pattern.val.diagram.regions
            (sourceLayout.materialRegions.origin material))).rename
            (deiterationOutputRegionEquiv input selection witness) =
        targetLayout.mapPatternRegion
          ((source.pattern.val.diagram.regions
            (sourceLayout.materialRegions.origin material)).rename
              occurrence.diagram.regions) :=
        deiterationMapPatternRegion_eq input selection witness _
      _ = targetLayout.mapPatternRegion
          (target.pattern.val.diagram.regions
            (occurrence.diagram.regions
              (sourceLayout.materialRegions.origin material))) := by
        exact congrArg targetLayout.mapPatternRegion
          (occurrence.diagram.regions_eq
            (sourceLayout.materialRegions.origin material))

private theorem deiterationMapFrameNode_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (node : CNode (deiterationRemoved input selection).val.regionCount) :
    (((deiterationReinsertInput input selection witness).plugLayout
      |>.mapFrameNode node).rename
        (deiterationOutputRegionEquiv input selection witness)) =
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout.mapFrameNode node := by
  cases node <;>
    simp [Splice.Input.PlugLayout.mapFrameNode, CNode.rename,
      deiterationOutputRegionEquiv_frame] <;> rfl

private noncomputable def deiterationMapPatternNode_corresponds
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    {sourceNode : CNode
      (deiterationReinsertInput input selection witness).pattern.val.diagram.regionCount}
    {targetNode : CNode
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).pattern.val.diagram.regionCount}
    (certified : CNode.CertifiedCorresponds
      (deiterationPatternOccurrenceEquiv input selection witness).diagram.regions
      sourceNode targetNode) :
    CNode.CertifiedCorresponds
      (deiterationOutputRegionEquiv input selection witness)
      ((deiterationReinsertInput input selection witness).plugLayout
        |>.mapPatternNode sourceNode)
      ((Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout
          |>.mapPatternNode targetNode) := by
  let sourceLayout := (deiterationReinsertInput input selection witness).plugLayout
  let targetLayout := (Splice.Decomposition.originalFragmentInput
    (deiterationDecomposition input selection)).plugLayout
  cases certified with
  | term sourceRegion targetRegion ports sourceTerm targetTerm regionEq certificate =>
      exact .term (sourceLayout.bodyRegion sourceRegion)
        (targetLayout.bodyRegion targetRegion) ports sourceTerm targetTerm
        ((deiterationOutputRegionEquiv_body input selection witness sourceRegion).trans
          (congrArg targetLayout.bodyRegion regionEq)) certificate
  | atom sourceRegion sourceBinder targetRegion targetBinder regionEq binderEq =>
      exact .atom (sourceLayout.bodyRegion sourceRegion)
        (sourceLayout.binderRegion sourceBinder)
        (targetLayout.bodyRegion targetRegion)
        (targetLayout.binderRegion targetBinder)
        ((deiterationOutputRegionEquiv_body input selection witness sourceRegion).trans
          (congrArg targetLayout.bodyRegion regionEq))
        ((deiterationOutputRegionEquiv_binder input selection witness sourceBinder).trans
          (congrArg targetLayout.binderRegion binderEq))
  | named sourceRegion targetRegion definition arity regionEq =>
      exact .named (sourceLayout.bodyRegion sourceRegion)
        (targetLayout.bodyRegion targetRegion) definition arity
        ((deiterationOutputRegionEquiv_body input selection witness sourceRegion).trans
          (congrArg targetLayout.bodyRegion regionEq))

noncomputable def deiterationOutputNode_correspond
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (node : Fin
      (deiterationReinsertInput input selection witness).plugLayout.plugRaw.nodeCount) :
    CNode.CertifiedCorresponds
      (deiterationOutputRegionEquiv input selection witness)
      ((deiterationReinsertInput input selection witness).plugLayout.plugRaw.nodes node)
      ((Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout.plugRaw.nodes
          (deiterationOutputNodeEquiv input selection witness node)) := by
  let source := deiterationReinsertInput input selection witness
  let target := Splice.Decomposition.originalFragmentInput
    (deiterationDecomposition input selection)
  let occurrence := deiterationPatternOccurrenceEquiv input selection witness
  let sourceLayout := source.plugLayout
  let targetLayout := target.plugLayout
  refine Fin.addCases (m := source.frame.val.nodeCount)
    (n := source.pattern.val.diagram.nodeCount) (fun frameNode => ?_)
      (fun patternNode => ?_) node
  · change CNode.CertifiedCorresponds
      (deiterationOutputRegionEquiv input selection witness)
      (sourceLayout.plugNode (sourceLayout.frameNode frameNode))
      (targetLayout.plugNode
        (deiterationOutputNodeEquiv input selection witness
          (sourceLayout.frameNode frameNode)))
    rw [sourceLayout.plugNode_frameNode,
      deiterationOutputNodeEquiv_frame,
      targetLayout.plugNode_frameNode]
    exact CNode.CertifiedCorresponds.ofRenameEq _
      (deiterationMapFrameNode_eq input selection witness
        (source.frame.val.nodes frameNode))
  · change CNode.CertifiedCorresponds
      (deiterationOutputRegionEquiv input selection witness)
      (sourceLayout.plugNode (sourceLayout.patternNode patternNode))
      (targetLayout.plugNode
        (deiterationOutputNodeEquiv input selection witness
          (sourceLayout.patternNode patternNode)))
    rw [sourceLayout.plugNode_patternNode,
      deiterationOutputNodeEquiv_pattern,
      targetLayout.plugNode_patternNode]
    exact deiterationMapPatternNode_corresponds input selection witness
      (occurrence.diagram.nodes_correspond patternNode)

theorem deiterationCoalescedScope_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (quotient :
      (deiterationReinsertInput input selection witness).wireQuotient.Carrier) :
    (deiterationReinsertInput input selection witness).coalescedScope quotient =
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).coalescedScope
          (deiterationQuotientEquiv input selection witness quotient) := by
  change (iterationInput (deiterationRemoved input selection)
      (deiterationRetainedSelection input selection witness)
      (deiterationReinsertTarget input selection)).coalescedScope quotient = _
  rw [iterationCoalescedScope_eq,
    Splice.Decomposition.originalCoalescedScope_eq,
    deiterationQuotientEquiv_origin]
  rfl

theorem deiterationCoalescedEndpoints_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (quotient :
      (deiterationReinsertInput input selection witness).wireQuotient.Carrier) :
    (deiterationReinsertInput input selection witness).coalescedEndpoints quotient =
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).coalescedEndpoints
          (deiterationQuotientEquiv input selection witness quotient) := by
  change (iterationInput (deiterationRemoved input selection)
      (deiterationRetainedSelection input selection witness)
      (deiterationReinsertTarget input selection)).coalescedEndpoints quotient = _
  rw [iterationCoalescedEndpoints_eq,
    Splice.Decomposition.originalCoalescedEndpoints_eq,
    deiterationQuotientEquiv_origin]
  rfl

theorem deiterationMapFrameEndpoint_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (endpoint : CEndpoint (deiterationRemoved input selection).val.nodeCount) :
    (((deiterationReinsertInput input selection witness).plugLayout
      |>.mapFrameEndpoint endpoint).rename
        (deiterationOutputNodeEquiv input selection witness)) =
      ((Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout
          |>.mapFrameEndpoint endpoint) := by
  cases endpoint
  simp [Splice.Input.PlugLayout.mapFrameEndpoint,
    CEndpoint.rename, deiterationOutputNodeEquiv_frame]
  rfl

theorem deiterationMapPatternEndpoint_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (endpoint : CEndpoint
      (deiterationReinsertInput input selection witness).pattern.val.diagram.nodeCount) :
    (((deiterationReinsertInput input selection witness).plugLayout
      |>.mapPatternEndpoint endpoint).rename
        (deiterationOutputNodeEquiv input selection witness)) =
      ((Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout
          |>.mapPatternEndpoint
            (endpoint.rename
              (deiterationPatternOccurrenceEquiv input selection witness).diagram.nodes)) := by
  cases endpoint
  simp [Splice.Input.PlugLayout.mapPatternEndpoint,
    CEndpoint.rename, deiterationOutputNodeEquiv_pattern]
  rfl

theorem deiterationMapPatternWire_scope_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (wire : Fin
      (deiterationReinsertInput input selection witness).pattern.val.diagram.wireCount) :
    deiterationOutputRegionEquiv input selection witness
        (((deiterationReinsertInput input selection witness).plugLayout
          |>.mapPatternWire
            ((deiterationReinsertInput input selection witness).pattern.val.diagram.wires
              wire)).scope) =
      (((Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout
          |>.mapPatternWire
            ((Splice.Decomposition.originalFragmentInput
              (deiterationDecomposition input selection)).pattern.val.diagram.wires
                ((deiterationPatternOccurrenceEquiv input selection witness).diagram.wires
                  wire))).scope) := by
  simp only [Splice.Input.PlugLayout.mapPatternWire]
  rw [deiterationOutputRegionEquiv_body]
  exact congrArg
    (Splice.Decomposition.originalFragmentInput
      (deiterationDecomposition input selection)).plugLayout.bodyRegion
    ((deiterationPatternOccurrenceEquiv input selection witness).diagram.wire_scope_eq wire)

theorem deiterationReinsertInput_pattern
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    (deiterationReinsertInput input selection witness).pattern =
      selectedFragment (deiterationRemoved input selection)
        (deiterationRetainedSelection input selection witness) := by
  rfl

theorem deiterationOriginalFragmentInput_pattern
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val) :
    (Splice.Decomposition.originalFragmentInput
      (deiterationDecomposition input selection)).pattern =
        selectedFragment input selection := by
  rfl

theorem deiterationMapPatternWire_endpoints_perm
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (wire : Fin
      (deiterationReinsertInput input selection witness).pattern.val.diagram.wireCount) :
    (((deiterationReinsertInput input selection witness).plugLayout.mapPatternWire
        ((deiterationReinsertInput input selection witness).pattern.val.diagram.wires
          wire)).endpoints.map
      (CEndpoint.rename (deiterationOutputNodeEquiv input selection witness))).Perm
        ((Splice.Decomposition.originalFragmentInput
          (deiterationDecomposition input selection)).plugLayout.mapPatternWire
            ((Splice.Decomposition.originalFragmentInput
              (deiterationDecomposition input selection)).pattern.val.diagram.wires
                ((deiterationPatternOccurrenceEquiv input selection witness).diagram.wires
                  wire))).endpoints := by
  let occurrence := deiterationPatternOccurrenceEquiv input selection witness
  let sourceLayout := (deiterationReinsertInput input selection witness).plugLayout
  let targetLayout := (Splice.Decomposition.originalFragmentInput
    (deiterationDecomposition input selection)).plugLayout
  have mapped := (occurrence.diagram.wire_endpoints_perm wire).map
    targetLayout.mapPatternEndpoint
  change ((((selectedFragment (deiterationRemoved input selection)
      (deiterationRetainedSelection input selection witness)).diagram.wires wire).endpoints.map
        sourceLayout.mapPatternEndpoint).map
          (CEndpoint.rename (deiterationOutputNodeEquiv input selection witness))).Perm
    (((selectedFragment input selection).diagram.wires
      (occurrence.diagram.wires wire)).endpoints.map targetLayout.mapPatternEndpoint)
  let endpoints := ((selectedFragment (deiterationRemoved input selection)
    (deiterationRetainedSelection input selection witness)).diagram.wires wire).endpoints
  have mappedLists :
      (endpoints.map sourceLayout.mapPatternEndpoint).map
          (CEndpoint.rename (deiterationOutputNodeEquiv input selection witness)) =
        (endpoints.map (CEndpoint.rename occurrence.diagram.nodes)).map
          targetLayout.mapPatternEndpoint := by
    induction endpoints with
    | nil => rfl
    | cons endpoint tail induction =>
        change
          (sourceLayout.mapPatternEndpoint endpoint).rename
                (deiterationOutputNodeEquiv input selection witness) ::
              (tail.map sourceLayout.mapPatternEndpoint).map
                (CEndpoint.rename
                  (deiterationOutputNodeEquiv input selection witness)) =
            targetLayout.mapPatternEndpoint
                (endpoint.rename occurrence.diagram.nodes) ::
              (tail.map (CEndpoint.rename occurrence.diagram.nodes)).map
                targetLayout.mapPatternEndpoint
        have headEq :=
          deiterationMapPatternEndpoint_eq input selection witness endpoint
        rw [headEq, induction]
        rfl
  rw [mappedLists]
  exact mapped

theorem deiterationAttachment_alignment
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (position : Fin
      (deiterationReinsertInput input selection witness).pattern.val.boundary.length) :
    (deiterationReinsertInput input selection witness).attachment position =
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).attachment
          (Fin.cast
            (deiterationPatternOccurrenceEquiv input selection witness).boundary_length_eq
            position) := by
  let domains := deiterationDomains input selection
  let retained := deiterationRetainedSelection input selection witness
  let occurrence := deiterationPatternOccurrenceEquiv input selection witness
  let retainedPosition : Fin retained.touchingWires.length :=
    Fin.cast
      ((deiterationRemoved input selection).val.extractBoundaryRaw_length
        retained {}) position
  let justifierPosition : Fin witness.justifier.touchingWires.length :=
    Fin.cast (deiterationTouchingWireLengthEq input selection witness)
      retainedPosition
  let targetPosition : Fin
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).pattern.val.boundary.length :=
    Fin.cast occurrence.boundary_length_eq position
  let selectionPosition : Fin selection.touchingWires.length :=
    Fin.cast (input.val.extractBoundaryRaw_length selection {}) targetPosition
  apply domains.wires.origin_injective
  change domains.wires.origin
      (retained.touchingWires.get retainedPosition) =
    domains.wires.origin
      (Splice.Decomposition.originalAttachment
        (deiterationDecomposition input selection)
          targetPosition)
  rw [deiterationRetained_touchingWire_get_origin]
  have targetOrigin :
      domains.wires.origin
          (Splice.Decomposition.originalAttachment
            (deiterationDecomposition input selection) targetPosition) =
        selection.touchingWires.get selectionPosition := by
    change domains.wires.origin
        (domains.wires.index (selection.touchingWires.get selectionPosition) _) = _
    rw [domains.wires.origin_index]
  rw [targetOrigin]
  change witness.justifier.touchingWires.get justifierPosition =
    selection.touchingWires.get selectionPosition
  have transported := List.get_of_eq witness.sameAttachments justifierPosition
  simpa only [List.get_eq_getElem, Fin.val_cast] using transported

@[simp] theorem deiterationQuotientEquiv_quotientWire
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (wire : Fin (deiterationRemoved input selection).val.wireCount) :
    deiterationQuotientEquiv input selection witness
        ((deiterationReinsertInput input selection witness).quotientWire wire) =
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).quotientWire wire := by
  apply (Splice.Decomposition.originalQuotientWireEquiv
    (deiterationDecomposition input selection)).injective
  rw [deiterationQuotientEquiv_origin,
    Splice.Decomposition.originalQuotientWireEquiv_quotientWire]
  exact iterationQuotientWireEquiv_quotientWire
    (deiterationRemoved input selection)
    (deiterationRetainedSelection input selection witness)
    (deiterationReinsertTarget input selection) wire

theorem deiterationExposedAttachment_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (sourceExternal : Fin
      (deiterationReinsertInput input selection witness).pattern.val.exposedWires.length)
    (targetExternal : Fin
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).pattern.val.exposedWires.length)
    (wireEq :
      (deiterationPatternOccurrenceEquiv input selection witness).diagram.wires
          ((deiterationReinsertInput input selection witness).pattern.val.exposedWires.get
            sourceExternal) =
        (Splice.Decomposition.originalFragmentInput
          (deiterationDecomposition input selection)).pattern.val.exposedWires.get
            targetExternal) :
    deiterationQuotientEquiv input selection witness
        ((deiterationReinsertInput input selection witness).plugLayout.exposedAttachment
          sourceExternal) =
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout.exposedAttachment
          targetExternal := by
  let source := deiterationReinsertInput input selection witness
  let target := Splice.Decomposition.originalFragmentInput
    (deiterationDecomposition input selection)
  let occurrence := deiterationPatternOccurrenceEquiv input selection witness
  let sourcePosition := source.plugLayout.exposedPosition sourceExternal
  let targetPosition := target.plugLayout.exposedPosition targetExternal
  have sourceWire := source.plugLayout.exposedPosition_sound sourceExternal
  have targetWire := target.plugLayout.exposedPosition_sound targetExternal
  let mappedPosition : Fin
      (source.pattern.val.boundary.map occurrence.diagram.wires).length :=
    Fin.cast (List.length_map occurrence.diagram.wires).symm sourcePosition
  have boundaryAtSource :
      occurrence.diagram.wires (source.pattern.val.boundary.get sourcePosition) =
        target.pattern.val.boundary.get
          (Fin.cast occurrence.boundary_length_eq sourcePosition) := by
    have transported := List.get_of_eq occurrence.boundary mappedPosition
    simpa only [List.get_eq_getElem, List.getElem_map, Fin.val_cast] using transported
  have boundaryEq :
      target.pattern.val.boundary.get
          (Fin.cast occurrence.boundary_length_eq sourcePosition) =
        target.pattern.val.boundary.get targetPosition := by
    calc
      _ = occurrence.diagram.wires
          (source.pattern.val.exposedWires.get sourceExternal) := by
            rw [← boundaryAtSource]
            exact congrArg occurrence.diagram.wires sourceWire
      _ = target.pattern.val.exposedWires.get targetExternal := wireEq
      _ = _ := targetWire.symm
  have positionEq : Fin.cast occurrence.boundary_length_eq sourcePosition =
      targetPosition := by
    exact Splice.Decomposition.originalBoundary_get_injective
      (deiterationDecomposition input selection) boundaryEq
  unfold Splice.Input.PlugLayout.exposedAttachment
  rw [deiterationQuotientEquiv_quotientWire]
  apply congrArg target.quotientWire
  rw [deiterationAttachment_alignment input selection witness sourcePosition]
  exact congrArg target.attachment positionEq

theorem deiterationMappedBoundaryEndpoints_mem_iff
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (quotient :
      (deiterationReinsertInput input selection witness).wireQuotient.Carrier)
    (endpoint : CEndpoint
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout.nodeCount) :
    endpoint ∈
        ((deiterationReinsertInput input selection witness).plugLayout
          |>.boundaryEndpoints quotient |>.map
            (CEndpoint.rename
              (deiterationOutputNodeEquiv input selection witness))) ↔
      endpoint ∈
        (Splice.Decomposition.originalFragmentInput
          (deiterationDecomposition input selection)).plugLayout.boundaryEndpoints
            (deiterationQuotientEquiv input selection witness quotient) := by
  let source := deiterationReinsertInput input selection witness
  let target := Splice.Decomposition.originalFragmentInput
    (deiterationDecomposition input selection)
  let occurrence := deiterationPatternOccurrenceEquiv input selection witness
  let sourceLayout := source.plugLayout
  let targetLayout := target.plugLayout
  constructor
  · intro member
    obtain ⟨mapped, mappedMember, mappedEq⟩ := List.mem_map.mp member
    obtain ⟨sourceExternal, attachmentEq, original, originalMember,
        originalEq⟩ :=
      (sourceLayout.mem_boundaryEndpoints quotient mapped).1 mappedMember
    let sourceWire := source.pattern.val.exposedWires.get sourceExternal
    have targetExposed : occurrence.diagram.wires sourceWire ∈
        target.pattern.val.exposedWires :=
      (occurrence.mem_exposedWires_iff sourceWire).2 (List.get_mem _ _)
    obtain ⟨targetExternal, targetWire⟩ := List.mem_iff_get.mp targetExposed
    have exposedEq : occurrence.diagram.wires sourceWire =
        target.pattern.val.exposedWires.get targetExternal := targetWire.symm
    have targetAttachment : targetLayout.exposedAttachment targetExternal =
        deiterationQuotientEquiv input selection witness quotient := by
      rw [← deiterationExposedAttachment_eq input selection witness
        sourceExternal targetExternal exposedEq, attachmentEq]
    apply (targetLayout.mem_boundaryEndpoints
      (deiterationQuotientEquiv input selection witness quotient) endpoint).2
    refine ⟨targetExternal, targetAttachment,
      original.rename occurrence.diagram.nodes, ?_, ?_⟩
    · change original.rename occurrence.diagram.nodes ∈
        ((selectedFragment input selection).diagram.wires
          (target.pattern.val.exposedWires.get targetExternal)).endpoints
      rw [← exposedEq]
      exact occurrence.diagram.endpointOccurs_transport originalMember
    · rw [← mappedEq, ← originalEq]
      exact (deiterationMapPatternEndpoint_eq input selection witness original).symm
  · intro member
    obtain ⟨targetExternal, attachmentEq, targetOriginal, targetOriginalMember,
        targetOriginalEq⟩ :=
      (targetLayout.mem_boundaryEndpoints
        (deiterationQuotientEquiv input selection witness quotient) endpoint).1 member
    let targetWire := target.pattern.val.exposedWires.get targetExternal
    let sourceWire := occurrence.diagram.wires.symm targetWire
    have targetExposed : targetWire ∈ target.pattern.val.exposedWires :=
      List.get_mem _ _
    have sourceExposed : sourceWire ∈ source.pattern.val.exposedWires := by
      change sourceWire ∈ (selectedFragment (deiterationRemoved input selection)
        (deiterationRetainedSelection input selection witness)).exposedWires
      apply (occurrence.mem_exposedWires_iff sourceWire).1
      change occurrence.diagram.wires sourceWire ∈
        (selectedFragment input selection).exposedWires
      rw [show occurrence.diagram.wires sourceWire = targetWire from
        occurrence.diagram.wires.right_inv targetWire]
      exact targetExposed
    obtain ⟨sourceExternal, sourceWireEq⟩ := List.mem_iff_get.mp sourceExposed
    have exposedEq : occurrence.diagram.wires
          (source.pattern.val.exposedWires.get sourceExternal) =
        target.pattern.val.exposedWires.get targetExternal := by
      calc
        _ = occurrence.diagram.wires sourceWire :=
          congrArg occurrence.diagram.wires sourceWireEq
        _ = targetWire := occurrence.diagram.wires.right_inv targetWire
        _ = _ := rfl
    have sourceAttachment : sourceLayout.exposedAttachment sourceExternal =
        quotient := by
      apply (deiterationQuotientEquiv input selection witness).injective
      rw [deiterationExposedAttachment_eq input selection witness
        sourceExternal targetExternal exposedEq, attachmentEq]
    have targetEndpointMember : targetOriginal ∈
        (target.pattern.val.diagram.wires
          (occurrence.diagram.wires
            (source.pattern.val.exposedWires.get sourceExternal))).endpoints := by
      rw [exposedEq]
      exact targetOriginalMember
    have mappedEndpointMember :=
      (occurrence.diagram.wire_endpoints_perm
        (source.pattern.val.exposedWires.get sourceExternal)).mem_iff.mpr
          targetEndpointMember
    obtain ⟨sourceOriginal, sourceOriginalMember, sourceOriginalEq⟩ :=
      List.mem_map.mp mappedEndpointMember
    apply List.mem_map.mpr
    refine ⟨sourceLayout.mapPatternEndpoint sourceOriginal, ?_, ?_⟩
    · apply (sourceLayout.mem_boundaryEndpoints quotient _).2
      exact ⟨sourceExternal, sourceAttachment, sourceOriginal,
        sourceOriginalMember, rfl⟩
    · calc
        (sourceLayout.mapPatternEndpoint sourceOriginal).rename
            (deiterationOutputNodeEquiv input selection witness) =
          targetLayout.mapPatternEndpoint
            (sourceOriginal.rename occurrence.diagram.nodes) :=
              deiterationMapPatternEndpoint_eq input selection witness sourceOriginal
        _ = targetLayout.mapPatternEndpoint targetOriginal :=
          congrArg targetLayout.mapPatternEndpoint sourceOriginalEq
        _ = endpoint := targetOriginalEq

private theorem deiterationPerm_of_nodup_and_mem_iff
    {values other : List α} [BEq α] [LawfulBEq α]
    (valuesNodup : values.Nodup) (otherNodup : other.Nodup)
    (members : ∀ value, value ∈ values ↔ value ∈ other) :
    values.Perm other := by
  rw [List.perm_iff_count]
  intro value
  rw [valuesNodup.count, otherNodup.count]
  by_cases member : value ∈ values
  · have otherMember : value ∈ other := (members value).1 member
    simp [member, otherMember]
  · have otherNotMember : value ∉ other :=
      fun present => member ((members value).2 present)
    simp [member, otherNotMember]

theorem deiterationBoundaryEndpoints_perm
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (quotient :
      (deiterationReinsertInput input selection witness).wireQuotient.Carrier) :
    ((deiterationReinsertInput input selection witness).plugLayout.boundaryEndpoints
        quotient |>.map
          (CEndpoint.rename
            (deiterationOutputNodeEquiv input selection witness))).Perm
      ((Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout.boundaryEndpoints
          (deiterationQuotientEquiv input selection witness quotient)) := by
  let sourceLayout := (deiterationReinsertInput input selection witness).plugLayout
  let targetLayout := (Splice.Decomposition.originalFragmentInput
    (deiterationDecomposition input selection)).plugLayout
  apply deiterationPerm_of_nodup_and_mem_iff
  · apply List.Pairwise.map
      (R := fun left right => left ≠ right)
      (S := fun left right => left ≠ right)
      (CEndpoint.rename (deiterationOutputNodeEquiv input selection witness))
    · intro left right different equality
      exact different (CEndpoint.rename_injective
        (deiterationOutputNodeEquiv input selection witness) equality)
    · exact sourceLayout.boundaryEndpoints_nodup quotient
  · exact targetLayout.boundaryEndpoints_nodup
      (deiterationQuotientEquiv input selection witness quotient)
  · exact deiterationMappedBoundaryEndpoints_mem_iff input selection witness quotient

theorem deiterationMappedCoalescedEndpoints_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (quotient :
      (deiterationReinsertInput input selection witness).wireQuotient.Carrier) :
    ((((deiterationReinsertInput input selection witness).coalescedEndpoints quotient).map
        (deiterationReinsertInput input selection witness).plugLayout.mapFrameEndpoint).map
          (CEndpoint.rename
            (deiterationOutputNodeEquiv input selection witness))) =
      ((Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).coalescedEndpoints
          (deiterationQuotientEquiv input selection witness quotient)).map
            (Splice.Decomposition.originalFragmentInput
              (deiterationDecomposition input selection)).plugLayout.mapFrameEndpoint := by
  let endpoints :=
    (deiterationReinsertInput input selection witness).coalescedEndpoints quotient
  rw [← deiterationCoalescedEndpoints_eq input selection witness quotient]
  change (endpoints.map
      (deiterationReinsertInput input selection witness).plugLayout.mapFrameEndpoint).map
        (CEndpoint.rename
          (deiterationOutputNodeEquiv input selection witness)) =
    endpoints.map
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout.mapFrameEndpoint
  induction endpoints with
  | nil => rfl
  | cons endpoint tail induction =>
      change
        ((deiterationReinsertInput input selection witness).plugLayout
            |>.mapFrameEndpoint endpoint).rename
              (deiterationOutputNodeEquiv input selection witness) :: _ =
          ((Splice.Decomposition.originalFragmentInput
            (deiterationDecomposition input selection)).plugLayout
              |>.mapFrameEndpoint endpoint) :: _
      rw [deiterationMapFrameEndpoint_eq input selection witness endpoint, induction]
      rfl

theorem deiterationOutputWire_scope_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (wire : Fin
      (deiterationReinsertInput input selection witness).plugLayout.plugRaw.wireCount) :
    deiterationOutputRegionEquiv input selection witness
        ((deiterationReinsertInput input selection witness).plugLayout.plugRaw.wires
          wire).scope =
      ((Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout.plugRaw.wires
          (deiterationOutputWireEquiv input selection witness wire)).scope := by
  let source := deiterationReinsertInput input selection witness
  let target := Splice.Decomposition.originalFragmentInput
    (deiterationDecomposition input selection)
  let sourceLayout := source.plugLayout
  let targetLayout := target.plugLayout
  refine Fin.addCases (m := source.wireQuotient.count)
    (n := sourceLayout.internalWires.count) (fun quotient => ?_)
      (fun internal => ?_) wire
  · change deiterationOutputRegionEquiv input selection witness
        (sourceLayout.plugWire (sourceLayout.frameWire quotient)).scope =
      (targetLayout.plugWire
        (deiterationOutputWireEquiv input selection witness
          (sourceLayout.frameWire quotient))).scope
    rw [deiterationOutputWireEquiv_quotient,
      show sourceLayout.frameWire quotient =
        sourceLayout.quotientBlockWire quotient by rfl,
      sourceLayout.plugWire_quotientBlockWire,
      show targetLayout.frameWire
          (deiterationQuotientEquiv input selection witness quotient) =
        targetLayout.quotientBlockWire
          (deiterationQuotientEquiv input selection witness quotient) by rfl,
      targetLayout.plugWire_quotientBlockWire,
      deiterationOutputRegionEquiv_frame,
      deiterationCoalescedScope_eq]
  · change deiterationOutputRegionEquiv input selection witness
        (sourceLayout.plugWire (sourceLayout.internalWire internal)).scope =
      (targetLayout.plugWire
        (deiterationOutputWireEquiv input selection witness
          (sourceLayout.internalWire internal))).scope
    rw [deiterationOutputWireEquiv_internal,
      show sourceLayout.internalWire internal =
        sourceLayout.internalBlockWire internal by rfl,
      sourceLayout.plugWire_internalBlockWire,
      show targetLayout.internalWire
          (deiterationInternalWireEquiv input selection witness internal) =
        targetLayout.internalBlockWire
          (deiterationInternalWireEquiv input selection witness internal) by rfl,
      targetLayout.plugWire_internalBlockWire,
      deiterationInternalWireEquiv_origin]
    exact deiterationMapPatternWire_scope_eq input selection witness
      (sourceLayout.internalWires.origin internal)

theorem deiterationOutputWire_endpoints_perm
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (wire : Fin
      (deiterationReinsertInput input selection witness).plugLayout.plugRaw.wireCount) :
    (((deiterationReinsertInput input selection witness).plugLayout.plugRaw.wires
        wire).endpoints.map
          (CEndpoint.rename
            (deiterationOutputNodeEquiv input selection witness))).Perm
      ((Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout.plugRaw.wires
          (deiterationOutputWireEquiv input selection witness wire)).endpoints := by
  let source := deiterationReinsertInput input selection witness
  let target := Splice.Decomposition.originalFragmentInput
    (deiterationDecomposition input selection)
  let sourceLayout := source.plugLayout
  let targetLayout := target.plugLayout
  refine Fin.addCases (m := source.wireQuotient.count)
    (n := sourceLayout.internalWires.count) (fun quotient => ?_)
      (fun internal => ?_) wire
  · change ((sourceLayout.plugWire
        (sourceLayout.frameWire quotient)).endpoints.map
          (CEndpoint.rename
            (deiterationOutputNodeEquiv input selection witness))).Perm
      (targetLayout.plugWire
        (deiterationOutputWireEquiv input selection witness
          (sourceLayout.frameWire quotient))).endpoints
    rw [deiterationOutputWireEquiv_quotient,
      show sourceLayout.frameWire quotient =
        sourceLayout.quotientBlockWire quotient by rfl,
      sourceLayout.plugWire_quotientBlockWire,
      show targetLayout.frameWire
          (deiterationQuotientEquiv input selection witness quotient) =
        targetLayout.quotientBlockWire
          (deiterationQuotientEquiv input selection witness quotient) by rfl,
      targetLayout.plugWire_quotientBlockWire]
    change ((((source.coalescedEndpoints quotient).map
        sourceLayout.mapFrameEndpoint) ++ sourceLayout.boundaryEndpoints quotient).map
          (CEndpoint.rename
            (deiterationOutputNodeEquiv input selection witness))).Perm
      (((target.coalescedEndpoints
        (deiterationQuotientEquiv input selection witness quotient)).map
          targetLayout.mapFrameEndpoint) ++
        targetLayout.boundaryEndpoints
          (deiterationQuotientEquiv input selection witness quotient))
    let coalesced := (source.coalescedEndpoints quotient).map
      sourceLayout.mapFrameEndpoint
    let boundary := sourceLayout.boundaryEndpoints quotient
    let rename := CEndpoint.rename
      (deiterationOutputNodeEquiv input selection witness)
    have mappedAppend : (coalesced ++ boundary).map rename =
        coalesced.map rename ++ boundary.map rename := by
      induction coalesced with
      | nil => rfl
      | cons endpoint tail induction =>
          change rename endpoint :: (tail ++ boundary).map rename =
            rename endpoint :: (tail.map rename ++ boundary.map rename)
          rw [induction]
    have firstPerm : ((coalesced ++ boundary).map rename).Perm
        (coalesced.map rename ++ boundary.map rename) := by
      rw [mappedAppend]
    have secondPerm : (coalesced.map rename ++ boundary.map rename).Perm
        (((target.coalescedEndpoints
          (deiterationQuotientEquiv input selection witness quotient)).map
            targetLayout.mapFrameEndpoint) ++
          targetLayout.boundaryEndpoints
            (deiterationQuotientEquiv input selection witness quotient)) := by
      rw [deiterationMappedCoalescedEndpoints_eq input selection witness quotient]
      exact (List.Perm.refl _).append
        (deiterationBoundaryEndpoints_perm input selection witness quotient)
    exact firstPerm.trans secondPerm
  · change ((sourceLayout.plugWire
        (sourceLayout.internalWire internal)).endpoints.map
          (CEndpoint.rename
            (deiterationOutputNodeEquiv input selection witness))).Perm
      (targetLayout.plugWire
        (deiterationOutputWireEquiv input selection witness
          (sourceLayout.internalWire internal))).endpoints
    rw [deiterationOutputWireEquiv_internal,
      show sourceLayout.internalWire internal =
        sourceLayout.internalBlockWire internal by rfl,
      sourceLayout.plugWire_internalBlockWire,
      show targetLayout.internalWire
          (deiterationInternalWireEquiv input selection witness internal) =
        targetLayout.internalBlockWire
          (deiterationInternalWireEquiv input selection witness internal) by rfl,
      targetLayout.plugWire_internalBlockWire,
      deiterationInternalWireEquiv_origin]
    exact deiterationMapPatternWire_endpoints_perm input selection witness
      (sourceLayout.internalWires.origin internal)

noncomputable def deiterationOutputOccurrenceEquiv
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection) :
    ConcreteOccurrenceEquiv
      (deiterationReinsertInput input selection witness).plugLayout.plugRaw
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout.plugRaw where
  regionCount_eq := finCount_eq_of_equiv
    (deiterationOutputRegionEquiv input selection witness)
  nodeCount_eq := finCount_eq_of_equiv
    (deiterationOutputNodeEquiv input selection witness)
  wireCount_eq := finCount_eq_of_equiv
    (deiterationOutputWireEquiv input selection witness)
  regions := deiterationOutputRegionEquiv input selection witness
  nodes := deiterationOutputNodeEquiv input selection witness
  wires := deiterationOutputWireEquiv input selection witness
  root_eq := by
    change deiterationOutputRegionEquiv input selection witness
        ((deiterationReinsertInput input selection witness).plugLayout.frameRegion
          (deiterationRemoved input selection).val.root) =
      (Splice.Decomposition.originalFragmentInput
        (deiterationDecomposition input selection)).plugLayout.frameRegion
          (Splice.Decomposition.originalFragmentInput
            (deiterationDecomposition input selection)).frame.val.root
    rw [deiterationOutputRegionEquiv_frame]
    rfl
  regions_eq := deiterationOutputRegion_eq input selection witness
  nodes_correspond := deiterationOutputNode_correspond input selection witness
  wire_scope_eq := deiterationOutputWire_scope_eq input selection witness
  wire_endpoints_perm :=
    deiterationOutputWire_endpoints_perm input selection witness

theorem deiterationOutputBoundary_eq
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (sourceBoundary : List
      (Fin (deiterationRemoved input selection).val.wireCount)) :
    (Splice.Input.PlugLayout.outputOpenRoot
      (deiterationReinsertInput input selection witness)
      (deiterationReinsertInput input selection witness).plugLayout
      sourceBoundary).boundary.map
        (deiterationOutputWireEquiv input selection witness) =
      (Splice.Input.PlugLayout.outputOpenRoot
        (Splice.Decomposition.originalFragmentInput
          (deiterationDecomposition input selection))
        (Splice.Decomposition.originalFragmentInput
          (deiterationDecomposition input selection)).plugLayout
        sourceBoundary).boundary := by
  let source := deiterationReinsertInput input selection witness
  let target := Splice.Decomposition.originalFragmentInput
    (deiterationDecomposition input selection)
  change (sourceBoundary.map
      (source.plugLayout.frameWire ∘ source.quotientWire)).map
        (deiterationOutputWireEquiv input selection witness) =
    sourceBoundary.map (target.plugLayout.frameWire ∘ target.quotientWire)
  induction sourceBoundary with
  | nil => rfl
  | cons wire tail induction =>
      change deiterationOutputWireEquiv input selection witness
            (source.plugLayout.frameWire (source.quotientWire wire)) ::
          (tail.map
            (source.plugLayout.frameWire ∘ source.quotientWire)).map
              (deiterationOutputWireEquiv input selection witness) =
        target.plugLayout.frameWire (target.quotientWire wire) ::
          tail.map (target.plugLayout.frameWire ∘ target.quotientWire)
      rw [deiterationOutputWireEquiv_quotient,
        deiterationQuotientEquiv_quotientWire, induction]
      rfl

noncomputable def deiterationOutputOpenOccurrenceEquiv
    (input : CheckedDiagram signature)
    (selection : CheckedSelection input.val)
    (witness : DeiterationWitness input selection)
    (sourceBoundary : List
      (Fin (deiterationRemoved input selection).val.wireCount)) :
    OpenOccurrenceEquiv
      (Splice.Input.PlugLayout.outputOpenRoot
        (deiterationReinsertInput input selection witness)
        (deiterationReinsertInput input selection witness).plugLayout
        sourceBoundary)
      (Splice.Input.PlugLayout.outputOpenRoot
        (Splice.Decomposition.originalFragmentInput
          (deiterationDecomposition input selection))
        (Splice.Decomposition.originalFragmentInput
          (deiterationDecomposition input selection)).plugLayout
        sourceBoundary) where
  diagram := deiterationOutputOccurrenceEquiv input selection witness
  boundary := deiterationOutputBoundary_eq input selection witness sourceBoundary

end VisualProof.Rule.IterationSoundness
