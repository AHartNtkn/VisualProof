import VisualProof.Diagram.Concrete.WireQuantifierRelationJoinRaw

namespace VisualProof

namespace ConcreteWireQuantifier

namespace RelationJoinStep

/-- Generated request nodes occupy a one-to-one checked allocation range. -/
theorem checkedIdentityNode_injective
    (step : RelationJoinStep source dying content) :
    Function.Injective step.checkedIdentityNode := by
  intro left right same
  apply Fin.ext
  have values := congrArg Fin.val same
  simpa [checkedIdentityNode, Internal.checkedNode,
    ConcreteSpliceAttachment.identityNode] using values

/-- Copied fragment nodes and generated request nodes occupy disjoint checked
allocation ranges. -/
theorem checkedFragmentNode_ne_checkedIdentityNode
    (step : RelationJoinStep source dying content)
    (node : content.val.diagram.NodeId)
    (request : Fin step.attachment.identityRequests.length) :
    step.checkedFragmentNode node ≠ step.checkedIdentityNode request := by
  intro same
  have values := congrArg Fin.val same
  have underlying : step.attachment.fragmentNode node =
      step.attachment.identityNode request := by
    apply Fin.ext
    simpa [checkedFragmentNode, checkedIdentityNode,
      Internal.checkedNode] using values
  exact step.attachment.fragmentNode_ne_identityNode _ _ underlying

/-- A generated request node cannot collide with a transported prior node. -/
theorem checkedPriorNode_ne_checkedIdentityNode
    (step : RelationJoinStep source dying content)
    (prior : step.prior.val.NodeId)
    (different : prior ≠ step.priorApplication)
    (request : Fin step.attachment.identityRequests.length) :
    step.checkedPriorNode prior different ≠
      step.checkedIdentityNode request := by
  intro same
  have values := congrArg Fin.val same
  have priorBound :=
    (ConcreteDiagram.DenseErasure.eraseNodeIndex
      step.prior step.priorApplication prior (by
        simp [ConcreteDiagram.DenseErasure.retainedNodes,
          ConcreteDiagram.nodesList, Data.Finite.mem_allFin,
          different])).isLt
  have erasedCount :
      (ConcreteDiagram.DenseErasure.eraseNodeCandidate
        step.prior step.priorApplication).nodeCount + 1 =
        step.prior.val.nodeCount :=
    Data.Finite.filter_not_mem_length_add_removed_length
      [step.priorApplication] (by simp)
  have baseCount := step.base_nodeCount_add_one
  have priorValBound :
      (ConcreteDiagram.DenseErasure.eraseNodeIndex step.prior
        step.priorApplication prior (by
          simp [ConcreteDiagram.DenseErasure.retainedNodes,
            ConcreteDiagram.nodesList, Data.Finite.mem_allFin,
            different])).val < step.base.val.nodeCount := by
    omega
  simp only [step.checkedPriorNode_val,
    step.checkedIdentityNode_val] at values
  omega

/-- Copied fragment nodes cannot collide with transported prior nodes. -/
theorem checkedFragmentNode_ne_checkedPriorNode
    (step : RelationJoinStep source dying content)
    (fragment : content.val.diagram.NodeId)
    (prior : step.prior.val.NodeId)
    (different : prior ≠ step.priorApplication) :
    step.checkedFragmentNode fragment ≠
      step.checkedPriorNode prior different := by
  intro same
  have values := congrArg Fin.val same
  have priorBound :=
    (ConcreteDiagram.DenseErasure.eraseNodeIndex
      step.prior step.priorApplication prior (by
        simp [ConcreteDiagram.DenseErasure.retainedNodes,
          ConcreteDiagram.nodesList, Data.Finite.mem_allFin,
          different])).isLt
  have erasedCount :
      (ConcreteDiagram.DenseErasure.eraseNodeCandidate
        step.prior step.priorApplication).nodeCount + 1 =
        step.prior.val.nodeCount :=
    Data.Finite.filter_not_mem_length_add_removed_length
      [step.priorApplication] (by simp)
  have baseCount := step.base_nodeCount_add_one
  have priorValBound :
      (ConcreteDiagram.DenseErasure.eraseNodeIndex step.prior
        step.priorApplication prior (by
          simp [ConcreteDiagram.DenseErasure.retainedNodes,
            ConcreteDiagram.nodesList, Data.Finite.mem_allFin,
            different])).val < step.base.val.nodeCount := by
    omega
  simp only [step.checkedFragmentNode_val,
    step.checkedPriorNode_val] at values
  omega

/-- A generated request node is carried by the occurrence's checked source
region image. -/
theorem checkedIdentityNode_data_at_sourceRegion
    (step : RelationJoinStep source dying content)
    (request : Fin step.attachment.identityRequests.length) :
    step.checked.val.nodes (step.checkedIdentityNode request) =
      .identity (step.checkedRegionImage step.sourceRegion)
        (step.attachment.identityRequests.get request).sig
        (step.attachment.identityRequests.get request).attachments.length := by
  rw [step.checkedIdentityNode_data, step.checkedRegionImageExact,
    ← step.siteExact]
  unfold Internal.checkedRegion
  rfl

end RelationJoinStep

theorem RelationJoinSemanticTrace.finalDyingScope_raw
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId}
    {finalScope : final.val.RegionId}
    (trace : RelationJoinSemanticTrace source dying content parameters args
      steps final finalRegionImage finalNodeImage finalWireImage finalDying
        finalScope) :
    (final.val.wires finalDying).scope = finalScope := by
  induction trace with
  | nil => rfl
  | snoc trace step priorExact priorRegionImageExact priorNodeImageExact
      priorWireImageExact priorDyingExact priorScopeExact relationArgsExact
      sourceParametersExact induction =>
      exact step.checked_dying_scope

namespace RelationJoinResult

theorem semantic_trace
    (result : RelationJoinResult source wire content parameters) :
    RelationJoinSemanticTrace source wire content parameters result.args
      result.steps result.boundFinal result.boundRegionImage
        result.boundNodeImage result.boundWireImage result.boundDying
        (result.boundRegionImage (source.val.wires wire).scope) :=
  result.construction_trace.semanticTrace

@[simp] theorem bound_dying_scope
    (result : RelationJoinResult source wire content parameters) :
    (result.boundFinal.val.wires result.boundDying).scope =
      result.boundRegionImage (source.val.wires wire).scope :=
  result.semantic_trace.finalDyingScope_raw

theorem boundNodeImage_eq_none_iff
    (result : RelationJoinResult source wire content parameters)
    (sourceNode : source.val.NodeId) :
    result.boundNodeImage sourceNode = none ↔
      sourceNode ∈ result.applications := by
  change result.constructionAtlas.nodeImage sourceNode = none ↔ _
  rw [CertifiedAtlas.nodeImage_eq_none_iff]
  rw [result.steps_application_order]

theorem trace_complete
    (result : RelationJoinResult source wire content parameters) :
    ∃ steps : List (RelationJoinStep source wire content),
      RelationJoinSemanticTrace source wire content parameters result.args
          steps result.boundFinal result.boundRegionImage
            result.boundNodeImage result.boundWireImage
            result.boundDying
            (result.boundRegionImage (source.val.wires wire).scope) ∧
        steps.map RelationJoinStep.application = result.applications := by
  exact ⟨result.steps, result.semantic_trace, result.steps_application_order⟩

/-- The exact origin type for terminal raw regions. -/
abbrev FinalRegionOrigin
    (result : RelationJoinResult source wire content parameters) : Type :=
  PrefixRegionOrigin (source := source) (dying := wire)
    (content := content) result.steps

/-- The exact live-origin type for terminal raw nodes. -/
abbrev FinalNodeOrigin
    (result : RelationJoinResult source wire content parameters) : Type :=
  { origin : PrefixNodeOrigin (source := source) (dying := wire)
      (content := content) result.steps // PrefixNodeLive origin }

/-- Terminal raw regions are exactly the certified construction rows.  The
forward direction is a direct terminal cast followed by row lookup; the
inverse is the atlas-owned constructive locator followed by the inverse cast. -/
def finalRegionOriginEquiv
    (result : RelationJoinResult source wire content parameters) :
    Data.Finite.FiniteEquiv result.plainFinal.val.RegionId
      (FinalRegionOrigin result) where
  toFun target :=
    result.constructionAtlas.rows.regionAt
      (Fin.cast result.plainFinal_regionCount target)
  invFun origin :=
    Fin.cast result.plainFinal_regionCount.symm
      (result.constructionAtlas.locateRegion origin).1
  left_inv target := by
    let boundTarget : result.boundFinal.val.RegionId :=
      Fin.cast result.plainFinal_regionCount target
    let landing := result.constructionAtlas.locateRegion
      (result.constructionAtlas.rows.regionAt boundTarget)
    have targetExact : landing.1 = boundTarget :=
      result.constructionAtlas.rows.regionAt_injective
        result.constructionAtlas.regionNodup landing.2.exact
    apply Fin.ext
    simpa [boundTarget, landing] using congrArg Fin.val targetExact
  right_inv origin := by
    let landing := result.constructionAtlas.locateRegion origin
    change result.constructionAtlas.rows.regionAt
        (Fin.cast result.plainFinal_regionCount
          (Fin.cast result.plainFinal_regionCount.symm landing.1)) = origin
    have targetExact :
        Fin.cast result.plainFinal_regionCount
            (Fin.cast result.plainFinal_regionCount.symm landing.1) =
          landing.1 := by
      apply Fin.ext
      rfl
    rw [targetExact]
    exact landing.2.exact

/-- Terminal raw nodes are exactly the live certified construction rows. -/
def finalNodeOriginEquiv
    (result : RelationJoinResult source wire content parameters) :
    Data.Finite.FiniteEquiv result.plainFinal.val.NodeId
      (FinalNodeOrigin result) where
  toFun target :=
    let boundTarget : result.boundFinal.val.NodeId :=
      Fin.cast result.plainFinal_nodeCount target
    ⟨result.constructionAtlas.rows.nodeAt boundTarget,
      result.constructionAtlas.nodeRowsLive boundTarget⟩
  invFun origin :=
    Fin.cast result.plainFinal_nodeCount.symm
      (result.constructionAtlas.locateNode origin.1 origin.2).1
  left_inv target := by
    let boundTarget : result.boundFinal.val.NodeId :=
      Fin.cast result.plainFinal_nodeCount target
    let landing := result.constructionAtlas.locateNode
      (result.constructionAtlas.rows.nodeAt boundTarget)
      (result.constructionAtlas.nodeRowsLive boundTarget)
    have targetExact : landing.1 = boundTarget :=
      result.constructionAtlas.rows.nodeAt_injective
        result.constructionAtlas.nodeNodup landing.2.exact
    apply Fin.ext
    simpa [boundTarget, landing] using congrArg Fin.val targetExact
  right_inv origin := by
    let landing := result.constructionAtlas.locateNode origin.1 origin.2
    apply Subtype.ext
    change result.constructionAtlas.rows.nodeAt
        (Fin.cast result.plainFinal_nodeCount
          (Fin.cast result.plainFinal_nodeCount.symm landing.1)) = origin.1
    have targetExact :
        Fin.cast result.plainFinal_nodeCount
            (Fin.cast result.plainFinal_nodeCount.symm landing.1) =
          landing.1 := by
      apply Fin.ext
      rfl
    rw [targetExact]
    exact landing.2.exact

end RelationJoinResult

namespace RelationJoinStep

/-- The copied content root is the checked image of the occurrence's source
site.  This is the root-identification half of the splice's region map. -/
theorem checkedFragmentRegion_root_eq_checkedRegionImage
    (step : RelationJoinStep source dying content) :
    step.checkedFragmentRegion content.val.diagram.root =
      step.checkedRegionImage step.sourceRegion := by
  apply Fin.ext
  simp [checkedFragmentRegion, ConcreteSpliceAttachment.fragmentRegion,
    step.checkedRegionImageExact, step.baseRegionImageExact,
    step.siteExact, Internal.checkedRegion]

theorem checkedFragmentRegion_injective_of_nonroot
    (step : RelationJoinStep source dying content)
    {left right : content.val.diagram.RegionId}
    (leftNonroot : left ≠ content.val.diagram.root)
    (rightNonroot : right ≠ content.val.diagram.root)
    (same : step.checkedFragmentRegion left =
      step.checkedFragmentRegion right) :
    left = right := by
  have values := congrArg Fin.val same
  have indices :
      DenseList.index step.attachment.fragmentRegions left (by
        simp [ConcreteSpliceAttachment.fragmentRegions,
          ConcreteDiagram.regionsList, Data.Finite.mem_allFin,
          leftNonroot]) =
        DenseList.index step.attachment.fragmentRegions right (by
          simp [ConcreteSpliceAttachment.fragmentRegions,
            ConcreteDiagram.regionsList, Data.Finite.mem_allFin,
            rightNonroot]) := by
    apply Fin.ext
    simpa [checkedFragmentRegion,
      ConcreteSpliceAttachment.fragmentRegion, leftNonroot, rightNonroot,
      ConcreteSpliceAttachment.freshRegion] using values
  have mapped := congrArg step.attachment.fragmentRegions.get indices
  rw [DenseList.get_index, DenseList.get_index] at mapped
  exact mapped

end RelationJoinStep

/-- Every snoc step preserves the source root's dense position. -/
theorem RelationJoinSemanticTrace.root_val
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId}
    {finalScope : final.val.RegionId}
    (trace :
      RelationJoinSemanticTrace source dying content parameters args steps
        final finalRegionImage finalNodeImage finalWireImage finalDying
          finalScope) :
    final.val.root.val = source.val.root.val := by
  induction trace with
  | nil => rfl
  | snoc trace step priorExact priorRegionImageExact priorNodeImageExact
      priorWireImageExact priorDyingExact priorScopeExact relationArgsExact
      sourceParametersExact induction =>
      subst priorExact
      exact step.checked_root_val.trans induction

/-- Source region rows are preserved exactly through every trace snoc. -/
theorem RelationJoinSemanticTrace.sourceRegion_data
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId}
    {finalScope : final.val.RegionId}
    (trace :
      RelationJoinSemanticTrace source dying content parameters args steps
        final finalRegionImage finalNodeImage finalWireImage finalDying
          finalScope)
    (region : source.val.RegionId) :
    final.val.regions (finalRegionImage region) =
      match source.val.regions region with
      | .sheet => .sheet
      | .cut parent => .cut (finalRegionImage parent) := by
  induction trace with
  | nil =>
      cases data : source.val.regions region <;> simp [data]
  | snoc trace step priorExact priorRegionImageExact priorNodeImageExact
      priorWireImageExact priorDyingExact priorScopeExact relationArgsExact
      sourceParametersExact induction =>
      subst priorExact
      cases eq_of_heq priorRegionImageExact
      cases eq_of_heq priorNodeImageExact
      cases eq_of_heq priorWireImageExact
      cases eq_of_heq priorDyingExact
      cases eq_of_heq priorScopeExact
      cases relationArgsExact
      cases sourceParametersExact
      rw [step.checkedRegionImage_eq_checkedPriorRegion]
      cases data : source.val.regions region with
      | sheet =>
          simp only [data]
          apply step.checkedPriorRegion_sheet
          simpa [data] using induction
      | cut parent =>
          simp only [data]
          rw [step.checkedRegionImage_eq_checkedPriorRegion parent]
          apply step.checkedPriorRegion_cut
          simpa [data] using induction

/-- Every surviving source node keeps its constructor and intrinsic payload;
only its source-region carrier follows the trace region image. -/
theorem RelationJoinSemanticTrace.sourceNode_data
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    {args : List Sig}
    {steps : List (RelationJoinStep source dying content)}
    {final : CheckedDiagram definitions}
    {finalRegionImage : source.val.RegionId → final.val.RegionId}
    {finalNodeImage : source.val.NodeId → Option final.val.NodeId}
    {finalWireImage : source.val.WireId → final.val.WireId}
    {finalDying : final.val.WireId}
    {finalScope : final.val.RegionId}
    (trace :
      RelationJoinSemanticTrace source dying content parameters args steps
        final finalRegionImage finalNodeImage finalWireImage finalDying
          finalScope)
    (sourceNode : source.val.NodeId)
    (finalNode : final.val.NodeId)
    (imageExact : finalNodeImage sourceNode = some finalNode) :
    final.val.nodes finalNode =
      (source.val.nodes sourceNode).relocate
        (finalRegionImage (source.val.nodes sourceNode).region) := by
  induction trace with
  | nil =>
      have nodeExact : sourceNode = finalNode := Option.some.inj imageExact
      subst finalNode
      cases data : source.val.nodes sourceNode <;>
        simp [CNode.relocate, CNode.region, data]
  | snoc trace step priorExact priorRegionImageExact priorNodeImageExact
      priorWireImageExact priorDyingExact priorScopeExact relationArgsExact
      sourceParametersExact induction =>
      subst priorExact
      cases eq_of_heq priorRegionImageExact
      cases eq_of_heq priorNodeImageExact
      cases eq_of_heq priorWireImageExact
      cases eq_of_heq priorDyingExact
      cases eq_of_heq priorScopeExact
      cases relationArgsExact
      cases sourceParametersExact
      cases priorImageExact : step.priorNodeImage sourceNode with
      | none =>
          rw [step.checkedNodeImageExact, step.baseNodeImageExact,
            priorImageExact] at imageExact
          contradiction
      | some priorNode =>
          have different : priorNode ≠ step.priorApplication := by
            intro same
            subst priorNode
            have sourceExact : sourceNode = step.application :=
              step.priorNodeImage_injective priorImageExact
                step.priorApplicationImage
            subst sourceNode
            rw [step.checkedNodeImage_application] at imageExact
            contradiction
          rw [step.checkedNodeImage_of_prior priorImageExact different]
            at imageExact
          have finalExact :
              finalNode = step.checkedPriorNode priorNode different :=
            (Option.some.inj imageExact).symm
          subst finalNode
          rw [step.checkedPriorNode_data]
          rw [induction priorNode priorImageExact]
          rw [step.checkedRegionImage_eq_checkedPriorRegion]
          cases data : source.val.nodes sourceNode <;>
            simp [CNode.relocate, CNode.region, data]

namespace RelationJoinResult

variable {definitions : List (List Sig)} {source : CheckedDiagram definitions}
variable {wire : source.val.WireId}
variable {content : CheckedOpenDiagram definitions}
variable {parameters : List source.val.WireId}

theorem boundRegionImage_data
    (result : RelationJoinResult source wire content parameters)
    (region : source.val.RegionId) :
    result.boundFinal.val.regions (result.boundRegionImage region) =
      match source.val.regions region with
      | .sheet => .sheet
      | .cut parent => .cut (result.boundRegionImage parent) :=
  (result.semantic_trace).sourceRegion_data region

@[simp] theorem boundFinal_root_val
    (result : RelationJoinResult source wire content parameters) :
    result.boundFinal.val.root.val = source.val.root.val :=
  result.semantic_trace.root_val

@[simp] theorem plainFinal_root_val
    (result : RelationJoinResult source wire content parameters) :
    result.plainFinal.val.root.val = source.val.root.val := by
  exact result.plainFinal_root_val_of_bound.trans result.boundFinal_root_val

theorem plainFinal_root_eq_source_image
    (result : RelationJoinResult source wire content parameters) :
    result.plainFinal.val.root =
      result.plainBoundRegionImage
        (result.boundRegionImage source.val.root) := by
  apply Fin.ext
  simp

theorem plainSourceRegionImage_data
    (result : RelationJoinResult source wire content parameters)
    (region : source.val.RegionId) :
    result.plainFinal.val.regions
        (result.plainBoundRegionImage
          (result.boundRegionImage region)) =
      match source.val.regions region with
      | .sheet => .sheet
      | .cut parent =>
          .cut
            (result.plainBoundRegionImage
              (result.boundRegionImage parent)) := by
  cases data : source.val.regions region with
  | sheet =>
      apply result.plainBoundRegionImage_sheet
      simpa [data] using result.boundRegionImage_data region
  | cut parent =>
      apply result.plainBoundRegionImage_cut
      simpa [data] using result.boundRegionImage_data region

/-- Final wire deletion preserves the dense node position. -/
theorem plainBoundNodeImage_eq_cast
    (result : RelationJoinResult source wire content parameters)
    (node : result.boundFinal.val.NodeId) :
    result.plainBoundNodeImage node =
      Fin.cast result.plainFinal_nodeCount.symm node := by
  apply Fin.ext
  simpa using result.plainBoundNodeImage_val node

end RelationJoinResult

end ConcreteWireQuantifier

end VisualProof
