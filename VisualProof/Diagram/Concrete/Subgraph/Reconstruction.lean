import VisualProof.Diagram.Concrete.Subgraph.SpliceRaw

namespace VisualProof

namespace Reconstruction

@[simp] theorem complement_regionCount
    (removed : RemovalResult occurrence) :
    removed.complement.val.regionCount =
      (Removal.regions occurrence).length :=
  rfl

@[simp] theorem complement_nodeCount
    (removed : RemovalResult occurrence) :
    removed.complement.val.nodeCount =
      (Removal.nodes occurrence).length :=
  rfl

@[simp] theorem complement_wireCount
    (removed : RemovalResult occurrence) :
    removed.complement.val.wireCount =
      (Removal.wires occurrence).length :=
  rfl

/-- The host wire named by one authoritative ordered boundary position. -/
def boundaryHostWire
    (occurrence : Occurrence pattern host)
    (position : Fin pattern.val.boundary.length) :
    host.val.WireId :=
  occurrence.wireMap (pattern.val.boundary.get position)

/--
Acceptance of the exact reconstruction attachment certifies that every ordered
boundary position names a retained complement wire.
-/
theorem boundaryHostWire_retained
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (accepted :
      reconstructionAttachment? occurrence removed =
        some attachment)
    (position : Fin pattern.val.boundary.length) :
    boundaryHostWire occurrence position ∈ Removal.wires occurrence := by
  unfold reconstructionAttachment? at accepted
  dsimp only at accepted
  split at accepted
  · rename_i retained
    simpa [boundaryHostWire, Occurrence.boundaryAttachments] using
      retained
        ⟨position.val, by
          simpa using position.isLt⟩
  · contradiction

/-- Exact reconstruction targets the retained image of each boundary position. -/
theorem attachment_target
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (accepted :
      reconstructionAttachment? occurrence removed =
        some attachment)
    (position : Fin pattern.val.boundary.length) :
    attachment.target position =
      Removal.wireIndex occurrence
        (boundaryHostWire occurrence position)
        (boundaryHostWire_retained occurrence removed
          attachment accepted position) := by
  unfold reconstructionAttachment? at accepted
  dsimp only at accepted
  split at accepted
  · rename_i retained
    have targetEquality :=
      checkConcreteSpliceAttachment_target
        removed.complement removed.site pattern _ attachment accepted
    simpa [boundaryHostWire, Occurrence.boundaryAttachments] using
      congrFun targetEquality position
  · contradiction

/--
All repeated positions of one boundary class reconstruct to one target. Hence
raw reconstruction introduces no attachment identities.
-/
theorem attachment_representative_eq_target
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (accepted :
      reconstructionAttachment? occurrence removed =
        some attachment)
    (position : Fin pattern.val.boundary.length) :
    attachment.representativeTarget
        (pattern.val.boundary.get position)
        (List.get_mem pattern.val.boundary position) =
      attachment.target position := by
  let representative :=
    attachment.representativePosition
      (pattern.val.boundary.get position)
      (List.get_mem pattern.val.boundary position)
  have sameBoundary :
      pattern.val.boundary.get representative =
        pattern.val.boundary.get position :=
    DenseList.get_index _ _ _
  change attachment.target representative = attachment.target position
  rw [attachment_target occurrence removed attachment accepted,
    attachment_target occurrence removed attachment accepted]
  apply Fin.ext
  simp only [boundaryHostWire, sameBoundary]

private theorem attachment_target_eq_of_same_source
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (accepted :
      reconstructionAttachment? occurrence removed =
        some attachment)
    (left right : Fin pattern.val.boundary.length)
    (same :
      pattern.val.boundary.get left =
        pattern.val.boundary.get right) :
    attachment.target left = attachment.target right := by
  rw [attachment_target occurrence removed attachment accepted,
    attachment_target occurrence removed attachment accepted]
  apply Fin.ext
  simp only [boundaryHostWire, same]

theorem identityRequests_eq_nil
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (accepted :
      reconstructionAttachment? occurrence removed =
        some attachment) :
    attachment.identityRequests = [] := by
  rw [attachment.identityRequests_exact]
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro request member
  unfold computedIdentityRequests at member
  rw [List.mem_eraseDups, List.mem_filterMap] at member
  rcases member with ⟨source, _, emitted⟩
  let targets :=
    concreteAttachmentTargets removed.complement pattern
      attachment.target source
  have targetsSubsingleton :
      ∀ left ∈ targets, ∀ right ∈ targets, left = right := by
    intro left leftMember right rightMember
    change left ∈
      concreteAttachmentTargets removed.complement pattern
        attachment.target source at leftMember
    change right ∈
      concreteAttachmentTargets removed.complement pattern
        attachment.target source at rightMember
    unfold concreteAttachmentTargets at leftMember rightMember
    rw [List.mem_eraseDups, List.mem_filterMap] at leftMember rightMember
    rcases leftMember with ⟨leftPosition, _, leftEmission⟩
    rcases rightMember with ⟨rightPosition, _, rightEmission⟩
    split at leftEmission
    · rename_i leftSource
      split at rightEmission
      · rename_i rightSource
        have leftTarget : attachment.target leftPosition = left :=
          Option.some.inj leftEmission
        have rightTarget : attachment.target rightPosition = right :=
          Option.some.inj rightEmission
        rw [← leftTarget, ← rightTarget]
        apply attachment_target_eq_of_same_source occurrence
          removed attachment accepted
        exact leftSource.trans rightSource.symm
      · contradiction
    · contradiction
  have targetsNodup : targets.Nodup := by
    unfold targets concreteAttachmentTargets
    exact Data.Finite.eraseDups_nodup _
  have targetsLength : targets.length ≤ 1 := by
    cases targetsEq : targets with
    | nil => simp
    | cons head tail =>
        cases tailEq : tail with
        | nil => simp
        | cons next rest =>
            rw [targetsEq, tailEq] at targetsNodup targetsSubsingleton
            have different : head ≠ next := by
              rw [List.nodup_cons] at targetsNodup
              exact fun same =>
                targetsNodup.1
                  (by
                    rw [same]
                    exact List.mem_cons_self)
            exact False.elim
              (different
                (targetsSubsingleton head List.mem_cons_self next
                  (List.mem_cons_of_mem _ List.mem_cons_self)))
  change
    (if 2 ≤ targets.length then
      some { source := source, attachments := targets }
    else none) = some request at emitted
  split at emitted
  · rename_i atLeastTwo
    omega
  · contradiction

private def RegionsExact
    (occurrence : Occurrence pattern host) : Prop :=
  ∀ region,
    region ∈ occurrence.toSelection.allRegions ↔
      ∃ source,
        source ≠ pattern.val.diagram.root ∧
          occurrence.regionMap source = region

private def NodesExact
    (occurrence : Occurrence pattern host) : Prop :=
  ∀ node,
    node ∈ occurrence.toSelection.allNodes ↔
      ∃ source, occurrence.nodeMap source = node

private def WiresExact
    (occurrence : Occurrence pattern host) : Prop :=
  ∀ wire,
    wire ∈ occurrence.toSelection.internalWires ↔
      ∃ source,
        source ∉ pattern.val.boundary ∧
          occurrence.wireMap source = wire

private theorem retainedRegion_of_not_selected
    (occurrence : Occurrence pattern host)
    {region : host.val.RegionId}
    (outside : region ∉ occurrence.toSelection.allRegions) :
    region ∈ Removal.regions occurrence := by
  have outsideSelected :
      ¬ occurrence.toSelection.IsSelectedRegion region := by
    intro selected
    apply outside
    rw [CheckedSelection.mem_allRegions]
    exact selected
  apply List.mem_filter.mpr
  refine ⟨Data.Finite.mem_allFin _, decide_eq_true (.inr (.inr ?_))⟩
  change region ∉ occurrence.toSelection.allRegions
  exact outside

private theorem retainedNode_of_not_selected
    (occurrence : Occurrence pattern host)
    {node : host.val.NodeId}
    (outside : node ∉ occurrence.toSelection.allNodes) :
    node ∈ Removal.nodes occurrence := by
  have outsideSelected :
      ¬ occurrence.toSelection.IsSelectedNode node := by
    intro selected
    apply outside
    rw [CheckedSelection.mem_allNodes]
    exact selected
  apply List.mem_filter.mpr
  refine ⟨Data.Finite.mem_allFin _, decide_eq_true ?_⟩
  change node ∉ occurrence.toSelection.allNodes
  exact outside

private theorem retainedWire_of_not_internal
    (occurrence : Occurrence pattern host)
    {wire : host.val.WireId}
    (outside : wire ∉ occurrence.toSelection.internalWires) :
    wire ∈ Removal.wires occurrence := by
  have outsideInternal :
      ¬ occurrence.toSelection.IsInternal wire := by
    intro internal
    apply outside
    rw [CheckedSelection.mem_internalWires]
    exact internal
  apply List.mem_filter.mpr
  refine ⟨Data.Finite.mem_allFin _, decide_eq_true ?_⟩
  change wire ∉ occurrence.toSelection.internalWires
  exact outside

private def regionForward
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (region : attachment.diagram.RegionId) :
    host.val.RegionId :=
  Fin.addCases
    (Removal.sourceRegion occurrence)
    (fun fresh =>
      occurrence.regionMap (attachment.fragmentRegions.get fresh))
    region

private noncomputable def regionBackward
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (exact : RegionsExact occurrence)
    (region : host.val.RegionId) :
    attachment.diagram.RegionId :=
  if selected : region ∈ occurrence.toSelection.allRegions then
    let source := Classical.choose ((exact region).mp selected)
    let sourceData := Classical.choose_spec ((exact region).mp selected)
    attachment.freshRegion
      (DenseList.index attachment.fragmentRegions source (by
        change source ∈
          pattern.val.diagram.regionsList.filter fun region =>
            decide (region ≠ pattern.val.diagram.root)
        apply List.mem_filter.mpr
        refine ⟨Data.Finite.mem_allFin _, decide_eq_true ?_⟩
        exact sourceData.1))
  else
    attachment.hostRegion
      (Removal.regionIndex occurrence region
        (retainedRegion_of_not_selected occurrence selected))

private noncomputable def regionClassicalEquiv
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (exact : RegionsExact occurrence) :
    Data.Finite.FiniteEquiv
      attachment.diagram.RegionId host.val.RegionId where
  toFun := regionForward occurrence removed attachment
  invFun :=
    regionBackward occurrence removed attachment exact
  left_inv := by
    intro allocated
    refine Fin.addCases ?_ ?_ allocated
    · intro retained
      have outsideOrAnchor :=
        of_decide_eq_true
          (List.mem_filter.mp
            (List.get_mem (Removal.regions occurrence) retained)).2
      have outsideOrAnchor :
          Removal.sourceRegion occurrence retained = host.val.root ∨
          Removal.sourceRegion occurrence retained =
              occurrence.toSelection.region ∨
            Removal.sourceRegion occurrence retained ∉
              occurrence.toSelection.allRegions := by
        rcases outsideOrAnchor with root | anchor | outside
        · exact .inl root
        · exact .inr (.inl anchor)
        · exact .inr (.inr (by
            change Removal.sourceRegion occurrence retained ∉
              occurrence.toSelection.allRegions
            exact outside))
      have outside :
          Removal.sourceRegion occurrence retained ∉
            occurrence.toSelection.allRegions := by
        intro selected
        rcases outsideOrAnchor with root | anchor | outside
        · rcases (exact _).mp selected with
            ⟨source, sourceNonroot, sourceMap⟩
          have onlyRoot :=
            of_decide_eq_true
              (List.all_eq_true.mp
                pattern.property.diagram.only_root_is_sheet
                source (Data.Finite.mem_allFin source))
          cases sourceRegion : pattern.val.diagram.regions source with
          | sheet => exact sourceNonroot (onlyRoot sourceRegion)
          | cut parent =>
              have mapped :=
                occurrence.maps_parentage source parent sourceRegion
              rw [sourceMap, root, host.property.root_is_sheet] at mapped
              contradiction
        · rcases (exact _).mp selected with
            ⟨source, sourceNonroot, sourceMap⟩
          have same :
              occurrence.regionMap source =
                occurrence.regionMap pattern.val.diagram.root := by
            rw [sourceMap, anchor, occurrence.toSelection_region,
              occurrence.maps_root]
          exact sourceNonroot (occurrence.regionMap_injective same)
        · exact outside selected
      simp [regionBackward, regionForward, outside,
        Removal.regionIndex_sourceRegion,
        ConcreteSpliceAttachment.hostRegion]
    · intro fresh
      let source := attachment.fragmentRegions.get fresh
      have sourceMember : source ∈ attachment.fragmentRegions :=
        List.get_mem _ fresh
      have nonroot : source ≠ pattern.val.diagram.root := by
        simpa [ConcreteSpliceAttachment.fragmentRegions,
          ConcreteDiagram.regionsList, Data.Finite.mem_allFin] using
            (List.mem_filter.mp sourceMember).2
      have selected :
          occurrence.regionMap source ∈
            occurrence.toSelection.allRegions :=
        (exact _).mpr ⟨source, nonroot, rfl⟩
      simp only [regionForward, Fin.addCases_right]
      unfold regionBackward
      rw [dif_pos selected]
      dsimp only
      let chosen :=
        Classical.choose ((exact (occurrence.regionMap source)).mp selected)
      have chosenData :=
        Classical.choose_spec
          ((exact (occurrence.regionMap source)).mp selected)
      have chosenEq : chosen = source := by
        apply occurrence.regionMap_injective
        exact chosenData.2
      have chosenMember : chosen ∈ attachment.fragmentRegions := by
        simpa only [chosenEq] using sourceMember
      have indexEquality :
          DenseList.index attachment.fragmentRegions chosen chosenMember =
            fresh := by
        calc
          DenseList.index attachment.fragmentRegions chosen chosenMember =
              DenseList.index attachment.fragmentRegions source
                sourceMember := by
            unfold DenseList.index
            simp only [chosenEq]
          _ = fresh :=
            DenseList.index_get attachment.fragmentRegions
              ((Data.Finite.allFin_nodup
                pattern.val.diagram.regionCount).filter _) fresh
      apply Fin.ext
      simp only [ConcreteSpliceAttachment.freshRegion, Fin.natAdd]
      change
        removed.complement.val.regionCount +
            (DenseList.index attachment.fragmentRegions chosen _).val =
          removed.complement.val.regionCount + fresh.val
      rw [indexEquality]
  right_inv := by
    intro region
    by_cases selected :
        region ∈ occurrence.toSelection.allRegions
    · let source := Classical.choose ((exact region).mp selected)
      have sourceData := Classical.choose_spec ((exact region).mp selected)
      simp only [regionBackward, dif_pos selected, regionForward,
        ConcreteSpliceAttachment.freshRegion, Fin.addCases_right]
      rw [DenseList.get_index]
      exact sourceData.2
    · simp [regionBackward, selected, regionForward,
        ConcreteSpliceAttachment.hostRegion,
        Removal.sourceRegion_regionIndex]

private theorem regionForward_bijective
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (exact : RegionsExact occurrence) :
    Function.Injective (regionForward occurrence removed attachment) ∧
      ∀ target, ∃ source,
        regionForward occurrence removed attachment source = target := by
  let equivalence :=
    regionClassicalEquiv occurrence removed attachment exact
  exact ⟨equivalence.injective,
    fun target => ⟨equivalence.symm target, equivalence.right_inv target⟩⟩

/-- Construction-owned finite region correspondence for exact reconstruction. -/
def regionEquiv
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (exact : RegionsExact occurrence) :
    Data.Finite.FiniteEquiv
      attachment.diagram.RegionId host.val.RegionId :=
  Data.Finite.FiniteEquiv.ofBijectiveFin
    (regionForward occurrence removed attachment)
    (regionForward_bijective occurrence removed attachment exact)

private def eliminateIdentityRequest
    {occurrence : Occurrence pattern host}
    {removed : RemovalResult occurrence}
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (empty : attachment.identityRequests = [])
    (identity : Fin attachment.identityRequests.length) :
    α :=
  Fin.elim0
    (Fin.cast (by
      have lengths := congrArg List.length empty
      simpa using lengths) identity)

private def nodeForward
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (empty : attachment.identityRequests = [])
    (node : attachment.diagram.NodeId) :
    host.val.NodeId :=
  Fin.addCases
    (Removal.sourceNode occurrence)
    (Fin.addCases occurrence.nodeMap
      (eliminateIdentityRequest attachment empty))
    node

private noncomputable def nodeBackward
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (exact : NodesExact occurrence)
    (node : host.val.NodeId) :
    attachment.diagram.NodeId :=
  if selected : node ∈ occurrence.toSelection.allNodes then
    attachment.fragmentNode
      (Classical.choose ((exact node).mp selected))
  else
    attachment.hostNode
      (Removal.nodeIndex occurrence node
        (retainedNode_of_not_selected occurrence selected))

private noncomputable def nodeClassicalEquiv
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (empty : attachment.identityRequests = [])
    (exact : NodesExact occurrence) :
    Data.Finite.FiniteEquiv
      attachment.diagram.NodeId host.val.NodeId where
  toFun := nodeForward occurrence removed attachment empty
  invFun := nodeBackward occurrence removed attachment exact
  left_inv := by
    intro allocated
    refine Fin.addCases ?_ ?_ allocated
    · intro retained
      have outside :
          Removal.sourceNode occurrence retained ∉
            occurrence.toSelection.allNodes := by
        exact of_decide_eq_true
          (List.mem_filter.mp
            (List.get_mem (Removal.nodes occurrence) retained)).2
      simp [nodeForward, nodeBackward, outside,
        ConcreteSpliceAttachment.hostNode,
        Removal.nodeIndex_sourceNode]
    · intro inserted
      refine Fin.addCases ?_ ?_ inserted
      · intro source
        have selected :
            occurrence.nodeMap source ∈ occurrence.toSelection.allNodes :=
          (exact _).mpr ⟨source, rfl⟩
        simp only [nodeForward, Fin.addCases_right, Fin.addCases_left]
        unfold nodeBackward
        rw [dif_pos selected]
        apply Fin.ext
        simp only [ConcreteSpliceAttachment.fragmentNode]
        have chosenData :=
          Classical.choose_spec ((exact (occurrence.nodeMap source)).mp selected)
        have chosenEq :
            Classical.choose ((exact (occurrence.nodeMap source)).mp selected) =
              source :=
          occurrence.nodeMap_injective chosenData
        change
          removed.complement.val.nodeCount +
              (Classical.choose
                ((exact (occurrence.nodeMap source)).mp selected)).val =
            removed.complement.val.nodeCount + source.val
        exact congrArg
          (fun value => removed.complement.val.nodeCount + value.val)
          chosenEq
      · intro identity
        exact eliminateIdentityRequest attachment empty identity
  right_inv := by
    intro node
    by_cases selected : node ∈ occurrence.toSelection.allNodes
    · unfold nodeBackward
      rw [dif_pos selected]
      let source := Classical.choose ((exact node).mp selected)
      have allocated :
          attachment.fragmentNode source =
            Fin.natAdd removed.complement.val.nodeCount
              (Fin.castAdd attachment.identityRequests.length source) :=
        Fin.ext (by simp [ConcreteSpliceAttachment.fragmentNode])
      change
        nodeForward occurrence removed attachment empty
            (attachment.fragmentNode source) =
          node
      rw [allocated]
      unfold nodeForward
      calc
        Fin.addCases (Removal.sourceNode occurrence)
              (Fin.addCases occurrence.nodeMap
                (eliminateIdentityRequest attachment empty))
              (Fin.natAdd removed.complement.val.nodeCount
                (Fin.castAdd attachment.identityRequests.length source)) =
            Fin.addCases occurrence.nodeMap
              (eliminateIdentityRequest attachment empty)
              (Fin.castAdd attachment.identityRequests.length source) :=
          Fin.addCases_right _
        _ = occurrence.nodeMap source :=
          Fin.addCases_left source
        _ = node :=
          Classical.choose_spec ((exact node).mp selected)
    · simp [nodeBackward, selected, nodeForward,
        ConcreteSpliceAttachment.hostNode,
        Removal.sourceNode_nodeIndex]

private theorem nodeForward_bijective
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (empty : attachment.identityRequests = [])
    (exact : NodesExact occurrence) :
    Function.Injective
        (nodeForward occurrence removed attachment empty) ∧
      ∀ target, ∃ source,
        nodeForward occurrence removed attachment empty source = target := by
  let equivalence :=
    nodeClassicalEquiv occurrence removed attachment empty exact
  exact ⟨equivalence.injective,
    fun target => ⟨equivalence.symm target, equivalence.right_inv target⟩⟩

/-- Construction-owned finite node correspondence for exact reconstruction. -/
def nodeEquiv
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (empty : attachment.identityRequests = [])
    (exact : NodesExact occurrence) :
    Data.Finite.FiniteEquiv
      attachment.diagram.NodeId host.val.NodeId :=
  Data.Finite.FiniteEquiv.ofBijectiveFin
    (nodeForward occurrence removed attachment empty)
    (nodeForward_bijective occurrence removed attachment empty exact)

/--
Port renaming owned by one allocated reconstruction node. Retained nodes keep
their concrete storage positions; copied identity nodes use the occurrence's
positional owner equivalence.
-/
private noncomputable def allocatedPortEquiv
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (empty : attachment.identityRequests = [])
    (node : attachment.diagram.NodeId) :
    Data.Finite.FiniteEquiv CPort CPort :=
  Fin.addCases
    (fun _ => Data.Finite.FiniteEquiv.refl _)
    (Fin.addCases
      (fun source => occurrence.portEquivForNode source)
      (eliminateIdentityRequest attachment empty))
    node

/-- Total splice-wide endpoint transport before restriction to wire fibers. -/
private noncomputable def endpointEquiv
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (empty : attachment.identityRequests = [])
    (nodesExact : NodesExact occurrence) :
    Data.Finite.FiniteEquiv
      (CEndpoint attachment.diagram.nodeCount)
      (CEndpoint host.val.nodeCount) where
  toFun := fun endpoint =>
    ⟨nodeEquiv occurrence removed attachment empty nodesExact endpoint.node,
      allocatedPortEquiv occurrence removed attachment empty endpoint.node
        endpoint.port⟩
  invFun := fun candidate =>
    let node :=
      (nodeEquiv occurrence removed attachment empty nodesExact).symm
        candidate.node
    ⟨node,
      (allocatedPortEquiv occurrence removed attachment empty node).symm
        candidate.port⟩
  left_inv := by
    rintro ⟨node, port⟩
    simp only [Data.Finite.FiniteEquiv.symm_apply_apply]
  right_inv := by
    rintro ⟨node, port⟩
    simp only [Data.Finite.FiniteEquiv.apply_symm_apply]

private def wireForward
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (wire : attachment.diagram.WireId) :
    host.val.WireId :=
  Fin.addCases
    (Removal.sourceWire occurrence)
    (fun fresh =>
      occurrence.wireMap
        (attachment.fragmentInternalWires.get fresh))
    wire

private noncomputable def wireBackward
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (exact : WiresExact occurrence)
    (wire : host.val.WireId) :
    attachment.diagram.WireId :=
  if internal : wire ∈ occurrence.toSelection.internalWires then
    let source := Classical.choose ((exact wire).mp internal)
    let sourceData := Classical.choose_spec ((exact wire).mp internal)
    attachment.freshWire
      (DenseList.index attachment.fragmentInternalWires source (by
        change source ∈
          pattern.val.diagram.wiresList.filter fun candidate =>
            decide (candidate ∉ pattern.val.boundary)
        apply List.mem_filter.mpr
        refine ⟨Data.Finite.mem_allFin _, decide_eq_true ?_⟩
        exact sourceData.1))
  else
    attachment.hostWire
      (Removal.wireIndex occurrence wire
        (retainedWire_of_not_internal occurrence internal))

private noncomputable def wireClassicalEquiv
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (exact : WiresExact occurrence) :
    Data.Finite.FiniteEquiv
      attachment.diagram.WireId host.val.WireId where
  toFun := wireForward occurrence removed attachment
  invFun := wireBackward occurrence removed attachment exact
  left_inv := by
    intro allocated
    refine Fin.addCases ?_ ?_ allocated
    · intro retained
      have outside :
          Removal.sourceWire occurrence retained ∉
            occurrence.toSelection.internalWires := by
        exact of_decide_eq_true
          (List.mem_filter.mp
            (List.get_mem (Removal.wires occurrence) retained)).2
      simp [wireForward, wireBackward, outside,
        ConcreteSpliceAttachment.hostWire,
        Removal.wireIndex_sourceWire]
    · intro fresh
      let source := attachment.fragmentInternalWires.get fresh
      have sourceMember : source ∈ attachment.fragmentInternalWires :=
        List.get_mem _ fresh
      have nonboundary : source ∉ pattern.val.boundary := by
        simpa [ConcreteSpliceAttachment.fragmentInternalWires,
          ConcreteDiagram.wiresList, Data.Finite.mem_allFin] using
            (List.mem_filter.mp sourceMember).2
      have internal :
          occurrence.wireMap source ∈
            occurrence.toSelection.internalWires :=
        (exact _).mpr ⟨source, nonboundary, rfl⟩
      simp only [wireForward, Fin.addCases_right]
      unfold wireBackward
      rw [dif_pos internal]
      dsimp only
      let chosen :=
        Classical.choose ((exact (occurrence.wireMap source)).mp internal)
      have chosenData :=
        Classical.choose_spec
          ((exact (occurrence.wireMap source)).mp internal)
      have chosenEq : chosen = source := by
        apply occurrence.internalWire_injective
        · exact chosenData.1
        · exact nonboundary
        · exact chosenData.2
      have chosenMember : chosen ∈ attachment.fragmentInternalWires := by
        simpa only [chosenEq] using sourceMember
      have indexEquality :
          DenseList.index attachment.fragmentInternalWires chosen
              chosenMember =
            fresh := by
        calc
          DenseList.index attachment.fragmentInternalWires chosen
                chosenMember =
              DenseList.index attachment.fragmentInternalWires source
                sourceMember := by
            unfold DenseList.index
            simp only [chosenEq]
          _ = fresh :=
            DenseList.index_get attachment.fragmentInternalWires
              ((Data.Finite.allFin_nodup
                pattern.val.diagram.wireCount).filter _) fresh
      apply Fin.ext
      simp only [ConcreteSpliceAttachment.freshWire, Fin.natAdd]
      change
        removed.complement.val.wireCount +
            (DenseList.index attachment.fragmentInternalWires chosen _).val =
          removed.complement.val.wireCount + fresh.val
      rw [indexEquality]
  right_inv := by
    intro wire
    by_cases internal :
        wire ∈ occurrence.toSelection.internalWires
    · let source := Classical.choose ((exact wire).mp internal)
      have sourceData := Classical.choose_spec ((exact wire).mp internal)
      unfold wireBackward
      rw [dif_pos internal]
      dsimp only
      simp only [wireForward, ConcreteSpliceAttachment.freshWire,
        Fin.addCases_right]
      rw [DenseList.get_index]
      exact sourceData.2
    · simp [wireBackward, internal, wireForward,
        ConcreteSpliceAttachment.hostWire,
        Removal.sourceWire_wireIndex]

private theorem wireForward_bijective
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (exact : WiresExact occurrence) :
    Function.Injective (wireForward occurrence removed attachment) ∧
      ∀ target, ∃ source,
        wireForward occurrence removed attachment source = target := by
  let equivalence :=
    wireClassicalEquiv occurrence removed attachment exact
  exact ⟨equivalence.injective,
    fun target => ⟨equivalence.symm target, equivalence.right_inv target⟩⟩

/-- Construction-owned finite wire correspondence for exact reconstruction. -/
def wireEquiv
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (exact : WiresExact occurrence) :
    Data.Finite.FiniteEquiv
      attachment.diagram.WireId host.val.WireId :=
  Data.Finite.FiniteEquiv.ofBijectiveFin
    (wireForward occurrence removed attachment)
    (wireForward_bijective occurrence removed attachment exact)

private theorem regionEquiv_hostRegion
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (exact : RegionsExact occurrence)
    (region : removed.complement.val.RegionId) :
    regionEquiv occurrence removed attachment exact
        (attachment.hostRegion region) =
      Removal.sourceRegion occurrence region := by
  change
    regionForward occurrence removed attachment
        (attachment.hostRegion region) =
      Removal.sourceRegion occurrence region
  unfold regionForward ConcreteSpliceAttachment.hostRegion
  exact Fin.addCases_left region

private theorem regionEquiv_freshRegion
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (exact : RegionsExact occurrence)
    (region : Fin attachment.fragmentRegions.length) :
    regionEquiv occurrence removed attachment exact
        (attachment.freshRegion region) =
      occurrence.regionMap (attachment.fragmentRegions.get region) := by
  change
    regionForward occurrence removed attachment
        (attachment.freshRegion region) =
      occurrence.regionMap (attachment.fragmentRegions.get region)
  unfold regionForward ConcreteSpliceAttachment.freshRegion
  exact Fin.addCases_right region

private theorem regionEquiv_fragmentRegion
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (exact : RegionsExact occurrence)
    (region : pattern.val.diagram.RegionId) :
    regionEquiv occurrence removed attachment exact
        (attachment.fragmentRegion region) =
      occurrence.regionMap region := by
  unfold ConcreteSpliceAttachment.fragmentRegion
  split
  · rename_i root
    subst region
    rw [regionEquiv_hostRegion occurrence removed attachment exact]
    calc
      Removal.sourceRegion occurrence removed.site =
          occurrence.toSelection.region := by
        unfold RemovalResult.site Removal.site
        rw [Removal.sourceRegion_regionIndex]
        rfl
      _ = occurrence.region := occurrence.toSelection_region
      _ = occurrence.regionMap pattern.val.diagram.root := by
        change occurrence.region =
          occurrence.regionMap pattern.val.diagram.root
        exact occurrence.maps_root.symm
  · rename_i nonroot
    rw [regionEquiv_freshRegion occurrence removed attachment exact]
    rw [DenseList.get_index]

private theorem nodeEquiv_hostNode
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (empty : attachment.identityRequests = [])
    (exact : NodesExact occurrence)
    (node : removed.complement.val.NodeId) :
    nodeEquiv occurrence removed attachment empty exact
        (attachment.hostNode node) =
      Removal.sourceNode occurrence node := by
  change
    nodeForward occurrence removed attachment empty
        (attachment.hostNode node) =
      Removal.sourceNode occurrence node
  unfold nodeForward ConcreteSpliceAttachment.hostNode
  exact Fin.addCases_left node

private theorem nodeEquiv_fragmentNode
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (empty : attachment.identityRequests = [])
    (exact : NodesExact occurrence)
    (node : pattern.val.diagram.NodeId) :
    nodeEquiv occurrence removed attachment empty exact
        (attachment.fragmentNode node) =
      occurrence.nodeMap node := by
  change
    nodeForward occurrence removed attachment empty
        (attachment.fragmentNode node) =
      occurrence.nodeMap node
  have allocated :
      attachment.fragmentNode node =
        Fin.natAdd removed.complement.val.nodeCount
          (Fin.castAdd attachment.identityRequests.length node) :=
    Fin.ext (by simp [ConcreteSpliceAttachment.fragmentNode])
  rw [allocated]
  unfold nodeForward
  calc
    Fin.addCases (Removal.sourceNode occurrence)
          (Fin.addCases occurrence.nodeMap
            (eliminateIdentityRequest attachment empty))
          (Fin.natAdd removed.complement.val.nodeCount
            (Fin.castAdd attachment.identityRequests.length node)) =
        Fin.addCases occurrence.nodeMap
          (eliminateIdentityRequest attachment empty)
          (Fin.castAdd attachment.identityRequests.length node) :=
      Fin.addCases_right _
    _ = occurrence.nodeMap node := Fin.addCases_left node

private theorem allocatedPortEquiv_hostNode
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (empty : attachment.identityRequests = [])
    (node : removed.complement.val.NodeId) :
    allocatedPortEquiv occurrence removed attachment empty
        (attachment.hostNode node) =
      Data.Finite.FiniteEquiv.refl CPort := by
  unfold allocatedPortEquiv ConcreteSpliceAttachment.hostNode
  exact Fin.addCases_left node

private theorem allocatedPortEquiv_fragmentNode
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (empty : attachment.identityRequests = [])
    (node : pattern.val.diagram.NodeId) :
    allocatedPortEquiv occurrence removed attachment empty
        (attachment.fragmentNode node) =
      occurrence.portEquivForNode node := by
  have allocated :
      attachment.fragmentNode node =
        Fin.natAdd removed.complement.val.nodeCount
          (Fin.castAdd attachment.identityRequests.length node) :=
    Fin.ext (by simp [ConcreteSpliceAttachment.fragmentNode])
  rw [allocated]
  unfold allocatedPortEquiv
  rw [Fin.addCases_right]
  exact Fin.addCases_left node

private theorem endpointEquiv_hostEndpoint
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (empty : attachment.identityRequests = [])
    (nodesExact : NodesExact occurrence)
    (endpoint : CEndpoint removed.complement.val.nodeCount) :
    endpointEquiv occurrence removed attachment empty nodesExact
        (attachment.hostEndpoint endpoint) =
      Removal.sourceEndpoint occurrence endpoint := by
  rcases endpoint with ⟨node, port⟩
  simp only [endpointEquiv, ConcreteSpliceAttachment.hostEndpoint,
    Removal.sourceEndpoint]
  rw [nodeEquiv_hostNode occurrence removed attachment empty nodesExact]
  rw [allocatedPortEquiv_hostNode occurrence removed attachment empty]
  rfl

private theorem endpointEquiv_fragmentEndpoint
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (empty : attachment.identityRequests = [])
    (nodesExact : NodesExact occurrence)
    (endpoint : CEndpoint pattern.val.diagram.nodeCount) :
    endpointEquiv occurrence removed attachment empty nodesExact
        (attachment.fragmentEndpoint endpoint) =
      occurrence.endpointMapForNode endpoint
        := by
  rcases endpoint with ⟨node, port⟩
  simp only [endpointEquiv, ConcreteSpliceAttachment.fragmentEndpoint,
    Occurrence.endpointMapForNode]
  rw [nodeEquiv_fragmentNode occurrence removed attachment empty nodesExact]
  rw [allocatedPortEquiv_fragmentNode occurrence removed attachment empty]

private theorem wireEquiv_hostWire
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (exact : WiresExact occurrence)
    (wire : removed.complement.val.WireId) :
    wireEquiv occurrence removed attachment exact
        (attachment.hostWire wire) =
      Removal.sourceWire occurrence wire := by
  change
    wireForward occurrence removed attachment
        (attachment.hostWire wire) =
      Removal.sourceWire occurrence wire
  unfold wireForward ConcreteSpliceAttachment.hostWire
  exact Fin.addCases_left wire

private theorem wireEquiv_freshWire
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (exact : WiresExact occurrence)
    (wire : Fin attachment.fragmentInternalWires.length) :
    wireEquiv occurrence removed attachment exact
        (attachment.freshWire wire) =
      occurrence.wireMap
        (attachment.fragmentInternalWires.get wire) := by
  change
    wireForward occurrence removed attachment
        (attachment.freshWire wire) =
      occurrence.wireMap
        (attachment.fragmentInternalWires.get wire)
  unfold wireForward ConcreteSpliceAttachment.freshWire
  exact Fin.addCases_right wire

private theorem wireEquiv_fragmentWire
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (accepted :
      reconstructionAttachment? occurrence removed =
        some attachment)
    (exact : WiresExact occurrence)
    (wire : pattern.val.diagram.WireId) :
    wireEquiv occurrence removed attachment exact
        (attachment.fragmentWire wire) =
      occurrence.wireMap wire := by
  unfold ConcreteSpliceAttachment.fragmentWire
  split
  · rename_i boundary
    let position :=
      attachment.representativePosition wire boundary
    rw [wireEquiv_hostWire occurrence removed attachment exact]
    change
      Removal.sourceWire occurrence (attachment.target position) =
        occurrence.wireMap wire
    rw [attachment_target occurrence removed attachment accepted]
    rw [Removal.sourceWire_wireIndex]
    unfold boundaryHostWire position
    unfold ConcreteSpliceAttachment.representativePosition
    change
      occurrence.wireMap
          (pattern.val.boundary.get
            (DenseList.index pattern.val.boundary wire boundary)) =
        occurrence.wireMap wire
    rw [DenseList.get_index]
  · rename_i nonboundary
    rw [wireEquiv_freshWire occurrence removed attachment exact]
    rw [DenseList.get_index]

private theorem hostEndpoint_corresponds
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (empty : attachment.identityRequests = [])
    (regionsExact : RegionsExact occurrence)
    (nodesExact : NodesExact occurrence)
    (endpoint : CEndpoint removed.complement.val.nodeCount)
    (required :
      endpoint.port ∈
        removed.complement.val.requiredPorts endpoint.node) :
    PortCorresponds attachment.diagram host.val
      (nodeEquiv occurrence removed attachment empty nodesExact)
      (attachment.hostEndpoint endpoint)
      (Removal.sourceEndpoint occurrence endpoint) := by
  unfold PortCorresponds
  constructor
  · exact
      (nodeEquiv_hostNode occurrence removed attachment empty
        nodesExact endpoint.node).symm
  · have nodeRename :=
      Removal.diagramNode_rename occurrence endpoint.node
    cases baseNode : removed.complement.val.nodes endpoint.node with
    | atom region args =>
        have generatedNode :
            (Removal.diagram occurrence).nodes endpoint.node =
              .atom region args := baseNode
        rw [generatedNode] at nodeRename
        simp [ConcreteSpliceAttachment.diagram_node_hostNode,
          ConcreteSpliceAttachment.renameHostNode,
          generatedNode, nodeRename, mapNode,
          ConcreteSpliceAttachment.hostEndpoint,
          Removal.sourceEndpoint]
    | ref region definition args =>
        have generatedNode :
            (Removal.diagram occurrence).nodes endpoint.node =
              .ref region definition args := baseNode
        rw [generatedNode] at nodeRename
        simp [ConcreteSpliceAttachment.diagram_node_hostNode,
          ConcreteSpliceAttachment.renameHostNode,
          generatedNode, nodeRename, mapNode,
          ConcreteSpliceAttachment.hostEndpoint,
          Removal.sourceEndpoint]
    | identity region sig arity =>
        have generatedNode :
            (Removal.diagram occurrence).nodes endpoint.node =
              .identity region sig arity := baseNode
        rw [generatedNode] at nodeRename
        have requiredIdentity :
            endpoint.port ∈ (List.range arity).map CPort.identity := by
          simpa [ConcreteDiagram.requiredPorts, generatedNode] using required
        obtain ⟨index, _, port⟩ := List.mem_map.mp requiredIdentity
        simp [ConcreteSpliceAttachment.diagram_node_hostNode,
          ConcreteSpliceAttachment.renameHostNode,
          generatedNode, nodeRename, mapNode,
          ConcreteSpliceAttachment.hostEndpoint,
          Removal.sourceEndpoint, ← port]

private theorem fragmentEndpoint_corresponds
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (empty : attachment.identityRequests = [])
    (nodesExact : NodesExact occurrence)
    (endpoint : CEndpoint pattern.val.diagram.nodeCount)
    (required :
      endpoint.port ∈
        pattern.val.diagram.requiredPorts endpoint.node) :
    PortCorresponds attachment.diagram host.val
      (nodeEquiv occurrence removed attachment empty nodesExact)
      (attachment.fragmentEndpoint endpoint)
      ⟨occurrence.nodeMap endpoint.node, endpoint.port⟩ := by
  unfold PortCorresponds
  constructor
  · exact
      (nodeEquiv_fragmentNode occurrence removed attachment empty
        nodesExact endpoint.node).symm
  · have nodeCorresponds :=
      occurrence.node_correspondence endpoint.node
    cases sourceNode : pattern.val.diagram.nodes endpoint.node with
    | atom region args =>
        simp [OccurrenceNodeCorresponds, sourceNode] at nodeCorresponds
        have patternNode :
            pattern.val.diagram.nodes endpoint.node =
              .atom region args := sourceNode
        simp [ConcreteSpliceAttachment.diagram_node_fragmentNode,
          ConcreteSpliceAttachment.renameFragmentNode,
          patternNode, nodeCorresponds,
          ConcreteSpliceAttachment.fragmentEndpoint]
    | ref region definition args =>
        simp [OccurrenceNodeCorresponds, sourceNode] at nodeCorresponds
        have patternNode :
            pattern.val.diagram.nodes endpoint.node =
              .ref region definition args := sourceNode
        simp [ConcreteSpliceAttachment.diagram_node_fragmentNode,
          ConcreteSpliceAttachment.renameFragmentNode,
          patternNode, nodeCorresponds,
          ConcreteSpliceAttachment.fragmentEndpoint]
    | identity region sig arity =>
        simp [OccurrenceNodeCorresponds, sourceNode] at nodeCorresponds
        have patternNode :
            pattern.val.diagram.nodes endpoint.node =
              .identity region sig arity := sourceNode
        have requiredIdentity :
            endpoint.port ∈ (List.range arity).map CPort.identity := by
          simpa [ConcreteDiagram.requiredPorts, sourceNode] using required
        obtain ⟨index, _, port⟩ := List.mem_map.mp requiredIdentity
        simp [ConcreteSpliceAttachment.diagram_node_fragmentNode,
          ConcreteSpliceAttachment.renameFragmentNode,
          patternNode, nodeCorresponds,
          ConcreteSpliceAttachment.fragmentEndpoint, ← port]

private theorem occurrenceEndpointMultisetContains_mem
    {expected actual : List (OccurrenceEndpointKey nodeCount)}
    (contained :
      occurrenceEndpointMultisetContains expected actual = true)
    {key : OccurrenceEndpointKey nodeCount}
    (member : key ∈ expected) :
    key ∈ actual := by
  induction expected generalizing actual with
  | nil => contradiction
  | cons head tail induction =>
      unfold occurrenceEndpointMultisetContains at contained
      split at contained
      · rename_i headMember
        rw [List.mem_cons] at member
        rcases member with rfl | member
        · exact headMember
        · exact List.mem_of_mem_erase
            (induction contained member)
      · contradiction

private theorem fragmentEndpoint_corresponds_of_key
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (empty : attachment.identityRequests = [])
    (nodesExact : NodesExact occurrence)
    (source : CEndpoint pattern.val.diagram.nodeCount)
    (candidate : CEndpoint host.val.nodeCount)
    (sourceRequired :
      source.port ∈
        pattern.val.diagram.requiredPorts source.node)
    (sameKey :
      mappedOccurrenceEndpointKey occurrence.nodeMap source =
        occurrenceEndpointKey candidate) :
    PortCorresponds attachment.diagram host.val
      (nodeEquiv occurrence removed attachment empty nodesExact)
      (attachment.fragmentEndpoint source) candidate := by
  rcases source with ⟨sourceNodeId, sourcePort⟩
  rcases candidate with ⟨candidateNodeId, candidatePort⟩
  have nodeEquality :
      candidateNodeId = occurrence.nodeMap sourceNodeId := by
    exact (congrArg Prod.fst sameKey).symm
  have portKey :
      OccurrencePort.ofConcrete sourcePort =
        OccurrencePort.ofConcrete candidatePort :=
    congrArg Prod.snd sameKey
  unfold PortCorresponds
  constructor
  · change
      candidateNodeId =
        (nodeEquiv occurrence removed attachment empty
          nodesExact) (attachment.fragmentNode sourceNodeId)
    rw [nodeEquiv_fragmentNode occurrence removed attachment
      empty nodesExact]
    exact nodeEquality
  · have nodeCorresponds := occurrence.node_correspondence sourceNodeId
    simp only [ConcreteSpliceAttachment.fragmentEndpoint]
    cases sourceNode : pattern.val.diagram.nodes sourceNodeId with
    | atom region args =>
        simp [OccurrenceNodeCorresponds, sourceNode] at nodeCorresponds
        rw [ConcreteSpliceAttachment.diagram_node_fragmentNode]
        simp [ConcreteSpliceAttachment.renameFragmentNode, sourceNode,
          ConcreteSpliceAttachment.fragmentEndpoint,
          nodeEquality, nodeCorresponds]
        cases sourcePort <;> cases candidatePort <;>
          simp [OccurrencePort.ofConcrete, ConcreteDiagram.requiredPorts,
            sourceNode] at portKey sourceRequired ⊢ <;> omega
    | ref region definition args =>
        simp [OccurrenceNodeCorresponds, sourceNode] at nodeCorresponds
        rw [ConcreteSpliceAttachment.diagram_node_fragmentNode]
        simp [ConcreteSpliceAttachment.renameFragmentNode, sourceNode,
          ConcreteSpliceAttachment.fragmentEndpoint,
          nodeEquality, nodeCorresponds]
        cases sourcePort <;> cases candidatePort <;>
          simp [OccurrencePort.ofConcrete, ConcreteDiagram.requiredPorts,
            sourceNode] at portKey sourceRequired ⊢ <;> omega
    | identity region sig arity =>
        simp [OccurrenceNodeCorresponds, sourceNode] at nodeCorresponds
        rw [ConcreteSpliceAttachment.diagram_node_fragmentNode]
        simp [ConcreteSpliceAttachment.renameFragmentNode, sourceNode,
          ConcreteSpliceAttachment.fragmentEndpoint,
          nodeEquality, nodeCorresponds]
        cases sourcePort with
        | head =>
            simp [ConcreteDiagram.requiredPorts, sourceNode] at sourceRequired
        | arg sourceIndex =>
            simp [ConcreteDiagram.requiredPorts, sourceNode] at sourceRequired
        | identity sourceIndex =>
            cases candidatePort with
            | identity candidateIndex =>
                exact
                  ⟨⟨sourceIndex, rfl⟩, candidateIndex, rfl⟩
            | head =>
                simp [OccurrencePort.ofConcrete] at portKey
            | arg candidateIndex =>
                simp [OccurrencePort.ofConcrete] at portKey

private theorem occurrenceEndpoint_forward
    (occurrence : Occurrence pattern host)
    (wire : pattern.val.diagram.WireId)
    (endpoint : CEndpoint pattern.val.diagram.nodeCount)
    (incident : endpoint ∈ (pattern.val.diagram.wires wire).endpoints) :
    ∃ candidate : CEndpoint host.val.nodeCount,
      candidate ∈ (host.val.wires (occurrence.wireMap wire)).endpoints ∧
        mappedOccurrenceEndpointKey occurrence.nodeMap endpoint =
          occurrenceEndpointKey candidate := by
  have expectedMember :
      mappedOccurrenceEndpointKey occurrence.nodeMap endpoint ∈
        (pattern.val.diagram.wires wire).endpoints.map
          (mappedOccurrenceEndpointKey occurrence.nodeMap) :=
    List.mem_map.mpr ⟨endpoint, incident, rfl⟩
  by_cases boundary : wire ∈ pattern.val.boundary
  · have actualMember :=
      occurrenceEndpointMultisetContains_mem
        (occurrence.boundaryEndpoints_contained wire boundary)
        expectedMember
    rcases List.mem_map.mp actualMember with
      ⟨candidate, candidateIncident, equality⟩
    exact ⟨candidate, candidateIncident, equality.symm⟩
  · have actualMember :=
      (occurrence.internalEndpoints_exact wire boundary).mem_iff.mp
        expectedMember
    rcases List.mem_map.mp actualMember with
      ⟨candidate, candidateIncident, equality⟩
    exact ⟨candidate, candidateIncident, equality.symm⟩

/-- The occurrence-owned positional endpoint map lands on the mapped wire. -/
theorem occurrenceEndpointMap_mem
    {definitions : List (List Sig)}
    {pattern : CheckedOpenDiagram definitions}
    {host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host)
    (wire : pattern.val.diagram.WireId)
    (endpoint : CEndpoint pattern.val.diagram.nodeCount)
    (incident : endpoint ∈ (pattern.val.diagram.wires wire).endpoints) :
    occurrence.endpointMapForNode endpoint ∈
      (host.val.wires (occurrence.wireMap wire)).endpoints := by
  have required :=
    ConcreteDiagram.incident_port_required _ pattern.val.diagram
      pattern.property.diagram wire endpoint incident
  cases endpoint with
  | mk node port =>
      cases nodeData : pattern.val.diagram.nodes node with
      | identity region sig arity =>
          have sourceNode :
              pattern.val.diagram.nodes node = .identity region sig arity :=
            nodeData
          have requiredIdentity :
              port ∈ (List.range arity).map CPort.identity := by
            simpa [ConcreteDiagram.requiredPorts, sourceNode] using required
          obtain ⟨index, bound, portExact⟩ := List.mem_map.mp requiredIdentity
          have boundLt : index < arity := List.mem_range.mp bound
          subst port
          have sourceOwner :=
            ConcreteDiagram.endpointOwner?_eq_of_incident _
              pattern.val.diagram pattern.property.diagram node
              (.identity index)
              (by simp [ConcreteDiagram.requiredPorts, sourceNode, boundLt])
              wire incident
          have targetOwner := occurrence.identityPortEquiv_owner node region
            sig arity sourceNode ⟨index, boundLt⟩ wire sourceOwner
          have targetIncident :=
            ConcreteDiagram.endpointOwner?_incident host.val
              ⟨occurrence.nodeMap node,
                .identity
                  ((occurrence.identityPortEquiv node region sig arity
                    sourceNode) ⟨index, boundLt⟩).val⟩
              (occurrence.wireMap wire) targetOwner
          simpa [Occurrence.endpointMapForNode,
            Occurrence.portEquivForNode_identity occurrence node region sig
              arity sourceNode,
            Occurrence.identityCPortEquiv,
            boundLt] using targetIncident
      | atom region args =>
          have sourceNode :
              pattern.val.diagram.nodes node = .atom region args := nodeData
          have sourcePortRequired := required
          simp [ConcreteDiagram.requiredPorts, sourceNode] at sourcePortRequired
          rcases occurrenceEndpoint_forward occurrence wire ⟨node, port⟩
              incident with
            ⟨candidate, candidateIncident, sameKey⟩
          have candidateExact :
              candidate = occurrence.endpointMapForNode ⟨node, port⟩ := by
            rcases candidate with ⟨candidateNode, candidatePort⟩
            simp [mappedOccurrenceEndpointKey, occurrenceEndpointKey,
              Occurrence.endpointMapForNode,
              Occurrence.portEquivForNode_atom occurrence node region args
                sourceNode] at sameKey ⊢
            rcases sameKey with ⟨nodeExact, portExact⟩
            subst candidateNode
            cases port <;> cases candidatePort <;>
              simp_all [OccurrencePort.ofConcrete]
          simpa [candidateExact] using candidateIncident

      | ref region definition args =>
          have sourceNode :
              pattern.val.diagram.nodes node =
                .ref region definition args := nodeData
          have sourcePortRequired := required
          simp [ConcreteDiagram.requiredPorts, sourceNode] at sourcePortRequired
          rcases occurrenceEndpoint_forward occurrence wire ⟨node, port⟩
              incident with
            ⟨candidate, candidateIncident, sameKey⟩
          have candidateExact :
              candidate = occurrence.endpointMapForNode ⟨node, port⟩ := by
            rcases candidate with ⟨candidateNode, candidatePort⟩
            simp [mappedOccurrenceEndpointKey, occurrenceEndpointKey,
              Occurrence.endpointMapForNode,
              Occurrence.portEquivForNode_ref occurrence node region
                definition args sourceNode] at sameKey ⊢
            rcases sameKey with ⟨nodeExact, portExact⟩
            subst candidateNode
            cases port <;> cases candidatePort <;>
              simp_all [OccurrencePort.ofConcrete]
          simpa [candidateExact] using candidateIncident

/-- Invert the positional endpoint map at an explicitly identified occurrence
node.  The owning pattern wire is recovered from well-formed port ownership. -/
theorem occurrenceEndpointMap_preimage
    (occurrence : Occurrence pattern host)
    (patternNode : pattern.val.diagram.NodeId)
    (wire : host.val.WireId)
    (candidate : CEndpoint host.val.nodeCount)
    (incident : candidate ∈ (host.val.wires wire).endpoints)
    (nodeExact : occurrence.nodeMap patternNode = candidate.node) :
    ∃ sourceWire : pattern.val.diagram.WireId,
      ∃ sourceEndpoint : CEndpoint pattern.val.diagram.nodeCount,
        sourceEndpoint ∈
            (pattern.val.diagram.wires sourceWire).endpoints ∧
          occurrence.wireMap sourceWire = wire ∧
          occurrence.endpointMapForNode sourceEndpoint = candidate := by
  let sourcePort :=
    (occurrence.portEquivForNode patternNode).symm candidate.port
  let sourceEndpoint : CEndpoint pattern.val.diagram.nodeCount :=
    ⟨patternNode, sourcePort⟩
  have candidateRequired :=
    ConcreteDiagram.incident_port_required _ host.val host.property
      wire candidate incident
  have sourceRequired :
      sourcePort ∈ pattern.val.diagram.requiredPorts patternNode := by
    have correspondence := occurrence.node_correspondence patternNode
    cases nodeData : pattern.val.diagram.nodes patternNode with
    | atom region args =>
        have hostData : host.val.nodes candidate.node =
            .atom (occurrence.regionMap region) args := by
          rw [← nodeExact]
          simpa [OccurrenceNodeCorresponds, nodeData] using correspondence
        simpa [sourcePort, ConcreteDiagram.requiredPorts, nodeData, hostData,
          Occurrence.portEquivForNode_atom occurrence patternNode region args
            nodeData] using candidateRequired
    | ref region definition args =>
        have hostData : host.val.nodes candidate.node =
            .ref (occurrence.regionMap region) definition args := by
          rw [← nodeExact]
          simpa [OccurrenceNodeCorresponds, nodeData] using correspondence
        simpa [sourcePort, ConcreteDiagram.requiredPorts, nodeData, hostData,
          Occurrence.portEquivForNode_ref occurrence patternNode region
            definition args nodeData] using candidateRequired
    | identity region sig arity =>
        have hostData : host.val.nodes candidate.node =
            .identity (occurrence.regionMap region) sig arity := by
          rw [← nodeExact]
          simpa [OccurrenceNodeCorresponds, nodeData] using correspondence
        have candidateIdentity :
            candidate.port ∈ (List.range arity).map CPort.identity := by
          simpa [ConcreteDiagram.requiredPorts, hostData] using
            candidateRequired
        obtain ⟨index, indexBound, portExact⟩ :=
          List.mem_map.mp candidateIdentity
        have indexLt : index < arity := List.mem_range.mp indexBound
        unfold sourcePort
        rw [← portExact]
        simp [ConcreteDiagram.requiredPorts, nodeData,
          Occurrence.portEquivForNode_identity occurrence patternNode region
            sig arity nodeData,
          Occurrence.identityCPortEquiv, indexLt]
  obtain ⟨sourceWire, sourceOwner⟩ :=
    ConcreteDiagram.endpointOwner?_complete _ pattern.val.diagram
      pattern.property.diagram patternNode sourcePort sourceRequired
  have sourceIncident :=
    ConcreteDiagram.endpointOwner?_incident pattern.val.diagram
      sourceEndpoint sourceWire sourceOwner
  have mappedIncident := occurrenceEndpointMap_mem occurrence
    sourceWire sourceEndpoint sourceIncident
  have endpointExact :
      occurrence.endpointMapForNode sourceEndpoint = candidate := by
    rcases candidate with ⟨candidateNode, candidatePort⟩
    simp only [Occurrence.endpointMapForNode, sourceEndpoint, sourcePort]
    congr
    exact (occurrence.portEquivForNode patternNode).right_inv candidatePort
  have mappedOwner :=
    ConcreteDiagram.endpointOwner?_eq_of_incident _ host.val host.property
      candidate.node candidate.port candidateRequired
      (occurrence.wireMap sourceWire) (by
        rw [← endpointExact]
        exact mappedIncident)
  have candidateOwner :=
    ConcreteDiagram.endpointOwner?_eq_of_incident _ host.val host.property
      candidate.node candidate.port candidateRequired wire incident
  exact ⟨sourceWire, sourceEndpoint, sourceIncident,
    Option.some.inj (mappedOwner.symm.trans candidateOwner), endpointExact⟩

/-- Every endpoint of an internal occurrence wire lies on an occurrence-mapped
node, independently of identity storage-position renaming. -/
theorem occurrenceInternalEndpoint_node_preimage
    (occurrence : Occurrence pattern host)
    (wire : pattern.val.diagram.WireId)
    (internal : wire ∉ pattern.val.boundary)
    (candidate : CEndpoint host.val.nodeCount)
    (incident :
      candidate ∈ (host.val.wires (occurrence.wireMap wire)).endpoints) :
    ∃ endpoint : CEndpoint pattern.val.diagram.nodeCount,
      endpoint ∈ (pattern.val.diagram.wires wire).endpoints ∧
        occurrence.nodeMap endpoint.node = candidate.node := by
  have actualMember :
      occurrenceEndpointKey candidate ∈
        (host.val.wires (occurrence.wireMap wire)).endpoints.map
          occurrenceEndpointKey :=
    List.mem_map.mpr ⟨candidate, incident, rfl⟩
  have expectedMember :=
    (occurrence.internalEndpoints_exact wire internal).mem_iff.mpr actualMember
  rcases List.mem_map.mp expectedMember with
    ⟨endpoint, endpointIncident, keyExact⟩
  exact ⟨endpoint, endpointIncident,
    congrArg Prod.fst keyExact⟩

/-- Positional occurrence transport preserves the semantic endpoint key. -/
private theorem occurrenceEndpointMap_key
    (occurrence : Occurrence pattern host)
    (wire : pattern.val.diagram.WireId)
    (endpoint : CEndpoint pattern.val.diagram.nodeCount)
    (incident : endpoint ∈ (pattern.val.diagram.wires wire).endpoints) :
    mappedOccurrenceEndpointKey occurrence.nodeMap endpoint =
      occurrenceEndpointKey (occurrence.endpointMapForNode endpoint) := by
  have required :=
    ConcreteDiagram.incident_port_required _ pattern.val.diagram
      pattern.property.diagram wire endpoint incident
  rcases endpoint with ⟨node, port⟩
  unfold Occurrence.endpointMapForNode
  cases nodeData : pattern.val.diagram.nodes node with
  | atom region args =>
      rw [Occurrence.portEquivForNode_atom occurrence node region args
        nodeData]
      simp [mappedOccurrenceEndpointKey, occurrenceEndpointKey,
        Occurrence.endpointMapForNode]
  | ref region definition args =>
      rw [Occurrence.portEquivForNode_ref occurrence node region definition
        args nodeData]
      simp [mappedOccurrenceEndpointKey, occurrenceEndpointKey,
        Occurrence.endpointMapForNode]
  | identity region sig arity =>
      rw [Occurrence.portEquivForNode_identity occurrence node region sig
        arity nodeData]
      have requiredIdentity :
          port ∈ (List.range arity).map CPort.identity := by
        simpa [ConcreteDiagram.requiredPorts, nodeData] using required
      obtain ⟨index, bound, portExact⟩ := List.mem_map.mp requiredIdentity
      have boundLt : index < arity := List.mem_range.mp bound
      subst port
      simp [mappedOccurrenceEndpointKey, occurrenceEndpointKey,
        Occurrence.endpointMapForNode, Occurrence.identityCPortEquiv,
        boundLt, OccurrencePort.ofConcrete]

/-- The splice-wide positional endpoint transport lands on the exact wire. -/
private theorem endpointEquiv_mem
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (accepted :
      reconstructionAttachment? occurrence removed = some attachment)
    (empty : attachment.identityRequests = [])
    (nodesExact : NodesExact occurrence)
    (wiresExact : WiresExact occurrence)
    (wire : attachment.diagram.WireId)
    (endpoint : CEndpoint attachment.diagram.nodeCount)
    (member : endpoint ∈ (attachment.diagram.wires wire).endpoints) :
    endpointEquiv occurrence removed attachment empty nodesExact endpoint ∈
      (host.val.wires
        (wireEquiv occurrence removed attachment wiresExact wire)).endpoints := by
  have generatedCase :
      ∀ candidateWire generatedEndpoint,
        generatedEndpoint ∈ attachment.generatedEndpoints candidateWire →
          endpointEquiv occurrence removed attachment empty nodesExact
              generatedEndpoint ∈
            (host.val.wires
              (wireEquiv occurrence removed attachment wiresExact
                candidateWire)).endpoints := by
    intro candidateWire generatedEndpoint generatedMember
    rcases attachment.generatedEndpoint_origin empty candidateWire
        generatedEndpoint generatedMember with
      ⟨sourceWire, sourceEndpoint, sourceIncident, mappedWire,
        mappedEndpoint⟩
    subst generatedEndpoint
    rw [endpointEquiv_fragmentEndpoint occurrence removed attachment empty
      nodesExact]
    have landed := occurrenceEndpointMap_mem occurrence sourceWire
      sourceEndpoint (by simpa [] using sourceIncident)
    have mappedHostWire :
        wireEquiv occurrence removed attachment wiresExact candidateWire =
          occurrence.wireMap sourceWire := by
      rw [← mappedWire]
      exact wireEquiv_fragmentWire occurrence removed attachment accepted
        wiresExact sourceWire
    simpa [mappedHostWire] using landed
  revert endpoint
  refine Fin.addCases ?_ ?_ wire
  · intro retained endpoint member
    unfold ConcreteSpliceAttachment.diagram
      ConcreteSpliceAttachment.wireTable at member
    simp only [ConcreteSpliceAttachment.hostWire,
      Fin.addCases_left] at member
    rcases List.mem_append.mp member with retainedMember | generatedMember
    · rcases List.mem_map.mp retainedMember with
        ⟨sourceEndpoint, sourceIncident, rfl⟩
      rw [endpointEquiv_hostEndpoint occurrence removed attachment empty
        nodesExact]
      change
        Removal.sourceEndpoint occurrence sourceEndpoint ∈
          (host.val.wires
            (wireEquiv occurrence removed attachment wiresExact
              (attachment.hostWire retained))).endpoints
      rw [wireEquiv_hostWire occurrence removed attachment wiresExact]
      exact
        (Removal.diagramEndpoint_mem_iff occurrence retained sourceEndpoint).mp
          sourceIncident
    · exact generatedCase (attachment.hostWire retained) endpoint
        generatedMember
  · intro fresh endpoint member
    unfold ConcreteSpliceAttachment.diagram
      ConcreteSpliceAttachment.wireTable at member
    simp only [ConcreteSpliceAttachment.freshWire,
      Fin.addCases_right] at member
    exact generatedCase (attachment.freshWire fresh) endpoint member
/-- Exact reconstructed region table under the construction-owned correspondence. -/
theorem regionTable_exact
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (regionsExact : RegionsExact occurrence)
    (region : attachment.diagram.RegionId) :
    host.val.regions
        (regionEquiv occurrence removed attachment regionsExact
          region) =
      (attachment.diagram.regions region).rename
        (regionEquiv occurrence removed attachment regionsExact) := by
  refine Fin.addCases ?_ ?_ region
  · intro retained
    change
      host.val.regions
          (regionEquiv occurrence removed attachment regionsExact
            (attachment.hostRegion retained)) =
        (attachment.diagram.regions
          (attachment.hostRegion retained)).rename
            (regionEquiv occurrence removed attachment regionsExact)
    have relation := Removal.diagramRegion_rename occurrence retained
    change
      host.val.regions (Removal.sourceRegion occurrence retained) =
        mapRegion (Removal.sourceRegion occurrence)
          (removed.complement.val.regions retained) at relation
    rw [regionEquiv_hostRegion occurrence removed attachment
      regionsExact]
    rw [ConcreteSpliceAttachment.diagram_region_hostRegion]
    cases data : removed.complement.val.regions retained with
    | sheet =>
        rw [data] at relation
        change
          host.val.regions (Removal.sourceRegion occurrence retained) =
            .sheet
        exact relation
    | cut parent =>
        rw [data] at relation
        simp only [mapRegion] at relation
        change
          host.val.regions (Removal.sourceRegion occurrence retained) =
            .cut
              (regionEquiv occurrence removed attachment
                regionsExact (attachment.hostRegion parent))
        rw [regionEquiv_hostRegion occurrence removed attachment
          regionsExact]
        exact relation
  · intro fresh
    change
      host.val.regions
          (regionEquiv occurrence removed attachment regionsExact
            (attachment.freshRegion fresh)) =
        (attachment.diagram.regions
          (attachment.freshRegion fresh)).rename
            (regionEquiv occurrence removed attachment regionsExact)
    let source := attachment.fragmentRegions.get fresh
    have sourceMember : source ∈ attachment.fragmentRegions :=
      List.get_mem _ fresh
    have sourceNonroot : source ≠ pattern.val.diagram.root := by
      simpa [ConcreteSpliceAttachment.fragmentRegions,
        ConcreteDiagram.regionsList, Data.Finite.mem_allFin] using
          (List.mem_filter.mp sourceMember).2
    rw [regionEquiv_freshRegion occurrence removed attachment
      regionsExact]
    rw [ConcreteSpliceAttachment.diagram_region_freshRegion]
    cases data : pattern.val.diagram.regions source with
    | sheet =>
        have onlyRoot :
            pattern.val.diagram.regions source = .sheet →
              source = pattern.val.diagram.root :=
          of_decide_eq_true
            (List.all_eq_true.mp
              pattern.property.diagram.only_root_is_sheet source
              (Data.Finite.mem_allFin source))
        exact False.elim (sourceNonroot (onlyRoot data))
    | cut parent =>
        have relation := occurrence.maps_parentage source parent data
        simp only [mapRegion, CRegion.rename]
        change
          host.val.regions (occurrence.regionMap source) =
            .cut
              (regionEquiv occurrence removed attachment
                regionsExact (attachment.fragmentRegion parent))
        rw [regionEquiv_fragmentRegion occurrence removed attachment
          regionsExact]
        exact relation

/-- Exact reconstructed node table under the construction-owned correspondence. -/
theorem nodeTable_exact
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (empty : attachment.identityRequests = [])
    (regionsExact : RegionsExact occurrence)
    (nodesExact : NodesExact occurrence)
    (node : attachment.diagram.NodeId) :
    host.val.nodes
        (nodeEquiv occurrence removed attachment empty nodesExact
          node) =
      (attachment.diagram.nodes node).rename
        (regionEquiv occurrence removed attachment regionsExact) := by
  refine Fin.addCases ?_ ?_ node
  · intro retained
    change
      host.val.nodes
          (nodeEquiv occurrence removed attachment empty nodesExact
            (attachment.hostNode retained)) =
        (attachment.diagram.nodes
          (attachment.hostNode retained)).rename
            (regionEquiv occurrence removed attachment regionsExact)
    have relation := Removal.diagramNode_rename occurrence retained
    change
      host.val.nodes (Removal.sourceNode occurrence retained) =
        mapNode (Removal.sourceRegion occurrence)
          (removed.complement.val.nodes retained) at relation
    rw [nodeEquiv_hostNode occurrence removed attachment empty
      nodesExact]
    rw [ConcreteSpliceAttachment.diagram_node_hostNode]
    cases data : removed.complement.val.nodes retained with
    | atom region args =>
        rw [data] at relation
        simp only [mapNode] at relation
        have attachmentData :
            attachment.renameHostNode retained =
              .atom (attachment.hostRegion region) args := by
          unfold ConcreteSpliceAttachment.renameHostNode
          rw [data]
        rw [attachmentData]
        simp only [CNode.rename]
        change
          host.val.nodes (Removal.sourceNode occurrence retained) =
            .atom
              (regionEquiv occurrence removed attachment
                regionsExact (attachment.hostRegion region)) args
        rw [regionEquiv_hostRegion occurrence removed attachment
          regionsExact]
        exact relation
    | ref region definition args =>
        rw [data] at relation
        simp only [mapNode] at relation
        have attachmentData :
            attachment.renameHostNode retained =
              .ref (attachment.hostRegion region) definition args := by
          unfold ConcreteSpliceAttachment.renameHostNode
          rw [data]
        rw [attachmentData]
        simp only [CNode.rename]
        change
          host.val.nodes (Removal.sourceNode occurrence retained) =
            .ref
              (regionEquiv occurrence removed attachment
                regionsExact (attachment.hostRegion region)) definition args
        rw [regionEquiv_hostRegion occurrence removed attachment
          regionsExact]
        exact relation
    | identity region sig arity =>
        rw [data] at relation
        simp only [mapNode] at relation
        have attachmentData :
            attachment.renameHostNode retained =
              .identity (attachment.hostRegion region) sig arity := by
          unfold ConcreteSpliceAttachment.renameHostNode
          rw [data]
        rw [attachmentData]
        simp only [CNode.rename]
        change
          host.val.nodes (Removal.sourceNode occurrence retained) =
            .identity
              (regionEquiv occurrence removed attachment
                regionsExact (attachment.hostRegion region)) sig arity
        rw [regionEquiv_hostRegion occurrence removed attachment
          regionsExact]
        exact relation
  · intro inserted
    refine Fin.addCases ?_ ?_ inserted
    · intro source
      change
        host.val.nodes
            (nodeEquiv occurrence removed attachment empty nodesExact
              (attachment.fragmentNode source)) =
          (attachment.diagram.nodes
            (attachment.fragmentNode source)).rename
              (regionEquiv occurrence removed attachment regionsExact)
      have relation := occurrence.node_correspondence source
      rw [nodeEquiv_fragmentNode occurrence removed attachment
        empty nodesExact]
      rw [ConcreteSpliceAttachment.diagram_node_fragmentNode]
      cases data : pattern.val.diagram.nodes source with
      | atom region args =>
          simp [OccurrenceNodeCorresponds, data] at relation
          have attachmentData :
              attachment.renameFragmentNode source =
                .atom (attachment.fragmentRegion region) args := by
            simp [ConcreteSpliceAttachment.renameFragmentNode, data]
          rw [attachmentData]
          simp only [CNode.rename]
          change
            host.val.nodes (occurrence.nodeMap source) =
              .atom
                (regionEquiv occurrence removed attachment
                  regionsExact (attachment.fragmentRegion region)) args
          rw [regionEquiv_fragmentRegion occurrence removed
            attachment regionsExact]
          exact relation
      | ref region definition args =>
          simp [OccurrenceNodeCorresponds, data] at relation
          have attachmentData :
              attachment.renameFragmentNode source =
                .ref (attachment.fragmentRegion region) definition args := by
            simp [ConcreteSpliceAttachment.renameFragmentNode, data]
          rw [attachmentData]
          simp only [CNode.rename]
          change
            host.val.nodes (occurrence.nodeMap source) =
              .ref
                (regionEquiv occurrence removed attachment
                  regionsExact (attachment.fragmentRegion region))
                definition args
          rw [regionEquiv_fragmentRegion occurrence removed
            attachment regionsExact]
          exact relation
      | identity region sig arity =>
          simp [OccurrenceNodeCorresponds, data] at relation
          have attachmentData :
              attachment.renameFragmentNode source =
                .identity (attachment.fragmentRegion region) sig arity := by
            simp [ConcreteSpliceAttachment.renameFragmentNode, data]
          rw [attachmentData]
          simp only [CNode.rename]
          change
            host.val.nodes (occurrence.nodeMap source) =
              .identity
                (regionEquiv occurrence removed attachment
                  regionsExact (attachment.fragmentRegion region)) sig arity
          rw [regionEquiv_fragmentRegion occurrence removed
            attachment regionsExact]
          exact relation
    · intro identity
      exact eliminateIdentityRequest attachment empty identity

/-- Exact reconstructed wire signatures under the construction-owned correspondence. -/
theorem wireSignature_exact
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (wiresExact : WiresExact occurrence)
    (wire : attachment.diagram.WireId) :
    (host.val.wires
        (wireEquiv occurrence removed attachment wiresExact
          wire)).sig =
      (attachment.diagram.wires wire).sig := by
  refine Fin.addCases ?_ ?_ wire
  · intro retained
    change
      (host.val.wires
          (wireEquiv occurrence removed attachment wiresExact
            (attachment.hostWire retained))).sig =
        (attachment.diagram.wires
          (attachment.hostWire retained)).sig
    rw [wireEquiv_hostWire occurrence removed attachment
      wiresExact]
    rw [ConcreteSpliceAttachment.diagram_wire_hostWire]
    exact Removal.diagramWire_signature occurrence retained
  · intro fresh
    change
      (host.val.wires
          (wireEquiv occurrence removed attachment wiresExact
            (attachment.freshWire fresh))).sig =
        (attachment.diagram.wires
          (attachment.freshWire fresh)).sig
    let source := attachment.fragmentInternalWires.get fresh
    rw [wireEquiv_freshWire occurrence removed attachment
      wiresExact]
    change
      (host.val.wires (occurrence.wireMap source)).sig =
        (attachment.diagram.wires (attachment.freshWire fresh)).sig
    rw [occurrence.wire_signature_preserved]
    unfold ConcreteSpliceAttachment.diagram
      ConcreteSpliceAttachment.wireTable
      ConcreteSpliceAttachment.freshWire
    simp only [Fin.addCases_right]
    change
      (pattern.val.diagram.wires source).sig =
        (pattern.val.diagram.wires source).sig
    rfl

/-- Exact reconstructed wire scopes under the construction-owned correspondence. -/
theorem wireScope_exact
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (regionsExact : RegionsExact occurrence)
    (wiresExact : WiresExact occurrence)
    (wire : attachment.diagram.WireId) :
    (host.val.wires
        (wireEquiv occurrence removed attachment wiresExact
          wire)).scope =
      regionEquiv occurrence removed attachment regionsExact
        (attachment.diagram.wires wire).scope := by
  refine Fin.addCases ?_ ?_ wire
  · intro retained
    change
      (host.val.wires
          (wireEquiv occurrence removed attachment wiresExact
            (attachment.hostWire retained))).scope =
        regionEquiv occurrence removed attachment regionsExact
          (attachment.diagram.wires
            (attachment.hostWire retained)).scope
    have relation := Removal.diagramWire_scope_rename occurrence retained
    change
      (host.val.wires (Removal.sourceWire occurrence retained)).scope =
        Removal.sourceRegion occurrence
          (removed.complement.val.wires retained).scope at relation
    rw [wireEquiv_hostWire occurrence removed attachment
      wiresExact]
    rw [ConcreteSpliceAttachment.diagram_wire_hostWire_scope]
    rw [regionEquiv_hostRegion occurrence removed attachment
      regionsExact]
    exact relation
  · intro fresh
    change
      (host.val.wires
          (wireEquiv occurrence removed attachment wiresExact
            (attachment.freshWire fresh))).scope =
        regionEquiv occurrence removed attachment regionsExact
          (attachment.diagram.wires
            (attachment.freshWire fresh)).scope
    let source := attachment.fragmentInternalWires.get fresh
    have sourceMember : source ∈ attachment.fragmentInternalWires :=
      List.get_mem _ fresh
    have nonboundary : source ∉ pattern.val.boundary := by
      simpa [source, ConcreteSpliceAttachment.fragmentInternalWires,
        ConcreteDiagram.wiresList, Data.Finite.mem_allFin] using
          (List.mem_filter.mp sourceMember).2
    rw [wireEquiv_freshWire occurrence removed attachment
      wiresExact]
    rw [occurrence.internalWire_scope source nonboundary]
    rw [ConcreteSpliceAttachment.diagram_wire_freshWire_scope]
    rw [regionEquiv_fragmentRegion occurrence removed attachment
      regionsExact]

/-- Every reconstructed endpoint has an exact source endpoint correspondence. -/
theorem endpointForward_exact
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (accepted :
      reconstructionAttachment? occurrence removed =
        some attachment)
    (empty : attachment.identityRequests = [])
    (regionsExact : RegionsExact occurrence)
    (nodesExact : NodesExact occurrence)
    (wiresExact : WiresExact occurrence)
    (wire : attachment.diagram.WireId)
    (endpoint : CEndpoint attachment.diagram.nodeCount)
    (member : endpoint ∈ (attachment.diagram.wires wire).endpoints) :
    ∃ candidate,
      candidate ∈
          (host.val.wires
            (wireEquiv occurrence removed attachment wiresExact
              wire)).endpoints ∧
        PortCorresponds attachment.diagram host.val
          (nodeEquiv occurrence removed attachment empty nodesExact)
          endpoint candidate := by
  have generatedCase :
      ∀ candidateWire generatedEndpoint,
        generatedEndpoint ∈ attachment.generatedEndpoints candidateWire →
        ∃ candidate,
          candidate ∈
              (host.val.wires
                (wireEquiv occurrence removed attachment wiresExact
                  candidateWire)).endpoints ∧
            PortCorresponds attachment.diagram host.val
              (nodeEquiv occurrence removed attachment empty
                nodesExact)
              generatedEndpoint candidate := by
    intro candidateWire generatedEndpoint generatedMember
    rcases attachment.generatedEndpoint_origin empty candidateWire
        generatedEndpoint generatedMember with
      ⟨source, sourceEndpoint, sourceIncident, mappedWire, mappedEndpoint⟩
    rcases occurrenceEndpoint_forward occurrence source sourceEndpoint
        (by
          simpa [] using sourceIncident) with
      ⟨candidate, candidateIncident, sameKey⟩
    have mappedHostWire :
        occurrence.wireMap source =
          wireEquiv occurrence removed attachment wiresExact
            candidateWire := by
      calc
        occurrence.wireMap source =
            wireEquiv occurrence removed attachment wiresExact
              (attachment.fragmentWire source) :=
          (wireEquiv_fragmentWire occurrence removed attachment
            accepted wiresExact source).symm
        _ =
            wireEquiv occurrence removed attachment wiresExact
              candidateWire :=
          congrArg
            (wireEquiv occurrence removed attachment wiresExact)
            mappedWire
    rw [← mappedHostWire]
    subst generatedEndpoint
    refine ⟨candidate, candidateIncident, ?_⟩
    apply fragmentEndpoint_corresponds_of_key occurrence removed
      attachment empty nodesExact sourceEndpoint candidate
    · exact
        ConcreteDiagram.incident_port_required _ pattern.val.diagram
          pattern.property.diagram source sourceEndpoint
            (by simpa [] using sourceIncident)
    · exact sameKey
  revert endpoint
  refine Fin.addCases ?_ ?_ wire
  · intro retained endpoint member
    unfold ConcreteSpliceAttachment.diagram
      ConcreteSpliceAttachment.wireTable at member
    simp only [ConcreteSpliceAttachment.hostWire,
      Fin.addCases_left] at member
    rcases List.mem_append.mp member with retainedMember | generatedMember
    · rcases List.mem_map.mp retainedMember with
        ⟨sourceEndpoint, sourceIncident, rfl⟩
      have hostIncident :=
        (Removal.diagramEndpoint_mem_iff occurrence retained
          sourceEndpoint).mp sourceIncident
      refine
        ⟨Removal.sourceEndpoint occurrence sourceEndpoint, ?_, ?_⟩
      · change
          Removal.sourceEndpoint occurrence sourceEndpoint ∈
            (host.val.wires
              (wireEquiv occurrence removed attachment wiresExact
                (attachment.hostWire retained))).endpoints
        rw [wireEquiv_hostWire occurrence removed attachment
          wiresExact]
        exact hostIncident
      · apply hostEndpoint_corresponds occurrence removed
          attachment empty regionsExact nodesExact sourceEndpoint
        exact
          ConcreteDiagram.incident_port_required _ removed.complement.val
            removed.complement.property retained sourceEndpoint sourceIncident
    · exact generatedCase (attachment.hostWire retained) endpoint
        generatedMember
  · intro fresh endpoint member
    unfold ConcreteSpliceAttachment.diagram
      ConcreteSpliceAttachment.wireTable at member
    simp only [ConcreteSpliceAttachment.freshWire,
      Fin.addCases_right] at member
    exact generatedCase (attachment.freshWire fresh) endpoint member

private theorem occurrenceEndpoint_backward_selected
    (occurrence : Occurrence pattern host)
    (nodesExact : NodesExact occurrence)
    (hostWire : host.val.WireId)
    (candidate : CEndpoint host.val.nodeCount)
    (incident : candidate ∈ (host.val.wires hostWire).endpoints)
    (selected : candidate.node ∈ occurrence.toSelection.allNodes) :
    ∃ sourceWire : pattern.val.diagram.WireId,
      ∃ sourceEndpoint : CEndpoint pattern.val.diagram.nodeCount,
        sourceEndpoint ∈
            (pattern.val.diagram.wires sourceWire).endpoints ∧
          occurrence.wireMap sourceWire = hostWire ∧
          mappedOccurrenceEndpointKey occurrence.nodeMap sourceEndpoint =
            occurrenceEndpointKey candidate := by
  let sourceNode := Classical.choose ((nodesExact candidate.node).mp selected)
  have sourceNodeMap :
      occurrence.nodeMap sourceNode = candidate.node :=
    Classical.choose_spec ((nodesExact candidate.node).mp selected)
  have nodeCorresponds := occurrence.node_correspondence sourceNode
  have candidateRequired :=
    ConcreteDiagram.incident_port_required _ host.val host.property
      hostWire candidate incident
  cases sourceData : pattern.val.diagram.nodes sourceNode with
  | atom region args =>
      simp [OccurrenceNodeCorresponds, sourceData] at nodeCorresponds
      have hostData :
          host.val.nodes candidate.node =
            .atom (occurrence.regionMap region) args := by
        rw [← sourceNodeMap]
        exact nodeCorresponds
      have sourceRequired :
          candidate.port ∈ pattern.val.diagram.requiredPorts sourceNode := by
        simpa [ConcreteDiagram.requiredPorts, sourceData, hostData] using
          candidateRequired
      obtain ⟨sourceWire, owner⟩ :=
        ConcreteDiagram.endpointOwner?_complete _ pattern.val.diagram
          pattern.property.diagram sourceNode candidate.port sourceRequired
      let sourceEndpoint :
          CEndpoint pattern.val.diagram.nodeCount :=
        ⟨sourceNode, candidate.port⟩
      have sourceIncident :
          sourceEndpoint ∈
            (pattern.val.diagram.wires sourceWire).endpoints :=
        ConcreteDiagram.endpointOwner?_incident pattern.val.diagram
          sourceEndpoint sourceWire owner
      rcases occurrenceEndpoint_forward occurrence sourceWire sourceEndpoint
          sourceIncident with
        ⟨mappedCandidate, mappedIncident, sameKey⟩
      have mappedCandidateEq : mappedCandidate = candidate := by
        rcases mappedCandidate with ⟨mappedNode, mappedPort⟩
        rcases candidate with ⟨candidateNode, candidatePort⟩
        simp only [sourceEndpoint, mappedOccurrenceEndpointKey,
          occurrenceEndpointKey] at sameKey
        have mappedNodeEq :
            mappedNode = candidateNode :=
          (congrArg Prod.fst sameKey).symm.trans sourceNodeMap
        have portKey := congrArg Prod.snd sameKey
        subst mappedNode
        cases candidatePort <;> cases mappedPort <;>
          simp_all [OccurrencePort.ofConcrete,
            ConcreteDiagram.requiredPorts, sourceData]
      have mappedOwner :=
        ConcreteDiagram.endpointOwner?_eq_of_incident _ host.val host.property
          mappedCandidate.node mappedCandidate.port
          (ConcreteDiagram.incident_port_required _ host.val host.property
            (occurrence.wireMap sourceWire) mappedCandidate mappedIncident)
          (occurrence.wireMap sourceWire) mappedIncident
      have candidateOwner :=
        ConcreteDiagram.endpointOwner?_eq_of_incident _ host.val host.property
          candidate.node candidate.port candidateRequired hostWire incident
      rw [mappedCandidateEq] at mappedOwner
      have wireEquality :
          occurrence.wireMap sourceWire = hostWire :=
        Option.some.inj (mappedOwner.symm.trans candidateOwner)
      exact
        ⟨sourceWire, sourceEndpoint, sourceIncident, wireEquality,
          by
            simpa [sourceEndpoint, sourceNodeMap,
              mappedOccurrenceEndpointKey, occurrenceEndpointKey]⟩
  | ref region definition args =>
      simp [OccurrenceNodeCorresponds, sourceData] at nodeCorresponds
      have hostData :
          host.val.nodes candidate.node =
            .ref (occurrence.regionMap region) definition args := by
        rw [← sourceNodeMap]
        exact nodeCorresponds
      have sourceRequired :
          candidate.port ∈ pattern.val.diagram.requiredPorts sourceNode := by
        simpa [ConcreteDiagram.requiredPorts, sourceData, hostData] using
          candidateRequired
      obtain ⟨sourceWire, owner⟩ :=
        ConcreteDiagram.endpointOwner?_complete _ pattern.val.diagram
          pattern.property.diagram sourceNode candidate.port sourceRequired
      let sourceEndpoint :
          CEndpoint pattern.val.diagram.nodeCount :=
        ⟨sourceNode, candidate.port⟩
      have sourceIncident :
          sourceEndpoint ∈
            (pattern.val.diagram.wires sourceWire).endpoints :=
        ConcreteDiagram.endpointOwner?_incident pattern.val.diagram
          sourceEndpoint sourceWire owner
      rcases occurrenceEndpoint_forward occurrence sourceWire sourceEndpoint
          sourceIncident with
        ⟨mappedCandidate, mappedIncident, sameKey⟩
      have mappedCandidateEq : mappedCandidate = candidate := by
        rcases mappedCandidate with ⟨mappedNode, mappedPort⟩
        rcases candidate with ⟨candidateNode, candidatePort⟩
        simp only [sourceEndpoint, mappedOccurrenceEndpointKey,
          occurrenceEndpointKey] at sameKey
        have mappedNodeEq :
            mappedNode = candidateNode :=
          (congrArg Prod.fst sameKey).symm.trans sourceNodeMap
        have portKey := congrArg Prod.snd sameKey
        subst mappedNode
        cases candidatePort <;> cases mappedPort <;>
          simp_all [OccurrencePort.ofConcrete,
            ConcreteDiagram.requiredPorts, sourceData]
      have mappedOwner :=
        ConcreteDiagram.endpointOwner?_eq_of_incident _ host.val host.property
          mappedCandidate.node mappedCandidate.port
          (ConcreteDiagram.incident_port_required _ host.val host.property
            (occurrence.wireMap sourceWire) mappedCandidate mappedIncident)
          (occurrence.wireMap sourceWire) mappedIncident
      have candidateOwner :=
        ConcreteDiagram.endpointOwner?_eq_of_incident _ host.val host.property
          candidate.node candidate.port candidateRequired hostWire incident
      rw [mappedCandidateEq] at mappedOwner
      have wireEquality :
          occurrence.wireMap sourceWire = hostWire :=
        Option.some.inj (mappedOwner.symm.trans candidateOwner)
      exact
        ⟨sourceWire, sourceEndpoint, sourceIncident, wireEquality,
          by
            simpa [sourceEndpoint, sourceNodeMap,
              mappedOccurrenceEndpointKey, occurrenceEndpointKey]⟩
  | identity region sig arity =>
      simp [OccurrenceNodeCorresponds, sourceData] at nodeCorresponds
      have hostData :
          host.val.nodes candidate.node =
            .identity (occurrence.regionMap region) sig arity := by
        rw [← sourceNodeMap]
        exact nodeCorresponds
      have hostIncidentWire :
          hostWire ∈ host.val.identityIncidentWires candidate.node :=
        (ConcreteDiagram.mem_identityIncidentWires host.val candidate.node
          hostWire).mpr ⟨candidate, incident, rfl⟩
      have hostOwner :
          hostWire ∈ host.val.identityOwners candidate.node arity :=
        (ConcreteDiagram.mem_identityIncidentWires_iff_mem_identityOwners
          _ host.val host.property candidate.node
          (occurrence.regionMap region) sig arity hostData hostWire).mp
            hostIncidentWire
      have mappedOwner :
          hostWire ∈
            (pattern.val.diagram.identityOwners sourceNode arity).map
              occurrence.wireMap := by
        have permuted :=
          occurrence.identityIncidence_permuted sourceNode region sig arity
            sourceData
        rw [sourceNodeMap] at permuted
        exact permuted.mem_iff.mpr hostOwner
      rcases List.mem_map.mp mappedOwner with
        ⟨sourceWire, sourceOwner, wireEquality⟩
      unfold ConcreteDiagram.identityOwners at sourceOwner
      rcases List.mem_filterMap.mp sourceOwner with
        ⟨sourceIndex, sourceIndexMember, owner⟩
      let sourceEndpoint :
          CEndpoint pattern.val.diagram.nodeCount :=
        ⟨sourceNode, .identity sourceIndex⟩
      have sourceIncident :
          sourceEndpoint ∈
            (pattern.val.diagram.wires sourceWire).endpoints :=
        ConcreteDiagram.endpointOwner?_incident pattern.val.diagram
          sourceEndpoint sourceWire owner
      have candidateIdentity :
          ∃ candidateIndex, candidate.port = .identity candidateIndex := by
        obtain ⟨candidateIndex, bound, candidatePort⟩ := by
          simpa [ConcreteDiagram.requiredPorts, hostData] using
            candidateRequired
        exact ⟨candidateIndex, candidatePort.symm⟩
      rcases candidateIdentity with ⟨candidateIndex, candidatePort⟩
      exact
        ⟨sourceWire, sourceEndpoint, sourceIncident, wireEquality,
          by
            unfold mappedOccurrenceEndpointKey occurrenceEndpointKey
            simp [sourceEndpoint, sourceNodeMap, candidatePort,
              OccurrencePort.ofConcrete]⟩

/-- Selected host incidences invert the positional occurrence endpoint map. -/
private theorem occurrenceEndpoint_backward_selected_positional
    (occurrence : Occurrence pattern host)
    (nodesExact : NodesExact occurrence)
    (hostWire : host.val.WireId)
    (candidate : CEndpoint host.val.nodeCount)
    (incident : candidate ∈ (host.val.wires hostWire).endpoints)
    (selected : candidate.node ∈ occurrence.toSelection.allNodes) :
    ∃ sourceWire : pattern.val.diagram.WireId,
      ∃ sourceEndpoint : CEndpoint pattern.val.diagram.nodeCount,
        sourceEndpoint ∈
            (pattern.val.diagram.wires sourceWire).endpoints ∧
          occurrence.wireMap sourceWire = hostWire ∧
          occurrence.endpointMapForNode sourceEndpoint =
            candidate := by
  let sourceNode := Classical.choose ((nodesExact candidate.node).mp selected)
  have sourceNodeMap : occurrence.nodeMap sourceNode = candidate.node :=
    Classical.choose_spec ((nodesExact candidate.node).mp selected)
  have candidateRequired :=
    ConcreteDiagram.incident_port_required _ host.val host.property
      hostWire candidate incident
  cases sourceData : pattern.val.diagram.nodes sourceNode with
  | atom region args =>
      rcases occurrenceEndpoint_backward_selected occurrence nodesExact
          hostWire candidate incident selected with
        ⟨sourceWire, sourceEndpoint, sourceIncident, wireExact, keyExact⟩
      have endpointNode : sourceEndpoint.node = sourceNode := by
        apply occurrence.nodeMap_injective
        exact (congrArg Prod.fst keyExact).trans sourceNodeMap.symm
      rcases sourceEndpoint with ⟨sourceEndpointNode, sourcePort⟩
      simp only at endpointNode
      subst sourceEndpointNode
      refine ⟨sourceWire, ⟨sourceNode, sourcePort⟩, sourceIncident,
        wireExact, ?_⟩
      have sourceRequired :=
        ConcreteDiagram.incident_port_required _ pattern.val.diagram
          pattern.property.diagram sourceWire ⟨sourceNode, sourcePort⟩
            sourceIncident
      simp [ConcreteDiagram.requiredPorts, sourceData] at sourceRequired
      rcases candidate with ⟨candidateNode, candidatePort⟩
      simp only [mappedOccurrenceEndpointKey, occurrenceEndpointKey] at keyExact
      have portExact := congrArg Prod.snd keyExact
      simp [Occurrence.endpointMapForNode,
        Occurrence.portEquivForNode_atom occurrence sourceNode region args
          sourceData,
        sourceNodeMap]
      cases sourcePort <;> cases candidatePort <;>
        simp_all [OccurrencePort.ofConcrete]
  | ref region definition args =>
      rcases occurrenceEndpoint_backward_selected occurrence nodesExact
          hostWire candidate incident selected with
        ⟨sourceWire, sourceEndpoint, sourceIncident, wireExact, keyExact⟩
      have endpointNode : sourceEndpoint.node = sourceNode := by
        apply occurrence.nodeMap_injective
        exact (congrArg Prod.fst keyExact).trans sourceNodeMap.symm
      rcases sourceEndpoint with ⟨sourceEndpointNode, sourcePort⟩
      simp only at endpointNode
      subst sourceEndpointNode
      refine ⟨sourceWire, ⟨sourceNode, sourcePort⟩, sourceIncident,
        wireExact, ?_⟩
      have sourceRequired :=
        ConcreteDiagram.incident_port_required _ pattern.val.diagram
          pattern.property.diagram sourceWire ⟨sourceNode, sourcePort⟩
            sourceIncident
      simp [ConcreteDiagram.requiredPorts, sourceData] at sourceRequired
      rcases candidate with ⟨candidateNode, candidatePort⟩
      simp only [mappedOccurrenceEndpointKey, occurrenceEndpointKey] at keyExact
      have portExact := congrArg Prod.snd keyExact
      simp [Occurrence.endpointMapForNode,
        Occurrence.portEquivForNode_ref occurrence sourceNode region definition
          args sourceData,
        sourceNodeMap]
      cases sourcePort <;> cases candidatePort <;>
        simp_all [OccurrencePort.ofConcrete]
  | identity region sig arity =>
      have nodeCorresponds := occurrence.node_correspondence sourceNode
      simp [OccurrenceNodeCorresponds, sourceData] at nodeCorresponds
      have hostData :
          host.val.nodes candidate.node =
            .identity (occurrence.regionMap region) sig arity := by
        rw [← sourceNodeMap]
        exact nodeCorresponds
      obtain ⟨candidateIndex, candidateBound, candidatePort⟩ := by
        simpa [ConcreteDiagram.requiredPorts, hostData] using
          candidateRequired
      have targetOwner :=
        ConcreteDiagram.endpointOwner?_eq_of_incident _ host.val host.property
          candidate.node candidate.port candidateRequired hostWire incident
      have targetOwnerAtIndex :
          host.val.endpointOwner?
              ⟨occurrence.nodeMap sourceNode,
                .identity candidateIndex⟩ = some hostWire := by
        simpa [sourceNodeMap, candidatePort] using targetOwner
      let targetIndex : Fin arity := ⟨candidateIndex, candidateBound⟩
      rcases occurrence.identityPortEquiv_symm_owner sourceNode region sig
          arity sourceData targetIndex hostWire targetOwnerAtIndex with
        ⟨sourceWire, sourceOwner, wireExact⟩
      let sourceIndex :=
        (occurrence.identityPortEquiv sourceNode region sig arity sourceData).symm
          targetIndex
      let sourceEndpoint : CEndpoint pattern.val.diagram.nodeCount :=
        ⟨sourceNode, .identity sourceIndex.val⟩
      have sourceIncident :
          sourceEndpoint ∈
            (pattern.val.diagram.wires sourceWire).endpoints :=
        ConcreteDiagram.endpointOwner?_incident pattern.val.diagram
          sourceEndpoint sourceWire (by simpa [sourceEndpoint, sourceIndex]
            using sourceOwner)
      refine ⟨sourceWire, sourceEndpoint, sourceIncident, wireExact, ?_⟩
      have forwardIndex :
          occurrence.identityPortEquiv sourceNode region sig arity sourceData
              sourceIndex = targetIndex :=
        Data.Finite.FiniteEquiv.apply_symm_apply
          (occurrence.identityPortEquiv sourceNode region sig arity sourceData)
          targetIndex
      have candidateExact :
          candidate = ⟨candidate.node, .identity candidateIndex⟩ := by
        rcases candidate with ⟨candidateNode, candidatePortValue⟩
        simp only at candidatePort ⊢
        subst candidatePortValue
        rfl
      rw [candidateExact]
      simp [sourceEndpoint, Occurrence.endpointMapForNode,
        Occurrence.portEquivForNode_identity occurrence sourceNode region sig
          arity sourceData,
        Occurrence.identityCPortEquiv,
        sourceIndex.isLt, forwardIndex, sourceNodeMap, targetIndex]

private theorem generatedEndpoint_mem_diagram
    (attachment : ConcreteSpliceAttachment base site fragment)
    (wire : attachment.diagram.WireId)
    (endpoint : CEndpoint attachment.diagram.nodeCount)
    (member : endpoint ∈ attachment.generatedEndpoints wire) :
    endpoint ∈ (attachment.diagram.wires wire).endpoints := by
  revert endpoint
  refine Fin.addCases ?_ ?_ wire
  · intro retained endpoint member
    unfold ConcreteSpliceAttachment.diagram
      ConcreteSpliceAttachment.wireTable
    simp only [Fin.addCases_left]
    exact List.mem_append_right _ member
  · intro fresh endpoint member
    unfold ConcreteSpliceAttachment.diagram
      ConcreteSpliceAttachment.wireTable
    simp only [Fin.addCases_right]
    exact member

private theorem unselected_incident_wire_not_internal
    (occurrence : Occurrence pattern host)
    (nodesExact : NodesExact occurrence)
    (wiresExact : WiresExact occurrence)
    (wire : host.val.WireId)
    (candidate : CEndpoint host.val.nodeCount)
    (incident : candidate ∈ (host.val.wires wire).endpoints)
    (unselected : candidate.node ∉ occurrence.toSelection.allNodes) :
    wire ∉ occurrence.toSelection.internalWires := by
  intro internal
  rcases (wiresExact wire).mp internal with
    ⟨source, nonboundary, sourceMap⟩
  have actualMember :
      occurrenceEndpointKey candidate ∈
        (host.val.wires (occurrence.wireMap source)).endpoints.map
          occurrenceEndpointKey := by
    apply List.mem_map.mpr
    exact ⟨candidate, by simpa [sourceMap] using incident, rfl⟩
  have expectedMember :=
    (occurrence.internalEndpoints_exact source nonboundary).mem_iff.mpr
      actualMember
  rcases List.mem_map.mp expectedMember with
    ⟨sourceEndpoint, _, sameKey⟩
  apply unselected
  apply (nodesExact candidate.node).mpr
  refine ⟨sourceEndpoint.node, ?_⟩
  exact congrArg Prod.fst sameKey

/-- Exact per-wire incidence preservation by the splice-wide endpoint map. -/
private theorem endpointEquiv_mem_iff
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (accepted :
      reconstructionAttachment? occurrence removed = some attachment)
    (empty : attachment.identityRequests = [])
    (nodesExact : NodesExact occurrence)
    (wiresExact : WiresExact occurrence)
    (wire : attachment.diagram.WireId)
    (endpoint : CEndpoint attachment.diagram.nodeCount) :
    endpointEquiv occurrence removed attachment empty nodesExact endpoint ∈
          (host.val.wires
            (wireEquiv occurrence removed attachment wiresExact wire)).endpoints ↔
      endpoint ∈ (attachment.diagram.wires wire).endpoints := by
  constructor
  · intro incident
    let candidate :=
      endpointEquiv occurrence removed attachment empty nodesExact endpoint
    by_cases selected :
        candidate.node ∈ occurrence.toSelection.allNodes
    · rcases occurrenceEndpoint_backward_selected_positional occurrence
          nodesExact
          (wireEquiv occurrence removed attachment wiresExact wire)
          candidate incident selected with
        ⟨sourceWire, sourceEndpoint, sourceIncident, sourceWireMap,
          sourceEndpointMap⟩
      have mappedWire : attachment.fragmentWire sourceWire = wire := by
        apply (wireEquiv occurrence removed attachment wiresExact).injective
        rw [wireEquiv_fragmentWire occurrence removed attachment accepted
          wiresExact sourceWire]
        exact sourceWireMap
      have generated := attachment.fragmentEndpoint_mem_generated empty
        sourceWire sourceEndpoint (by simpa [] using sourceIncident)
      rw [mappedWire] at generated
      have fragmentIncident := generatedEndpoint_mem_diagram attachment wire
        (attachment.fragmentEndpoint sourceEndpoint) generated
      have endpointExact :
          endpoint = attachment.fragmentEndpoint sourceEndpoint := by
        apply
          (endpointEquiv occurrence removed attachment empty nodesExact).injective
        rw [endpointEquiv_fragmentEndpoint occurrence removed attachment empty
          nodesExact]
        exact sourceEndpointMap.symm
      rwa [endpointExact]
    · let mappedHostWire :=
        wireEquiv occurrence removed attachment wiresExact wire
      have notInternal :
          mappedHostWire ∉ occurrence.toSelection.internalWires :=
        unselected_incident_wire_not_internal occurrence nodesExact wiresExact
          mappedHostWire candidate incident selected
      have retainedWire : mappedHostWire ∈ Removal.wires occurrence :=
        retainedWire_of_not_internal occurrence notInternal
      let baseWire :=
        Removal.wireIndex occurrence mappedHostWire retainedWire
      have baseWireSource :
          Removal.sourceWire occurrence baseWire = mappedHostWire :=
        Removal.sourceWire_wireIndex occurrence mappedHostWire retainedWire
      have allocatedWire : attachment.hostWire baseWire = wire := by
        apply (wireEquiv occurrence removed attachment wiresExact).injective
        rw [wireEquiv_hostWire occurrence removed attachment wiresExact]
        exact baseWireSource
      have retainedNode : candidate.node ∈ Removal.nodes occurrence :=
        retainedNode_of_not_selected occurrence selected
      let sourceEndpoint : CEndpoint removed.complement.val.nodeCount :=
        ⟨Removal.nodeIndex occurrence candidate.node retainedNode,
          candidate.port⟩
      have sourceEndpointMap :
          Removal.sourceEndpoint occurrence sourceEndpoint = candidate :=
        Removal.sourceEndpoint_index occurrence candidate retainedNode
      have sourceIncident :
          sourceEndpoint ∈
            (removed.complement.val.wires baseWire).endpoints := by
        apply (Removal.diagramEndpoint_mem_iff occurrence baseWire
          sourceEndpoint).mpr
        rw [sourceEndpointMap, baseWireSource]
        exact incident
      have allocatedIncident :
          attachment.hostEndpoint sourceEndpoint ∈
            (attachment.diagram.wires
              (attachment.hostWire baseWire)).endpoints := by
        unfold ConcreteSpliceAttachment.diagram
          ConcreteSpliceAttachment.wireTable
        simp only [ConcreteSpliceAttachment.hostWire, Fin.addCases_left]
        exact List.mem_append_left _
          (List.mem_map.mpr ⟨sourceEndpoint, sourceIncident, rfl⟩)
      rw [allocatedWire] at allocatedIncident
      have endpointExact :
          endpoint = attachment.hostEndpoint sourceEndpoint := by
        apply
          (endpointEquiv occurrence removed attachment empty nodesExact).injective
        rw [endpointEquiv_hostEndpoint occurrence removed attachment empty
          nodesExact]
        exact sourceEndpointMap.symm
      rwa [endpointExact]
  · exact endpointEquiv_mem occurrence removed attachment accepted empty
      nodesExact wiresExact wire endpoint

private theorem endpointEquiv_corresponds
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (empty : attachment.identityRequests = [])
    (regionsExact : RegionsExact occurrence)
    (nodesExact : NodesExact occurrence)
    (wire : attachment.diagram.WireId)
    (endpoint : CEndpoint attachment.diagram.nodeCount)
    (member : endpoint ∈ (attachment.diagram.wires wire).endpoints) :
    PortCorresponds attachment.diagram host.val
      (nodeEquiv occurrence removed attachment empty nodesExact)
      endpoint
      (endpointEquiv occurrence removed attachment empty nodesExact endpoint) := by
  have generatedCase :
      ∀ candidateWire generatedEndpoint,
        generatedEndpoint ∈ attachment.generatedEndpoints candidateWire →
          PortCorresponds attachment.diagram host.val
            (nodeEquiv occurrence removed attachment empty nodesExact)
            generatedEndpoint
            (endpointEquiv occurrence removed attachment empty nodesExact
              generatedEndpoint) := by
    intro candidateWire generatedEndpoint generatedMember
    rcases attachment.generatedEndpoint_origin empty candidateWire
        generatedEndpoint generatedMember with
      ⟨sourceWire, sourceEndpoint, sourceIncident, mappedWire,
        mappedEndpoint⟩
    subst generatedEndpoint
    rw [endpointEquiv_fragmentEndpoint occurrence removed attachment empty
      nodesExact]
    apply fragmentEndpoint_corresponds_of_key occurrence removed attachment
      empty nodesExact sourceEndpoint
      (occurrence.endpointMapForNode sourceEndpoint)
    · exact
        ConcreteDiagram.incident_port_required _ pattern.val.diagram
          pattern.property.diagram sourceWire sourceEndpoint
            (by simpa [] using sourceIncident)
    · exact occurrenceEndpointMap_key occurrence sourceWire sourceEndpoint
        (by simpa [] using sourceIncident)
  revert endpoint
  refine Fin.addCases ?_ ?_ wire
  · intro retained endpoint member
    unfold ConcreteSpliceAttachment.diagram
      ConcreteSpliceAttachment.wireTable at member
    simp only [ConcreteSpliceAttachment.hostWire,
      Fin.addCases_left] at member
    rcases List.mem_append.mp member with retainedMember | generatedMember
    · rcases List.mem_map.mp retainedMember with
        ⟨sourceEndpoint, sourceIncident, rfl⟩
      rw [endpointEquiv_hostEndpoint occurrence removed attachment empty
        nodesExact]
      apply hostEndpoint_corresponds occurrence removed attachment empty
        regionsExact nodesExact sourceEndpoint
      exact
        ConcreteDiagram.incident_port_required _ removed.complement.val
          removed.complement.property retained sourceEndpoint sourceIncident
    · exact generatedCase (attachment.hostWire retained) endpoint
        generatedMember
  · intro fresh endpoint member
    unfold ConcreteSpliceAttachment.diagram
      ConcreteSpliceAttachment.wireTable at member
    simp only [ConcreteSpliceAttachment.freshWire,
      Fin.addCases_right] at member
    exact generatedCase (attachment.freshWire fresh) endpoint member

/-- Total construction-owned endpoint equivalence for one reconstructed wire. -/
private noncomputable def endpointFiberEquiv
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (accepted :
      reconstructionAttachment? occurrence removed = some attachment)
    (empty : attachment.identityRequests = [])
    (regionsExact : RegionsExact occurrence)
    (nodesExact : NodesExact occurrence)
    (wiresExact : WiresExact occurrence)
    (wire : attachment.diagram.WireId) :
    ConcreteIso.EndpointFiberEquiv
      (nodeEquiv occurrence removed attachment empty nodesExact)
      (wireEquiv occurrence removed attachment wiresExact) wire where
  equivalence :=
    { toFun := fun endpoint =>
        ⟨endpointEquiv occurrence removed attachment empty nodesExact
            endpoint.1,
          endpointEquiv_mem occurrence removed attachment accepted empty
            nodesExact wiresExact wire endpoint.1 endpoint.2⟩
      invFun := fun candidate =>
        let source :=
          (endpointEquiv occurrence removed attachment empty nodesExact).symm
            candidate.1
        ⟨source, (endpointEquiv_mem_iff occurrence removed attachment
          accepted empty nodesExact wiresExact wire source).mp (by
            have mapped :
                endpointEquiv occurrence removed attachment empty nodesExact
                    source = candidate.1 :=
              Data.Finite.FiniteEquiv.apply_symm_apply
                (endpointEquiv occurrence removed attachment empty nodesExact)
                candidate.1
            rw [mapped]
            exact candidate.2)⟩
      left_inv := by
        intro endpoint
        apply Subtype.ext
        exact Data.Finite.FiniteEquiv.symm_apply_apply
          (endpointEquiv occurrence removed attachment empty nodesExact)
          endpoint.1
      right_inv := by
        intro candidate
        apply Subtype.ext
        exact Data.Finite.FiniteEquiv.apply_symm_apply
          (endpointEquiv occurrence removed attachment empty nodesExact)
          candidate.1 }
  corresponds := by
    intro endpoint
    exact endpointEquiv_corresponds occurrence removed attachment empty
      regionsExact nodesExact wire endpoint.1 endpoint.2

/-- Every source endpoint has an exact reconstructed endpoint correspondence. -/
theorem endpointBackward_exact
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (accepted :
      reconstructionAttachment? occurrence removed =
        some attachment)
    (empty : attachment.identityRequests = [])
    (regionsExact : RegionsExact occurrence)
    (nodesExact : NodesExact occurrence)
    (wiresExact : WiresExact occurrence)
    (wire : attachment.diagram.WireId)
    (candidate : CEndpoint host.val.nodeCount)
    (incident :
      candidate ∈
        (host.val.wires
          (wireEquiv occurrence removed attachment wiresExact
            wire)).endpoints) :
    ∃ endpoint,
      endpoint ∈ (attachment.diagram.wires wire).endpoints ∧
        PortCorresponds attachment.diagram host.val
          (nodeEquiv occurrence removed attachment empty nodesExact)
          endpoint candidate := by
  by_cases selected :
      candidate.node ∈ occurrence.toSelection.allNodes
  · rcases occurrenceEndpoint_backward_selected occurrence nodesExact
        (wireEquiv occurrence removed attachment wiresExact wire)
        candidate incident selected with
      ⟨sourceWire, sourceEndpoint, sourceIncident, sourceWireMap, sameKey⟩
    have mappedWire :
        attachment.fragmentWire sourceWire = wire := by
      apply
        (wireEquiv occurrence removed attachment wiresExact).injective
      rw [wireEquiv_fragmentWire occurrence removed attachment
        accepted wiresExact sourceWire]
      exact sourceWireMap
    have generatedMember :=
      attachment.fragmentEndpoint_mem_generated empty sourceWire
        sourceEndpoint (by
          simpa [] using sourceIncident)
    rw [mappedWire] at generatedMember
    refine
      ⟨attachment.fragmentEndpoint sourceEndpoint,
        generatedEndpoint_mem_diagram attachment wire
          (attachment.fragmentEndpoint sourceEndpoint) generatedMember, ?_⟩
    apply fragmentEndpoint_corresponds_of_key occurrence removed
      attachment empty nodesExact sourceEndpoint candidate
    · exact
        ConcreteDiagram.incident_port_required _ pattern.val.diagram
          pattern.property.diagram sourceWire sourceEndpoint sourceIncident
    · exact sameKey
  · let mappedHostWire :=
      wireEquiv occurrence removed attachment wiresExact wire
    have notInternal :
        mappedHostWire ∉ occurrence.toSelection.internalWires :=
      unselected_incident_wire_not_internal occurrence nodesExact wiresExact
        mappedHostWire candidate incident selected
    have retainedWire : mappedHostWire ∈ Removal.wires occurrence :=
      retainedWire_of_not_internal occurrence notInternal
    let baseWire :=
      Removal.wireIndex occurrence mappedHostWire retainedWire
    have baseWireSource :
        Removal.sourceWire occurrence baseWire = mappedHostWire :=
      Removal.sourceWire_wireIndex occurrence mappedHostWire retainedWire
    have allocatedWire :
        attachment.hostWire baseWire = wire := by
      apply
        (wireEquiv occurrence removed attachment wiresExact).injective
      rw [wireEquiv_hostWire occurrence removed attachment
        wiresExact]
      exact baseWireSource
    have retainedNode : candidate.node ∈ Removal.nodes occurrence :=
      retainedNode_of_not_selected occurrence selected
    let sourceEndpoint :
        CEndpoint removed.complement.val.nodeCount :=
      ⟨Removal.nodeIndex occurrence candidate.node retainedNode,
        candidate.port⟩
    have sourceEndpointMap :
        Removal.sourceEndpoint occurrence sourceEndpoint = candidate :=
      Removal.sourceEndpoint_index occurrence candidate retainedNode
    have sourceIncident :
        sourceEndpoint ∈
          (removed.complement.val.wires baseWire).endpoints := by
      apply (Removal.diagramEndpoint_mem_iff occurrence baseWire
        sourceEndpoint).mpr
      rw [sourceEndpointMap, baseWireSource]
      exact incident
    have generatedMember :
        attachment.hostEndpoint sourceEndpoint ∈
          (attachment.diagram.wires
            (attachment.hostWire baseWire)).endpoints := by
      unfold ConcreteSpliceAttachment.diagram
        ConcreteSpliceAttachment.wireTable
      simp only [ConcreteSpliceAttachment.hostWire, Fin.addCases_left]
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨sourceEndpoint, sourceIncident, rfl⟩
    rw [allocatedWire] at generatedMember
    refine
      ⟨attachment.hostEndpoint sourceEndpoint, generatedMember, ?_⟩
    simpa [sourceEndpointMap] using
      (hostEndpoint_corresponds occurrence removed attachment
        empty regionsExact nodesExact sourceEndpoint
        (ConcreteDiagram.incident_port_required _ removed.complement.val
          removed.complement.property baseWire sourceEndpoint
            sourceIncident))

/--
An exact occurrence, partial removal, and acceptance of the reconstruction
attachment reconstruct the raw host diagram before any normalization.
-/
noncomputable def extract_splice_iso
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (accepted :
      reconstructionAttachment? occurrence removed =
        some attachment) :
    ConcreteIso attachment.diagram host.val := by
  have regionsExact : RegionsExact occurrence :=
    fun region =>
      occurrence.mem_toSelection_allRegions_iff_image region
  have nodesExact : NodesExact occurrence :=
    fun node =>
      occurrence.mem_toSelection_allNodes_iff_image node
  have wiresExact : WiresExact occurrence :=
    fun wire =>
      occurrence.mem_toSelection_internalWires_iff_image wire
  have empty :
      attachment.identityRequests = [] :=
    identityRequests_eq_nil occurrence removed attachment accepted
  apply ConcreteIso.ofEquivs
    (regionEquiv occurrence removed attachment regionsExact)
    (nodeEquiv occurrence removed attachment empty nodesExact)
    (wireEquiv occurrence removed attachment wiresExact)
  · change
      regionEquiv occurrence removed attachment regionsExact
          (attachment.hostRegion removed.complement.val.root) =
        host.val.root
    rw [regionEquiv_hostRegion occurrence removed attachment regionsExact]
    exact Removal.sourceRegion_regionIndex occurrence host.val.root
      (Removal.host_root_mem occurrence)
  · exact regionTable_exact occurrence removed attachment regionsExact
  · exact nodeTable_exact occurrence removed attachment empty regionsExact
      nodesExact
  · exact wireSignature_exact occurrence removed attachment wiresExact
  · exact wireScope_exact occurrence removed attachment regionsExact
      wiresExact
  · exact endpointFiberEquiv occurrence removed attachment accepted empty
      regionsExact nodesExact wiresExact

/-- Compatibility surface for consumers that still sequence optional checks. -/
def extract_splice_iso?
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence)
    (attachment :
      ConcreteSpliceAttachment
        removed.complement removed.site pattern)
    (accepted :
      reconstructionAttachment? occurrence removed =
        some attachment) :
    Option (ConcreteIso attachment.diagram host.val) := by
  have regionsExact : RegionsExact occurrence :=
    fun region =>
      occurrence.mem_toSelection_allRegions_iff_image region
  have nodesExact : NodesExact occurrence :=
    fun node =>
      occurrence.mem_toSelection_allNodes_iff_image node
  have wiresExact : WiresExact occurrence :=
    fun wire =>
      occurrence.mem_toSelection_internalWires_iff_image wire
  have empty : attachment.identityRequests = [] :=
    identityRequests_eq_nil occurrence removed attachment accepted
  exact ConcreteIso.checkEquivs? attachment.diagram host.val
    (regionEquiv occurrence removed attachment regionsExact)
    (nodeEquiv occurrence removed attachment empty nodesExact)
    (wireEquiv occurrence removed attachment wiresExact)

end Reconstruction

end VisualProof
