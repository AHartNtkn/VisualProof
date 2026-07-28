import VisualProof.Diagram.Concrete.Subgraph.Splice

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

private theorem attachment_ext
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {site : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (left right :
      @ConcreteSpliceAttachment definitions pattern host occurrence
        site fragment)
    (sameTarget : left.target = right.target)
    (sameRequests : left.identityRequests = right.identityRequests) :
    left = right := by
  cases left
  cases right
  simp_all

/-- A validated reconstruction attachment retains the generated original target. -/
theorem attachment_target
    (occurrence : Occurrence pattern host)
    (compiled : ExtractionCompilation occurrence)
    (removed : RemovalResult occurrence)
    (attachment : ConcreteSpliceAttachment removed compiled.checked)
    (accepted :
      reconstructionAttachment? occurrence compiled removed =
        some attachment)
    (position : Fin compiled.checked.val.boundary.length) :
    attachment.target position =
      Removal.wireIndex occurrence
        (occurrence.wireMap (occurrence.boundarySourceAt position))
        (Removal.boundarySource_retained occurrence position) := by
  unfold reconstructionAttachment? at accepted
  exact congrFun
    (checkConcreteSpliceAttachment_target
      removed compiled.checked _
      attachment accepted)
    position

/-- Every generated reconstruction position targets its source-class representative. -/
theorem attachment_representative_eq_target
    (occurrence : Occurrence pattern host)
    (compiled : ExtractionCompilation occurrence)
    (removed : RemovalResult occurrence)
    (attachment : ConcreteSpliceAttachment removed compiled.checked)
    (accepted :
      reconstructionAttachment? occurrence compiled removed =
        some attachment)
    (position : Fin compiled.checked.val.boundary.length) :
    attachment.representativeTarget
        (compiled.checked.val.boundary.get position)
        (List.get_mem compiled.checked.val.boundary position) =
      attachment.target position := by
  let source := compiled.checked.val.boundary.get position
  let representative :=
    attachment.representativePosition source
      (List.get_mem compiled.checked.val.boundary position)
  have retrieved :
      compiled.checked.val.boundary.get representative = source :=
    DenseList.get_index _ _ _
  have sources :
      occurrence.boundarySourceAt representative =
        occurrence.boundarySourceAt position := by
    simpa only [Occurrence.boundarySourceAt] using retrieved
  change attachment.target representative = attachment.target position
  rw [attachment_target occurrence compiled removed attachment accepted,
    attachment_target occurrence compiled removed attachment accepted]
  apply Fin.ext
  simpa only [sources]

/-- Original reconstruction aliases request no inserted identity nodes. -/
theorem identityRequests_eq_nil
    (occurrence : Occurrence pattern host)
    (compiled : ExtractionCompilation occurrence)
    (removed : RemovalResult occurrence)
    (attachment : ConcreteSpliceAttachment removed compiled.checked)
    (accepted :
      reconstructionAttachment? occurrence compiled removed =
        some attachment) :
    attachment.identityRequests = [] := by
  rw [attachment.identityRequests_exact]
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro request member
  unfold computedIdentityRequests at member
  rw [List.mem_eraseDups, List.mem_filterMap] at member
  rcases member with ⟨position, _, emitted⟩
  change
    (if attachment.representativeTarget
          (compiled.checked.val.boundary.get position)
          (List.get_mem compiled.checked.val.boundary position) =
        attachment.target position then
      none
    else
      some
        { sig :=
            (compiled.checked.val.diagram.wires
              (compiled.checked.val.boundary.get position)).sig
          representative :=
            attachment.representativeTarget
              (compiled.checked.val.boundary.get position)
              (List.get_mem compiled.checked.val.boundary position)
          target := attachment.target position }) =
      some request at emitted
  rw [attachment_representative_eq_target occurrence compiled removed
    attachment accepted position] at emitted
  simp at emitted

/-- Selected nonroot regions occupy the fresh reconstruction summand. -/
def freshRegions (occurrence : Occurrence pattern host) :
    List pattern.val.RegionId :=
  pattern.val.regionsList.filter fun region =>
    decide (region ≠ pattern.val.root)

/-- The generated fragment's non-root allocation list is definitionally the selection list. -/
theorem fragmentRegions_eq_freshRegions
    (occurrence : Occurrence pattern host)
    (compiled : ExtractionCompilation occurrence)
    (removed : RemovalResult occurrence)
    (attachment : ConcreteSpliceAttachment removed compiled.checked) :
    attachment.fragmentRegions = freshRegions occurrence :=
  rfl

theorem freshRegions_nodup (occurrence : Occurrence pattern host) :
    (freshRegions occurrence).Nodup :=
  Data.Finite.allFin_nodup pattern.val.regionCount |>.filter _

private theorem retainedRegion_of_not_selected
    (occurrence : Occurrence pattern host)
    {region : host.val.RegionId}
    (outside : region ∉ occurrence.selection.regions) :
    region ∈ Removal.regions occurrence := by
  simp [Removal.regions, ConcreteDiagram.regionsList,
    Data.Finite.mem_allFin, outside]

private theorem freshRegion_of_selected_nonroot
    (occurrence : Occurrence pattern host)
    {region : host.val.RegionId}
    (selected : region ∈ occurrence.selection.regions)
    (nonroot : region ≠ occurrence.selection.root) :
    occurrence.regionInverse region selected ∈ freshRegions occurrence := by
  simp only [freshRegions, List.mem_filter]
  refine ⟨Data.Finite.mem_allFin _, decide_eq_true ?_⟩
  intro sourceRoot
  have mapped := occurrence.region_right_inverse region selected
  rw [sourceRoot, occurrence.root] at mapped
  exact nonroot mapped.symm

def regionForward
    (occurrence : Occurrence pattern host) :
    Fin ((Removal.regions occurrence).length +
      (freshRegions occurrence).length) →
      host.val.RegionId :=
  Fin.addCases
    (Removal.sourceRegion occurrence)
    (fun fresh =>
      occurrence.regionMap ((freshRegions occurrence).get fresh))

def regionBackward
    (occurrence : Occurrence pattern host)
    (region : host.val.RegionId) :
    Fin ((Removal.regions occurrence).length +
      (freshRegions occurrence).length) :=
  if selected : region ∈ occurrence.selection.regions then
    if root : region = occurrence.selection.root then
      Fin.castAdd (freshRegions occurrence).length
        (Removal.regionIndex occurrence region
          (root ▸ Removal.selected_root_mem occurrence))
    else
      Fin.natAdd (Removal.regions occurrence).length
        (DenseList.index (freshRegions occurrence)
          (occurrence.regionInverse region selected)
          (freshRegion_of_selected_nonroot occurrence selected root))
  else
    Fin.castAdd (freshRegions occurrence).length
      (Removal.regionIndex occurrence region
        (retainedRegion_of_not_selected occurrence selected))

/-- Generated retained/fresh region allocation is a finite equivalence to host IDs. -/
def regionEquiv
    (occurrence : Occurrence pattern host) :
    Data.Finite.FiniteEquiv
      (Fin ((Removal.regions occurrence).length +
        (freshRegions occurrence).length))
      host.val.RegionId where
  toFun := regionForward occurrence
  invFun := regionBackward occurrence
  left_inv := by
    intro allocated
    refine Fin.addCases ?_ ?_ allocated
    · intro retained
      have member :=
        List.get_mem (Removal.regions occurrence) retained
      have retainedCase := (List.mem_filter.mp member).2
      have retainedCase :
          Removal.sourceRegion occurrence retained ∉
              occurrence.selection.regions ∨
            Removal.sourceRegion occurrence retained =
              occurrence.selection.root :=
        of_decide_eq_true retainedCase
      rcases retainedCase with outside | root
      · simp [regionBackward, regionForward, outside,
          Removal.regionIndex_sourceRegion]
      · have selected :
            Removal.sourceRegion occurrence retained ∈
              occurrence.selection.regions := by
          rw [root]
          exact occurrence.selection.root_mem
        simp only [regionForward, Fin.addCases_left]
        change
          regionBackward occurrence
              (Removal.sourceRegion occurrence retained) =
            Fin.castAdd (freshRegions occurrence).length retained
        unfold regionBackward
        rw [dif_pos selected, dif_pos root]
        exact congrArg
          (Fin.castAdd (freshRegions occurrence).length)
          (Removal.regionIndex_sourceRegion occurrence retained)
    · intro fresh
      let source := (freshRegions occurrence).get fresh
      have sourceMember :
          source ∈ freshRegions occurrence :=
        List.get_mem _ fresh
      have sourceNonroot : source ≠ pattern.val.root :=
        of_decide_eq_true (List.mem_filter.mp sourceMember).2
      have mappedSelected :
          occurrence.regionMap source ∈ occurrence.selection.regions :=
        occurrence.region_mem source
      have mappedNonroot :
          occurrence.regionMap source ≠ occurrence.selection.root := by
        intro equality
        have sourceEquality : source = pattern.val.root :=
          occurrence.region_injective
            (equality.trans occurrence.root.symm)
        exact sourceNonroot sourceEquality
      have inverse :
          occurrence.regionInverse (occurrence.regionMap source)
            mappedSelected = source :=
        occurrence.region_left_inverse source
      simp only [regionForward, Fin.addCases_right]
      change
        regionBackward occurrence (occurrence.regionMap source) =
          Fin.natAdd (Removal.regions occurrence).length fresh
      unfold regionBackward
      rw [dif_pos mappedSelected, dif_neg mappedNonroot]
      apply congrArg (Fin.natAdd (Removal.regions occurrence).length)
      simpa only [inverse] using
        DenseList.index_get (freshRegions occurrence)
          (freshRegions_nodup occurrence) fresh
  right_inv := by
    intro region
    by_cases selected : region ∈ occurrence.selection.regions
    · by_cases root : region = occurrence.selection.root
      · subst region
        unfold regionBackward
        rw [dif_pos occurrence.selection.root_mem, dif_pos rfl]
        simp [regionForward]
      · unfold regionBackward
        rw [dif_pos selected, dif_neg root]
        simp only [regionForward, Fin.addCases_right]
        rw [DenseList.get_index]
        exact occurrence.region_right_inverse region selected
    · simp [regionBackward, regionForward, selected,
        Removal.sourceRegion_regionIndex]

@[simp] theorem regionForward_hostRegion
    (occurrence : Occurrence pattern host)
    (region : Fin (Removal.regions occurrence).length) :
    regionForward occurrence
        (Fin.castAdd (freshRegions occurrence).length region) =
      Removal.sourceRegion occurrence region :=
  by simp [regionForward]

@[simp] theorem regionForward_freshRegion
    (occurrence : Occurrence pattern host)
    (fresh : Fin (freshRegions occurrence).length) :
    regionForward occurrence
        (Fin.natAdd (Removal.regions occurrence).length fresh) =
      occurrence.regionMap ((freshRegions occurrence).get fresh) :=
  by simp [regionForward]

theorem regionForward_fragmentRegion
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host)
    (region : pattern.val.RegionId) :
    regionForward occurrence
        (if root : region = pattern.val.root then
          Fin.castAdd (freshRegions occurrence).length
            (Removal.site occurrence)
        else
          Fin.natAdd (Removal.regions occurrence).length
            (DenseList.index (freshRegions occurrence) region (by
              simp [freshRegions, ConcreteDiagram.regionsList,
                Data.Finite.mem_allFin, root]))) =
      occurrence.regionMap region := by
  by_cases root : region = pattern.val.root
  · subst region
    simp [regionForward, Removal.site, occurrence.root]
  · simp only [root, ↓reduceDIte, regionForward, Fin.addCases_right]
    exact congrArg occurrence.regionMap (DenseList.get_index _ _ _)

private theorem retainedNode_of_not_selected
    (occurrence : Occurrence pattern host)
    {node : host.val.NodeId}
    (outside : node ∉ occurrence.selection.nodes) :
    node ∈ Removal.nodes occurrence := by
  simp [Removal.nodes, ConcreteDiagram.nodesList,
    Data.Finite.mem_allFin, outside]

def nodeForward
    (occurrence : Occurrence pattern host) :
    Fin ((Removal.nodes occurrence).length + pattern.val.nodeCount) →
      host.val.NodeId :=
  Fin.addCases
    (Removal.sourceNode occurrence)
    occurrence.nodeMap

def nodeBackward
    (occurrence : Occurrence pattern host)
    (node : host.val.NodeId) :
    Fin ((Removal.nodes occurrence).length + pattern.val.nodeCount) :=
  if selected : node ∈ occurrence.selection.nodes then
    Fin.natAdd (Removal.nodes occurrence).length
      (occurrence.nodeInverse node selected)
  else
    Fin.castAdd pattern.val.nodeCount
      (Removal.nodeIndex occurrence node
        (retainedNode_of_not_selected occurrence selected))

/-- Generated retained/fresh node allocation is a finite equivalence to host IDs. -/
def nodeEquiv
    (occurrence : Occurrence pattern host) :
    Data.Finite.FiniteEquiv
      (Fin ((Removal.nodes occurrence).length + pattern.val.nodeCount))
      host.val.NodeId where
  toFun := nodeForward occurrence
  invFun := nodeBackward occurrence
  left_inv := by
    intro allocated
    refine Fin.addCases ?_ ?_ allocated
    · intro retained
      have outside :
          Removal.sourceNode occurrence retained ∉
            occurrence.selection.nodes :=
        of_decide_eq_true
          (List.mem_filter.mp
            (List.get_mem (Removal.nodes occurrence) retained)).2
      simp [nodeForward, nodeBackward, outside,
        Removal.nodeIndex_sourceNode]
    · intro fresh
      have selected :
          occurrence.nodeMap fresh ∈ occurrence.selection.nodes :=
        occurrence.node_mem fresh
      simp [nodeForward, nodeBackward, selected,
        occurrence.node_left_inverse]
  right_inv := by
    intro node
    by_cases selected : node ∈ occurrence.selection.nodes
    · simp [nodeBackward, nodeForward, selected,
        occurrence.node_right_inverse]
    · simp [nodeBackward, nodeForward, selected,
        Removal.sourceNode_nodeIndex]

@[simp] theorem nodeForward_hostNode
    (occurrence : Occurrence pattern host)
    (node : Fin (Removal.nodes occurrence).length) :
    nodeForward occurrence
        (Fin.castAdd pattern.val.nodeCount node) =
      Removal.sourceNode occurrence node := by
  simp [nodeForward]

@[simp] theorem nodeForward_fragmentNode
    (occurrence : Occurrence pattern host)
    (node : pattern.val.NodeId) :
    nodeForward occurrence
        (Fin.natAdd (Removal.nodes occurrence).length node) =
      occurrence.nodeMap node := by
  simp [nodeForward]

def freshWires
    (occurrence : Occurrence pattern host) :
    List pattern.val.WireId :=
  pattern.val.wiresList.filter fun wire =>
    decide
      ((host.val.wires (occurrence.wireMap wire)).scope ∈
        occurrence.selection.regions)

private theorem internal_scope_not_boundarySource
    (occurrence : Occurrence pattern host)
    (wire : pattern.val.WireId)
    (internal :
      (host.val.wires (occurrence.wireMap wire)).scope ∈
        occurrence.selection.regions) :
    wire ∉ occurrence.boundarySources := by
  intro member
  let position :=
    DenseList.index occurrence.boundarySources wire member
  have retrieved :
      occurrence.boundarySourceAt position = wire := by
    exact DenseList.get_index _ _ _
  have external := occurrence.boundarySource_external position
  rw [retrieved] at external
  exact external internal

private theorem external_scope_boundarySource
    (occurrence : Occurrence pattern host)
    (wire : pattern.val.WireId)
    (external :
      (host.val.wires (occurrence.wireMap wire)).scope ∉
        occurrence.selection.regions) :
    wire ∈ occurrence.boundarySources := by
  have selected := occurrence.wire_mem wire
  have selectedReason :=
    (occurrence.selection.wires_exact
      (occurrence.wireMap wire)).mp selected
  have touches :
      CheckedSelection.endpointTouchesNodes host
        occurrence.selection.nodes (occurrence.wireMap wire) :=
    selectedReason.resolve_left external
  rcases touches with ⟨endpoint, incident, nodeSelected⟩
  let crossing :
      CheckedSelection.BoundaryCrossing occurrence.selection :=
    ⟨(occurrence.wireMap wire, endpoint),
      selected, incident, nodeSelected, external⟩
  have member := occurrence.boundary_complete crossing
  unfold Occurrence.boundarySources
  apply List.mem_map.mpr
  refine ⟨crossing, member, ?_⟩
  exact occurrence.wire_left_inverse wire

theorem internal_scope_iff_not_boundarySource
    (occurrence : Occurrence pattern host)
    (wire : pattern.val.WireId) :
    (host.val.wires (occurrence.wireMap wire)).scope ∈
        occurrence.selection.regions ↔
      wire ∉ occurrence.boundarySources := by
  constructor
  · exact internal_scope_not_boundarySource occurrence wire
  · intro notBoundary
    by_cases internal :
        (host.val.wires (occurrence.wireMap wire)).scope ∈
          occurrence.selection.regions
    · exact internal
    · exact False.elim
        (notBoundary
          (external_scope_boundarySource occurrence wire internal))

theorem freshWires_nodup (occurrence : Occurrence pattern host) :
    (freshWires occurrence).Nodup :=
  Data.Finite.allFin_nodup pattern.val.wireCount |>.filter _

/-- The generated fragment's nonboundary list is exactly the internal wire allocation. -/
theorem fragmentInternalWires_eq_freshWires
    (occurrence : Occurrence pattern host)
    (compiled : ExtractionCompilation occurrence)
    (removed : RemovalResult occurrence)
    (attachment : ConcreteSpliceAttachment removed compiled.checked) :
    attachment.fragmentInternalWires = freshWires occurrence := by
  unfold ConcreteSpliceAttachment.fragmentInternalWires freshWires
  change
    pattern.val.wiresList.filter
        (fun wire => decide (wire ∉ occurrence.boundarySources)) =
      pattern.val.wiresList.filter
        (fun wire =>
          decide
            ((host.val.wires (occurrence.wireMap wire)).scope ∈
              occurrence.selection.regions))
  apply List.filter_congr
  intro wire _
  by_cases internal :
      (host.val.wires (occurrence.wireMap wire)).scope ∈
        occurrence.selection.regions
  · have notBoundary :=
      internal_scope_not_boundarySource occurrence wire internal
    simp [internal, notBoundary]
  · have boundary :=
      external_scope_boundarySource occurrence wire internal
    simp [internal, boundary]

private theorem retainedWire_of_external_scope
    (occurrence : Occurrence pattern host)
    {wire : host.val.WireId}
    (external :
      (host.val.wires wire).scope ∉ occurrence.selection.regions) :
    wire ∈ Removal.wires occurrence := by
  simp [Removal.wires, ConcreteDiagram.wiresList,
    Data.Finite.mem_allFin, external]

private theorem freshWire_of_internal_scope
    (occurrence : Occurrence pattern host)
    {wire : host.val.WireId}
    (internal :
      (host.val.wires wire).scope ∈ occurrence.selection.regions) :
    occurrence.wireInverse wire
        (occurrence.selection.internal_wire_selected wire internal) ∈
      freshWires occurrence := by
  let selected :=
    occurrence.selection.internal_wire_selected wire internal
  have inverse :=
    occurrence.wire_right_inverse wire selected
  simp only [freshWires, List.mem_filter]
  refine ⟨Data.Finite.mem_allFin _, decide_eq_true ?_⟩
  simpa only [inverse] using internal

def wireForward
    (occurrence : Occurrence pattern host) :
    Fin ((Removal.wires occurrence).length +
      (freshWires occurrence).length) →
      host.val.WireId :=
  Fin.addCases
    (Removal.sourceWire occurrence)
    (fun fresh =>
      occurrence.wireMap ((freshWires occurrence).get fresh))

def wireBackward
    (occurrence : Occurrence pattern host)
    (wire : host.val.WireId) :
    Fin ((Removal.wires occurrence).length +
      (freshWires occurrence).length) :=
  if internal :
      (host.val.wires wire).scope ∈ occurrence.selection.regions then
    let selected :=
      occurrence.selection.internal_wire_selected wire internal
    Fin.natAdd (Removal.wires occurrence).length
      (DenseList.index (freshWires occurrence)
        (occurrence.wireInverse wire selected)
        (freshWire_of_internal_scope occurrence internal))
  else
    Fin.castAdd (freshWires occurrence).length
      (Removal.wireIndex occurrence wire
        (retainedWire_of_external_scope occurrence internal))

/-- Generated retained/fresh wire allocation is a finite equivalence to host IDs. -/
def wireEquiv
    (occurrence : Occurrence pattern host) :
    Data.Finite.FiniteEquiv
      (Fin ((Removal.wires occurrence).length +
        (freshWires occurrence).length))
      host.val.WireId where
  toFun := wireForward occurrence
  invFun := wireBackward occurrence
  left_inv := by
    intro allocated
    refine Fin.addCases ?_ ?_ allocated
    · intro retained
      have external :
          (host.val.wires (Removal.sourceWire occurrence retained)).scope ∉
            occurrence.selection.regions :=
        of_decide_eq_true
          (List.mem_filter.mp
            (List.get_mem (Removal.wires occurrence) retained)).2
      simp [wireForward, wireBackward, external,
        Removal.wireIndex_sourceWire]
    · intro fresh
      let source := (freshWires occurrence).get fresh
      have sourceMember : source ∈ freshWires occurrence :=
        List.get_mem _ fresh
      have internal :
          (host.val.wires (occurrence.wireMap source)).scope ∈
            occurrence.selection.regions :=
        of_decide_eq_true (List.mem_filter.mp sourceMember).2
      let selected :=
        occurrence.selection.internal_wire_selected
          (occurrence.wireMap source) internal
      have inverse :
          occurrence.wireInverse (occurrence.wireMap source) selected =
            source :=
        occurrence.wire_left_inverse source
      simp only [wireForward, Fin.addCases_right]
      change
        wireBackward occurrence (occurrence.wireMap source) =
          Fin.natAdd (Removal.wires occurrence).length fresh
      unfold wireBackward
      rw [dif_pos internal]
      apply congrArg (Fin.natAdd (Removal.wires occurrence).length)
      simpa only [inverse] using
        DenseList.index_get (freshWires occurrence)
          (freshWires_nodup occurrence) fresh
  right_inv := by
    intro wire
    by_cases internal :
        (host.val.wires wire).scope ∈ occurrence.selection.regions
    · unfold wireBackward
      rw [dif_pos internal]
      simp only [wireForward, Fin.addCases_right]
      rw [DenseList.get_index]
      exact occurrence.wire_right_inverse wire
        (occurrence.selection.internal_wire_selected wire internal)
    · simp [wireBackward, wireForward, internal,
        Removal.sourceWire_wireIndex]

@[simp] theorem wireForward_hostWire
    (occurrence : Occurrence pattern host)
    (wire : Fin (Removal.wires occurrence).length) :
    wireForward occurrence
        (Fin.castAdd (freshWires occurrence).length wire) =
      Removal.sourceWire occurrence wire := by
  simp [wireForward]

@[simp] theorem wireForward_freshWire
    (occurrence : Occurrence pattern host)
    (fresh : Fin (freshWires occurrence).length) :
    wireForward occurrence
        (Fin.natAdd (Removal.wires occurrence).length fresh) =
      occurrence.wireMap ((freshWires occurrence).get fresh) := by
  simp [wireForward]

/-- Region equivalence specialized to the generated reconstruction carrier. -/
def attachmentRegionEquiv
    (occurrence : Occurrence pattern host)
    (compiled : ExtractionCompilation occurrence)
    (removed : RemovalResult occurrence)
    (attachment : ConcreteSpliceAttachment removed compiled.checked) :
    Data.Finite.FiniteEquiv attachment.diagram.RegionId host.val.RegionId := by
  change Data.Finite.FiniteEquiv
    (Fin ((Removal.regions occurrence).length +
      attachment.fragmentRegions.length))
    host.val.RegionId
  rw [show attachment.fragmentRegions = freshRegions occurrence from
    fragmentRegions_eq_freshRegions occurrence compiled removed attachment]
  exact regionEquiv occurrence

/-- Node equivalence specialized to the generated reconstruction carrier. -/
def attachmentNodeEquiv
    (occurrence : Occurrence pattern host)
    (compiled : ExtractionCompilation occurrence)
    (removed : RemovalResult occurrence)
    (attachment : ConcreteSpliceAttachment removed compiled.checked)
    (accepted :
      reconstructionAttachment? occurrence compiled removed =
        some attachment) :
    Data.Finite.FiniteEquiv attachment.diagram.NodeId host.val.NodeId := by
  change Data.Finite.FiniteEquiv
    (Fin ((Removal.nodes occurrence).length +
      (pattern.val.nodeCount + attachment.identityRequests.length)))
    host.val.NodeId
  rw [show attachment.identityRequests = [] from
    identityRequests_eq_nil occurrence compiled removed attachment accepted]
  exact nodeEquiv occurrence

private theorem attachmentFreshWire_of_internal_scope
    (occurrence : Occurrence pattern host)
    (compiled : ExtractionCompilation occurrence)
    (removed : RemovalResult occurrence)
    (attachment : ConcreteSpliceAttachment removed compiled.checked)
    {wire : host.val.WireId}
    (internal :
      (host.val.wires wire).scope ∈ occurrence.selection.regions) :
    occurrence.wireInverse wire
        (occurrence.selection.internal_wire_selected wire internal) ∈
      attachment.fragmentInternalWires := by
  rw [fragmentInternalWires_eq_freshWires
    occurrence compiled removed attachment]
  exact freshWire_of_internal_scope occurrence internal

private theorem attachmentFragmentInternalWires_nodup
    (occurrence : Occurrence pattern host)
    (compiled : ExtractionCompilation occurrence)
    (removed : RemovalResult occurrence)
    (attachment : ConcreteSpliceAttachment removed compiled.checked) :
    attachment.fragmentInternalWires.Nodup := by
  rw [fragmentInternalWires_eq_freshWires
    occurrence compiled removed attachment]
  exact freshWires_nodup occurrence

def attachmentWireForward
    (occurrence : Occurrence pattern host)
    (compiled : ExtractionCompilation occurrence)
    (removed : RemovalResult occurrence)
    (attachment : ConcreteSpliceAttachment removed compiled.checked) :
    attachment.diagram.WireId → host.val.WireId :=
  Fin.addCases
    (Removal.sourceWire occurrence)
    (fun fresh =>
      occurrence.wireMap
        (attachment.fragmentInternalWires.get fresh))

def attachmentWireBackward
    (occurrence : Occurrence pattern host)
    (compiled : ExtractionCompilation occurrence)
    (removed : RemovalResult occurrence)
    (attachment : ConcreteSpliceAttachment removed compiled.checked)
    (wire : host.val.WireId) :
    attachment.diagram.WireId :=
  if internal :
      (host.val.wires wire).scope ∈ occurrence.selection.regions then
    Fin.natAdd removed.complement.val.wireCount
      (DenseList.index attachment.fragmentInternalWires
        (occurrence.wireInverse wire
          (occurrence.selection.internal_wire_selected wire internal))
        (attachmentFreshWire_of_internal_scope occurrence compiled
          removed attachment internal))
  else
    Fin.castAdd attachment.fragmentInternalWires.length
      (Removal.wireIndex occurrence wire
        (retainedWire_of_external_scope occurrence internal))

/-- Wire equivalence specialized directly to the actual reconstruction carrier. -/
def attachmentWireEquiv
    (occurrence : Occurrence pattern host)
    (compiled : ExtractionCompilation occurrence)
    (removed : RemovalResult occurrence)
    (attachment : ConcreteSpliceAttachment removed compiled.checked) :
    Data.Finite.FiniteEquiv attachment.diagram.WireId host.val.WireId where
  toFun := attachmentWireForward occurrence compiled removed attachment
  invFun := attachmentWireBackward occurrence compiled removed attachment
  left_inv := by
    intro allocated
    refine Fin.addCases ?_ ?_ allocated
    · intro retained
      have external :
          (host.val.wires
            (Removal.sourceWire occurrence retained)).scope ∉
              occurrence.selection.regions :=
        of_decide_eq_true
          (List.mem_filter.mp
            (List.get_mem (Removal.wires occurrence) retained)).2
      simp [attachmentWireForward, attachmentWireBackward, external,
        Removal.wireIndex_sourceWire]
    · intro fresh
      let source := attachment.fragmentInternalWires.get fresh
      have sourceMember :
          source ∈ attachment.fragmentInternalWires :=
        List.get_mem _ fresh
      have sourceFresh : source ∈ freshWires occurrence := by
        rw [← fragmentInternalWires_eq_freshWires
          occurrence compiled removed attachment]
        exact sourceMember
      have internal :
          (host.val.wires (occurrence.wireMap source)).scope ∈
            occurrence.selection.regions :=
        of_decide_eq_true (List.mem_filter.mp sourceFresh).2
      let selected :=
        occurrence.selection.internal_wire_selected
          (occurrence.wireMap source) internal
      have inverse :
          occurrence.wireInverse (occurrence.wireMap source) selected =
            source :=
        occurrence.wire_left_inverse source
      simp only [attachmentWireForward, Fin.addCases_right]
      change
        attachmentWireBackward occurrence compiled removed attachment
            (occurrence.wireMap source) =
          Fin.natAdd removed.complement.val.wireCount fresh
      unfold attachmentWireBackward
      rw [dif_pos internal]
      apply congrArg (Fin.natAdd removed.complement.val.wireCount)
      simpa only [inverse] using
        DenseList.index_get attachment.fragmentInternalWires
          (attachmentFragmentInternalWires_nodup occurrence compiled
            removed attachment) fresh
  right_inv := by
    intro wire
    by_cases internal :
        (host.val.wires wire).scope ∈ occurrence.selection.regions
    · unfold attachmentWireBackward
      rw [dif_pos internal]
      unfold attachmentWireForward
      simp only [Fin.addCases_right]
      rw [DenseList.get_index]
      exact occurrence.wire_right_inverse wire
        (occurrence.selection.internal_wire_selected wire internal)
    · simp [attachmentWireBackward, attachmentWireForward, internal,
        Removal.sourceWire_wireIndex]

@[simp] theorem attachmentWireEquiv_hostWire
    (occurrence : Occurrence pattern host)
    (compiled : ExtractionCompilation occurrence)
    (removed : RemovalResult occurrence)
    (attachment : ConcreteSpliceAttachment removed compiled.checked)
    (wire : removed.complement.val.WireId) :
    (attachmentWireEquiv occurrence compiled removed attachment).toFun
        (attachment.hostWire wire) =
      Removal.sourceWire occurrence wire := by
  simp [attachmentWireEquiv, attachmentWireForward,
    ConcreteSpliceAttachment.hostWire]

@[simp] theorem attachmentWireEquiv_freshWire
    (occurrence : Occurrence pattern host)
    (compiled : ExtractionCompilation occurrence)
    (removed : RemovalResult occurrence)
    (attachment : ConcreteSpliceAttachment removed compiled.checked)
    (fresh : Fin attachment.fragmentInternalWires.length) :
    (attachmentWireEquiv occurrence compiled removed attachment).toFun
        (attachment.freshWire fresh) =
      occurrence.wireMap (attachment.fragmentInternalWires.get fresh) := by
  simp [attachmentWireEquiv, attachmentWireForward,
    ConcreteSpliceAttachment.freshWire]

theorem attachmentWireEquiv_fragmentWire
    (occurrence : Occurrence pattern host)
    (compiled : ExtractionCompilation occurrence)
    (removed : RemovalResult occurrence)
    (attachment : ConcreteSpliceAttachment removed compiled.checked)
    (accepted :
      reconstructionAttachment? occurrence compiled removed =
        some attachment)
    (source : compiled.checked.val.diagram.WireId) :
    (attachmentWireEquiv occurrence compiled removed attachment).toFun
        (attachment.fragmentWire source) =
      occurrence.wireMap source := by
  by_cases boundary : source ∈ compiled.checked.val.boundary
  · let position :=
      attachment.representativePosition source boundary
    have retrieved :
        compiled.checked.val.boundary.get position = source :=
      DenseList.get_index _ _ _
    have sourceAt :
        occurrence.boundarySourceAt position = source := by
      simpa only [Occurrence.boundarySourceAt] using retrieved
    unfold ConcreteSpliceAttachment.fragmentWire
    rw [dif_pos boundary]
    rw [attachmentWireEquiv_hostWire occurrence compiled removed attachment]
    change
      Removal.sourceWire occurrence
          (attachment.representativeTarget source boundary) =
        occurrence.wireMap source
    change
      Removal.sourceWire occurrence (attachment.target position) =
        occurrence.wireMap source
    rw [attachment_target occurrence compiled removed attachment accepted]
    rw [Removal.sourceWire_wireIndex, sourceAt]
  · unfold ConcreteSpliceAttachment.fragmentWire
    rw [dif_neg boundary]
    rw [attachmentWireEquiv_freshWire occurrence compiled removed attachment]
    exact congrArg occurrence.wireMap (DenseList.get_index _ _ _)

private theorem portCorresponds_of_renamed_node
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (regions : Data.Finite.FiniteEquiv left.RegionId right.RegionId)
    (nodes : Data.Finite.FiniteEquiv left.NodeId right.NodeId)
    (endpoint : CEndpoint left.nodeCount)
    (candidate : CEndpoint right.nodeCount)
    (nodeEquality : candidate.node = nodes endpoint.node)
    (nodeTable :
      right.nodes (nodes endpoint.node) =
        CNode.rename regions (left.nodes endpoint.node))
    (portRequired :
      candidate.port ∈ right.requiredPorts candidate.node)
    (portEquality : candidate.port = endpoint.port) :
    PortCorresponds left right nodes endpoint candidate := by
  unfold PortCorresponds
  refine ⟨nodeEquality, ?_⟩
  rw [nodeEquality]
  cases leftData : left.nodes endpoint.node <;>
    cases rightData : right.nodes (nodes endpoint.node) <;>
    simp [leftData, rightData, CNode.rename] at nodeTable ⊢
  all_goals try exact portEquality
  case identity.identity =>
    rcases nodeTable with ⟨_, signatureEquality, arityEquality⟩
    have identityPort :
        ∃ index, candidate.port = .identity index := by
      unfold ConcreteDiagram.requiredPorts at portRequired
      rw [nodeEquality] at portRequired
      rw [rightData] at portRequired
      rcases List.mem_map.mp portRequired with
        ⟨index, _, equality⟩
      exact ⟨index, equality.symm⟩
    rcases identityPort with ⟨index, identityPort⟩
    refine
      ⟨signatureEquality.symm, arityEquality.symm, ?_⟩
    exact
      ⟨⟨index, portEquality.symm.trans identityPort⟩,
        ⟨index, identityPort⟩⟩

@[simp] theorem regionEquiv_hostRegion
    (occurrence : Occurrence pattern host)
    (compiled : ExtractionCompilation occurrence)
    (removed : RemovalResult occurrence)
    (attachment : ConcreteSpliceAttachment removed compiled.checked)
    (region : removed.complement.val.RegionId) :
    (regionEquiv occurrence).toFun (attachment.hostRegion region) =
      Removal.sourceRegion occurrence region := by
  exact regionForward_hostRegion occurrence region

@[simp] theorem regionEquiv_hostAllocation
    (occurrence : Occurrence pattern host)
    (compiled : ExtractionCompilation occurrence)
    (removed : RemovalResult occurrence)
    (attachment : ConcreteSpliceAttachment removed compiled.checked)
    (region : removed.complement.val.RegionId) :
    (regionEquiv occurrence).toFun
        (Fin.castAdd attachment.fragmentRegions.length region) =
      Removal.sourceRegion occurrence region :=
  regionEquiv_hostRegion occurrence compiled removed attachment region

@[simp] theorem regionEquiv_freshRegion
    (occurrence : Occurrence pattern host)
    (compiled : ExtractionCompilation occurrence)
    (removed : RemovalResult occurrence)
    (attachment : ConcreteSpliceAttachment removed compiled.checked)
    (fresh : Fin attachment.fragmentRegions.length) :
    (regionEquiv occurrence).toFun (attachment.freshRegion fresh) =
      occurrence.regionMap (attachment.fragmentRegions.get fresh) := by
  exact regionForward_freshRegion occurrence fresh

@[simp] theorem regionEquiv_freshAllocation
    (occurrence : Occurrence pattern host)
    (compiled : ExtractionCompilation occurrence)
    (removed : RemovalResult occurrence)
    (attachment : ConcreteSpliceAttachment removed compiled.checked)
    (fresh : Fin attachment.fragmentRegions.length) :
    (regionEquiv occurrence).toFun
        (Fin.natAdd removed.complement.val.regionCount fresh) =
      occurrence.regionMap (attachment.fragmentRegions.get fresh) :=
  regionEquiv_freshRegion occurrence compiled removed attachment fresh

@[simp] theorem regionEquiv_fragmentRegion
    (occurrence : Occurrence pattern host)
    (compiled : ExtractionCompilation occurrence)
    (removed : RemovalResult occurrence)
    (attachment : ConcreteSpliceAttachment removed compiled.checked)
    (region : compiled.checked.val.diagram.RegionId) :
    (regionEquiv occurrence).toFun (attachment.fragmentRegion region) =
      occurrence.regionMap region := by
  exact regionForward_fragmentRegion occurrence region

@[simp] theorem fragmentRegionData
    (occurrence : Occurrence pattern host)
    (compiled : ExtractionCompilation occurrence)
    (removed : RemovalResult occurrence)
    (attachment : ConcreteSpliceAttachment removed compiled.checked)
    (fresh : Fin attachment.fragmentRegions.length) :
    compiled.checked.val.diagram.regions
        (attachment.fragmentRegions.get fresh) =
      occurrence.extractedRegion
        ((freshRegions occurrence).get fresh) :=
  rfl

theorem renamedHostNode_rename
    (occurrence : Occurrence pattern host)
    (compiled : ExtractionCompilation occurrence)
    (removed : RemovalResult occurrence)
    (attachment : ConcreteSpliceAttachment removed compiled.checked)
    (node : removed.complement.val.NodeId) :
    CNode.rename (regionEquiv occurrence)
        (ConcreteSpliceAttachment.renameHostNode attachment node) =
      mapNode (Removal.sourceRegion occurrence)
        (removed.complement.val.nodes node) := by
  cases nodeData : removed.complement.val.nodes node <;>
    simp [ConcreteSpliceAttachment.renameHostNode, nodeData,
      CNode.rename, mapNode,
      regionEquiv_hostRegion occurrence compiled removed attachment]

theorem renamedFragmentNode_rename
    (occurrence : Occurrence pattern host)
    (compiled : ExtractionCompilation occurrence)
    (removed : RemovalResult occurrence)
    (attachment : ConcreteSpliceAttachment removed compiled.checked)
    (node : compiled.checked.val.diagram.NodeId) :
    CNode.rename (regionEquiv occurrence)
        (ConcreteSpliceAttachment.renameFragmentNode attachment node) =
      mapNode occurrence.regionMap
        (compiled.checked.val.diagram.nodes node) := by
  cases nodeData : compiled.checked.val.diagram.nodes node <;>
    simp [ConcreteSpliceAttachment.renameFragmentNode, nodeData,
      CNode.rename, mapNode,
      regionEquiv_fragmentRegion occurrence compiled removed attachment]

/-- Extracting and reinserting at the generated original targets reconstructs the host. -/
def extract_splice_iso
    (occurrence : Occurrence pattern host)
    (compiled : ExtractionCompilation occurrence)
    (removed : RemovalResult occurrence)
    (attachment : ConcreteSpliceAttachment removed compiled.checked)
    (accepted :
      reconstructionAttachment? occurrence compiled removed =
        some attachment) :
    ConcreteIso attachment.diagram host.val := by
  have requestedAccepted := accepted
  unfold reconstructionAttachment? at accepted
  simp only [checkConcreteSpliceAttachment] at accepted
  split at accepted
  · rename_i signature_ok
    split at accepted
    · rename_i scope_ok
      let identities :=
        computedIdentityRequests removed compiled.checked fun position =>
          Removal.wireIndex occurrence
            (occurrence.wireMap
              (occurrence.boundarySourceAt position))
            (Removal.boundarySource_retained occurrence position)
      let checkedGenerated :
          ConcreteSpliceAttachment removed compiled.checked :=
        { target := fun position =>
            Removal.wireIndex occurrence
              (occurrence.wireMap
                (occurrence.boundarySourceAt position))
              (Removal.boundarySource_retained occurrence position)
          signature := signature_ok
          scope := scope_ok
          identityRequests := identities
          identityRequests_nodup := Data.Finite.eraseDups_nodup _
          identityRequests_exact := rfl }
      change some checkedGenerated = some attachment at accepted
      have checkedEqualsAttachment := Option.some.inj accepted
      have checkedGeneratedAccepted :
          reconstructionAttachment? occurrence compiled removed =
            some checkedGenerated := by
        rw [checkedEqualsAttachment]
        exact requestedAccepted
      have checkedRequestsEmpty :
          checkedGenerated.identityRequests = [] :=
        identityRequests_eq_nil occurrence compiled removed
          checkedGenerated checkedGeneratedAccepted
      have requestsEmpty :
          computedIdentityRequests removed compiled.checked
              checkedGenerated.target = [] :=
        checkedGenerated.identityRequests_exact.symm.trans
          checkedRequestsEmpty
      let generated : ConcreteSpliceAttachment removed compiled.checked :=
        { target := checkedGenerated.target
          signature := checkedGenerated.signature
          scope := checkedGenerated.scope
          identityRequests := []
          identityRequests_nodup := .nil
          identityRequests_exact := requestsEmpty.symm }
      have checkedEqualsGenerated : checkedGenerated = generated :=
        attachment_ext checkedGenerated generated rfl checkedRequestsEmpty
      have generatedEqualsAttachment : generated = attachment :=
        checkedEqualsGenerated.symm.trans checkedEqualsAttachment
      have generatedAccepted :
          reconstructionAttachment? occurrence compiled removed =
            some generated := by
        rw [generatedEqualsAttachment]
        exact requestedAccepted
      rw [← generatedEqualsAttachment]
      refine
        { regions := regionEquiv occurrence
          nodes := nodeEquiv occurrence
          wires := attachmentWireEquiv occurrence compiled removed generated
          root := by
              simp [ConcreteSpliceAttachment.diagram,
                ConcreteSpliceAttachment.hostRegion,
                ConcreteSpliceAttachment.fragmentRegions,
                ExtractionCompilation.checked, checkedExtraction,
                Occurrence.extractedOpen, Occurrence.extractedDiagram,
                ConcreteDiagram.regionsList,
                RemovalResult.complement, Removal.diagram,
                freshRegions, regionEquiv, regionForward,
                Removal.sourceRegion_regionIndex]
          region_table := by
              intro region
              refine Fin.addCases ?_ ?_ region
              · intro retained
                have relation :=
                  Removal.diagramRegion_rename occurrence retained
                cases regionData :
                    (Removal.diagram occurrence).regions retained
                case sheet =>
                  rw [regionData] at relation
                  unfold ConcreteSpliceAttachment.diagram
                    ConcreteSpliceAttachment.regionTable
                  simp only [Fin.addCases_left]
                  simp only [RemovalResult.complement, regionData,
                    CRegion.rename]
                  have allocation :=
                    regionEquiv_hostAllocation occurrence compiled
                      removed generated retained
                  calc
                    host.val.regions
                        ((regionEquiv occurrence).toFun
                          (Fin.castAdd generated.fragmentRegions.length
                            retained)) =
                        host.val.regions
                          (Removal.sourceRegion occurrence retained) :=
                      congrArg host.val.regions allocation
                    _ = .sheet := by
                      simpa only [mapRegion] using relation
                case cut parent =>
                  rw [regionData] at relation
                  unfold ConcreteSpliceAttachment.diagram
                    ConcreteSpliceAttachment.regionTable
                  simp only [Fin.addCases_left]
                  simp only [RemovalResult.complement, regionData,
                    CRegion.rename]
                  have allocation :=
                    regionEquiv_hostAllocation occurrence compiled
                      removed generated retained
                  have parentAllocation :=
                    regionEquiv_hostRegion occurrence compiled
                      removed generated parent
                  calc
                    host.val.regions
                        ((regionEquiv occurrence).toFun
                          (Fin.castAdd generated.fragmentRegions.length
                            retained)) =
                        host.val.regions
                          (Removal.sourceRegion occurrence retained) :=
                      congrArg host.val.regions allocation
                    _ = .cut
                          (Removal.sourceRegion occurrence parent) := by
                      simpa only [mapRegion] using relation
                    _ = .cut
                          ((regionEquiv occurrence).toFun
                            (generated.hostRegion parent)) :=
                      congrArg CRegion.cut parentAllocation.symm
              · intro fresh
                let source :=
                  (freshRegions occurrence).get fresh
                have sourceMember : source ∈ freshRegions occurrence :=
                  List.get_mem _ fresh
                have nonroot : source ≠ pattern.val.root :=
                  of_decide_eq_true
                    (List.mem_filter.mp sourceMember).2
                have relation :=
                  occurrence.extractedRegion_rename source nonroot
                cases regionData :
                    occurrence.extractedRegion source
                case sheet =>
                  rw [regionData] at relation
                  unfold ConcreteSpliceAttachment.diagram
                    ConcreteSpliceAttachment.regionTable
                  simp only [Fin.addCases_right]
                  rw [fragmentRegionData
                    occurrence compiled removed generated fresh]
                  rw [regionData]
                  simp only [CRegion.rename]
                  have allocation :=
                    regionEquiv_freshAllocation occurrence compiled
                      removed generated fresh
                  have sourceEq :
                      generated.fragmentRegions.get fresh = source :=
                    rfl
                  calc
                    host.val.regions
                        ((regionEquiv occurrence).toFun
                          (Fin.natAdd removed.complement.val.regionCount
                            fresh)) =
                        host.val.regions
                          (occurrence.regionMap
                            (generated.fragmentRegions.get fresh)) :=
                      congrArg host.val.regions allocation
                    _ = host.val.regions
                          (occurrence.regionMap source) :=
                      congrArg host.val.regions
                        (congrArg occurrence.regionMap sourceEq)
                    _ = .sheet := by
                      simpa only [mapRegion] using relation
                case cut parent =>
                  rw [regionData] at relation
                  unfold ConcreteSpliceAttachment.diagram
                    ConcreteSpliceAttachment.regionTable
                  simp only [Fin.addCases_right]
                  rw [fragmentRegionData
                    occurrence compiled removed generated fresh]
                  rw [regionData]
                  simp only [CRegion.rename]
                  have allocation :=
                    regionEquiv_freshAllocation occurrence compiled
                      removed generated fresh
                  have sourceEq :
                      generated.fragmentRegions.get fresh = source :=
                    rfl
                  have parentAllocation :=
                    regionEquiv_fragmentRegion occurrence compiled
                      removed generated parent
                  calc
                    host.val.regions
                        ((regionEquiv occurrence).toFun
                          (Fin.natAdd removed.complement.val.regionCount
                            fresh)) =
                        host.val.regions
                          (occurrence.regionMap
                            (generated.fragmentRegions.get fresh)) :=
                      congrArg host.val.regions allocation
                    _ = host.val.regions
                          (occurrence.regionMap source) :=
                      congrArg host.val.regions
                        (congrArg occurrence.regionMap sourceEq)
                    _ = .cut (occurrence.regionMap parent) := by
                      simpa only [mapRegion] using relation
                    _ = .cut
                          ((regionEquiv occurrence).toFun
                            (generated.fragmentRegion parent)) :=
                      congrArg CRegion.cut parentAllocation.symm
          node_table := by
              intro node
              refine Fin.addCases ?_ ?_ node
              · intro retained
                have relation :=
                  Removal.diagramNode_rename occurrence retained
                unfold ConcreteSpliceAttachment.diagram
                  ConcreteSpliceAttachment.nodeTable
                simp only [Fin.addCases_left]
                have allocation :
                    (nodeEquiv occurrence).toFun
                        (generated.hostNode retained) =
                      Removal.sourceNode occurrence retained := by
                  simpa [generated,
                    ConcreteSpliceAttachment.hostNode,
                    nodeEquiv, ExtractionCompilation.checked,
                    checkedExtraction, Occurrence.extractedOpen,
                    Occurrence.extractedDiagram] using
                    nodeForward_hostNode occurrence retained
                calc
                  host.val.nodes
                      ((nodeEquiv occurrence).toFun
                        (generated.hostNode retained)) =
                      host.val.nodes
                        (Removal.sourceNode occurrence retained) :=
                    congrArg host.val.nodes allocation
                  _ = mapNode (Removal.sourceRegion occurrence)
                        (removed.complement.val.nodes retained) := by
                    simpa only [RemovalResult.complement] using relation
                  _ = CNode.rename (regionEquiv occurrence)
                        (ConcreteSpliceAttachment.renameHostNode
                          generated retained) :=
                    (renamedHostNode_rename occurrence compiled removed
                      generated retained).symm
              · intro inserted
                refine Fin.addCases ?_ ?_ inserted
                · intro fresh
                  have relation :=
                    occurrence.extractedNode_rename fresh
                  unfold ConcreteSpliceAttachment.diagram
                    ConcreteSpliceAttachment.nodeTable
                  simp only [Fin.addCases_right, Fin.addCases_left]
                  have allocation :
                      (nodeEquiv occurrence).toFun
                          (generated.fragmentNode fresh) =
                        occurrence.nodeMap fresh := by
                    change
                      nodeForward occurrence
                          (generated.fragmentNode fresh) =
                        occurrence.nodeMap fresh
                    have allocated :
                        generated.fragmentNode fresh =
                          Fin.natAdd
                            (Removal.nodes occurrence).length fresh :=
                      Fin.ext (by
                        simp [generated,
                          ConcreteSpliceAttachment.fragmentNode])
                    rw [allocated]
                    exact nodeForward_fragmentNode occurrence fresh
                  calc
                    host.val.nodes
                        ((nodeEquiv occurrence).toFun
                          (generated.fragmentNode fresh)) =
                        host.val.nodes (occurrence.nodeMap fresh) :=
                      congrArg host.val.nodes allocation
                    _ = mapNode occurrence.regionMap
                          (compiled.checked.val.diagram.nodes fresh) := by
                      simpa [ExtractionCompilation.checked,
                        checkedExtraction,
                        Occurrence.extractedOpen,
                        Occurrence.extractedDiagram] using relation
                    _ = CNode.rename (regionEquiv occurrence)
                          (ConcreteSpliceAttachment.renameFragmentNode
                            generated fresh) :=
                      (renamedFragmentNode_rename occurrence compiled
                        removed generated fresh).symm
                · intro identity
                  exact Fin.elim0 identity
          wire_signature := by
              intro wire
              refine Fin.addCases ?_ ?_ wire
              · intro retained
                have relation :=
                  Removal.diagramWire_signature occurrence retained
                unfold ConcreteSpliceAttachment.diagram
                  ConcreteSpliceAttachment.wireTable
                simp only [Fin.addCases_left]
                have allocation :=
                  attachmentWireEquiv_hostWire occurrence compiled
                    removed generated retained
                calc
                  (host.val.wires
                      ((attachmentWireEquiv occurrence compiled removed
                        generated).toFun
                        (generated.hostWire retained))).sig =
                      (host.val.wires
                        (Removal.sourceWire occurrence retained)).sig :=
                    congrArg (fun id => (host.val.wires id).sig)
                      allocation
                  _ = (removed.complement.val.wires retained).sig := by
                    simpa only [RemovalResult.complement] using relation
              · intro fresh
                let source :=
                  generated.fragmentInternalWires.get fresh
                have relation :=
                  occurrence.extractedWire_signature source
                unfold ConcreteSpliceAttachment.diagram
                  ConcreteSpliceAttachment.wireTable
                simp only [Fin.addCases_right]
                have allocation :=
                  attachmentWireEquiv_freshWire occurrence compiled
                    removed generated fresh
                calc
                  (host.val.wires
                      ((attachmentWireEquiv occurrence compiled removed
                        generated).toFun
                        (generated.freshWire fresh))).sig =
                      (host.val.wires
                        (occurrence.wireMap source)).sig :=
                    congrArg (fun id => (host.val.wires id).sig)
                      allocation
                  _ = (compiled.checked.val.diagram.wires source).sig := by
                    simpa [source,
                      ExtractionCompilation.checked,
                      checkedExtraction,
                      Occurrence.extractedOpen,
                      Occurrence.extractedDiagram] using relation
          wire_scope := by
              intro wire
              refine Fin.addCases ?_ ?_ wire
              · intro retained
                have relation :=
                  Removal.diagramWire_scope_rename occurrence retained
                unfold ConcreteSpliceAttachment.diagram
                  ConcreteSpliceAttachment.wireTable
                simp only [Fin.addCases_left]
                have allocation :=
                  attachmentWireEquiv_hostWire occurrence compiled
                    removed generated retained
                have scopeAllocation :=
                  regionEquiv_hostRegion occurrence compiled removed
                    generated
                    (removed.complement.val.wires retained).scope
                calc
                  (host.val.wires
                      ((attachmentWireEquiv occurrence compiled removed
                        generated).toFun
                        (generated.hostWire retained))).scope =
                      (host.val.wires
                        (Removal.sourceWire occurrence retained)).scope :=
                    congrArg (fun id => (host.val.wires id).scope)
                      allocation
                  _ = Removal.sourceRegion occurrence
                        (removed.complement.val.wires retained).scope := by
                    simpa only [RemovalResult.complement] using relation
                  _ = (regionEquiv occurrence).toFun
                        (generated.hostRegion
                          (removed.complement.val.wires retained).scope) :=
                    scopeAllocation.symm
              · intro fresh
                let source :=
                  generated.fragmentInternalWires.get fresh
                have sourceMember :
                    source ∈ generated.fragmentInternalWires :=
                  List.get_mem _ fresh
                have sourceFresh : source ∈ freshWires occurrence := by
                  rw [← fragmentInternalWires_eq_freshWires
                    occurrence compiled removed generated]
                  exact sourceMember
                have internal :
                    (host.val.wires
                      (occurrence.wireMap source)).scope ∈
                      occurrence.selection.regions :=
                  of_decide_eq_true
                    (List.mem_filter.mp sourceFresh).2
                have relation :=
                  occurrence.extractedWire_scope_rename
                    source internal
                unfold ConcreteSpliceAttachment.diagram
                  ConcreteSpliceAttachment.wireTable
                simp only [Fin.addCases_right]
                have allocation :=
                  attachmentWireEquiv_freshWire occurrence compiled
                    removed generated fresh
                have scopeAllocation :=
                  regionEquiv_fragmentRegion occurrence compiled removed
                    generated
                    (compiled.checked.val.diagram.wires source).scope
                calc
                  (host.val.wires
                      ((attachmentWireEquiv occurrence compiled removed
                        generated).toFun
                        (generated.freshWire fresh))).scope =
                      (host.val.wires
                        (occurrence.wireMap source)).scope :=
                    congrArg (fun id => (host.val.wires id).scope)
                      allocation
                  _ = occurrence.regionMap
                        (compiled.checked.val.diagram.wires source).scope := by
                    simpa [source,
                      ExtractionCompilation.checked,
                      checkedExtraction,
                      Occurrence.extractedOpen,
                      Occurrence.extractedDiagram] using relation
                  _ = (regionEquiv occurrence).toFun
                        (generated.fragmentRegion
                          (compiled.checked.val.diagram.wires
                            source).scope) :=
                    scopeAllocation.symm
          endpoint_forward := by
              have fragmentCase :
                  ∀ (candidateWire : generated.diagram.WireId)
                    (endpoint : CEndpoint generated.diagram.nodeCount),
                    endpoint ∈
                        generated.generatedEndpoints candidateWire →
                      ∃ candidate,
                        candidate ∈
                            (host.val.wires
                              ((attachmentWireEquiv occurrence compiled
                                removed generated).toFun
                                candidateWire)).endpoints ∧
                          PortCorresponds generated.diagram host.val
                            (nodeEquiv occurrence) endpoint candidate := by
                intro candidateWire endpoint member
                rcases generated.generatedEndpoint_origin rfl
                    candidateWire endpoint member with
                  ⟨source, sourceEndpoint, sourceIncident,
                    mappedWire, mappedEndpoint⟩
                have hostIncident :=
                  (occurrence.extractedEndpoint_mem_iff
                    source sourceEndpoint).mp (by
                      simpa [ExtractionCompilation.checked,
                        checkedExtraction,
                        Occurrence.extractedOpen,
                        Occurrence.extractedDiagram] using sourceIncident)
                have hostWireEquality :
                    occurrence.wireMap source =
                      (attachmentWireEquiv occurrence compiled removed
                        generated).toFun candidateWire := by
                  calc
                    occurrence.wireMap source =
                        (attachmentWireEquiv occurrence compiled removed
                          generated).toFun
                          (generated.fragmentWire source) :=
                      (attachmentWireEquiv_fragmentWire occurrence compiled
                        removed generated generatedAccepted source).symm
                    _ = (attachmentWireEquiv occurrence compiled removed
                          generated).toFun candidateWire :=
                      congrArg
                        (attachmentWireEquiv occurrence compiled removed
                          generated).toFun mappedWire
                rw [hostWireEquality] at hostIncident
                subst endpoint
                refine
                  ⟨occurrence.pushEndpoint sourceEndpoint,
                    hostIncident, ?_⟩
                have fragmentAllocated :
                    generated.fragmentNode sourceEndpoint.node =
                      Fin.natAdd
                        (Removal.nodes occurrence).length
                        sourceEndpoint.node :=
                  Fin.ext (by
                    simp [generated,
                      ConcreteSpliceAttachment.fragmentNode])
                have nodeAllocation :
                    (nodeEquiv occurrence).toFun
                        (generated.fragmentEndpoint sourceEndpoint).node =
                      (occurrence.pushEndpoint sourceEndpoint).node := by
                  change
                    nodeForward occurrence
                        (generated.fragmentNode sourceEndpoint.node) =
                      occurrence.nodeMap sourceEndpoint.node
                  rw [fragmentAllocated]
                  exact
                    nodeForward_fragmentNode occurrence sourceEndpoint.node
                have sourceNodeRelation :=
                  occurrence.extractedNode_rename sourceEndpoint.node
                have nodeTableRelation :
                    host.val.nodes
                        ((nodeEquiv occurrence).toFun
                          (generated.fragmentEndpoint sourceEndpoint).node) =
                      CNode.rename (regionEquiv occurrence)
                        (generated.diagram.nodes
                          (generated.fragmentEndpoint
                            sourceEndpoint).node) := by
                  calc
                    host.val.nodes
                        ((nodeEquiv occurrence).toFun
                          (generated.fragmentEndpoint
                            sourceEndpoint).node) =
                        host.val.nodes
                          (occurrence.nodeMap sourceEndpoint.node) :=
                      congrArg host.val.nodes nodeAllocation
                    _ = mapNode occurrence.regionMap
                          (compiled.checked.val.diagram.nodes
                            sourceEndpoint.node) := by
                      simpa [ExtractionCompilation.checked,
                        checkedExtraction,
                        Occurrence.extractedOpen,
                        Occurrence.extractedDiagram] using
                        sourceNodeRelation
                    _ = CNode.rename (regionEquiv occurrence)
                          (ConcreteSpliceAttachment.renameFragmentNode
                            generated sourceEndpoint.node) :=
                      (renamedFragmentNode_rename occurrence compiled
                        removed generated sourceEndpoint.node).symm
                    _ = CNode.rename (regionEquiv occurrence)
                          (generated.diagram.nodes
                            (generated.fragmentEndpoint
                              sourceEndpoint).node) := by
                      simp [ConcreteSpliceAttachment.fragmentEndpoint]
                have portRequired :=
                  ConcreteDiagram.incident_port_required _
                    host.val host.property
                    ((attachmentWireEquiv occurrence compiled removed
                      generated).toFun candidateWire)
                    (occurrence.pushEndpoint sourceEndpoint)
                    hostIncident
                refine portCorresponds_of_renamed_node
                  (left := generated.diagram) (right := host.val)
                  (regions := regionEquiv occurrence)
                  (nodes := nodeEquiv occurrence)
                  (endpoint :=
                    generated.fragmentEndpoint sourceEndpoint)
                  (candidate := occurrence.pushEndpoint sourceEndpoint)
                  nodeAllocation.symm nodeTableRelation portRequired ?_
                rfl
              intro wire
              refine Fin.addCases ?_ ?_ wire
              · intro retained endpoint member
                unfold ConcreteSpliceAttachment.diagram
                  ConcreteSpliceAttachment.wireTable at member
                simp only [Fin.addCases_left] at member
                rcases List.mem_append.mp member with
                  retainedMember | generatedMember
                · rcases List.mem_map.mp retainedMember with
                    ⟨sourceEndpoint, sourceIncident, rfl⟩
                  have hostIncident :=
                    (Removal.diagramEndpoint_mem_iff occurrence
                      retained sourceEndpoint).mp (by
                        simpa only [RemovalResult.complement] using
                          sourceIncident)
                  refine
                    ⟨Removal.sourceEndpoint occurrence sourceEndpoint,
                      ?_, ?_⟩
                  · change
                      Removal.sourceEndpoint occurrence sourceEndpoint ∈
                        (host.val.wires
                          ((attachmentWireEquiv occurrence compiled removed
                            generated).toFun
                            (generated.hostWire retained))).endpoints
                    rw [attachmentWireEquiv_hostWire occurrence compiled
                      removed generated retained]
                    exact hostIncident
                  · have hostAllocated :
                        generated.hostNode sourceEndpoint.node =
                          Fin.castAdd pattern.val.nodeCount
                            sourceEndpoint.node :=
                      Fin.ext (by
                        simp [generated,
                          ConcreteSpliceAttachment.hostNode])
                    have nodeAllocation :
                        (nodeEquiv occurrence).toFun
                            (generated.hostEndpoint sourceEndpoint).node =
                          (Removal.sourceEndpoint occurrence
                            sourceEndpoint).node := by
                      change
                        nodeForward occurrence
                            (generated.hostNode sourceEndpoint.node) =
                          Removal.sourceNode occurrence sourceEndpoint.node
                      rw [hostAllocated]
                      exact
                        nodeForward_hostNode occurrence sourceEndpoint.node
                    have sourceNodeRelation :=
                      Removal.diagramNode_rename occurrence
                        sourceEndpoint.node
                    have nodeTableRelation :
                        host.val.nodes
                            ((nodeEquiv occurrence).toFun
                              (generated.hostEndpoint
                                sourceEndpoint).node) =
                          CNode.rename (regionEquiv occurrence)
                            (generated.diagram.nodes
                              (generated.hostEndpoint
                                sourceEndpoint).node) := by
                      calc
                        host.val.nodes
                            ((nodeEquiv occurrence).toFun
                              (generated.hostEndpoint
                                sourceEndpoint).node) =
                            host.val.nodes
                              (Removal.sourceNode occurrence
                                sourceEndpoint.node) :=
                          congrArg host.val.nodes nodeAllocation
                        _ = mapNode (Removal.sourceRegion occurrence)
                              (removed.complement.val.nodes
                                sourceEndpoint.node) := by
                          simpa only [RemovalResult.complement] using
                            sourceNodeRelation
                        _ = CNode.rename (regionEquiv occurrence)
                              (ConcreteSpliceAttachment.renameHostNode
                                generated sourceEndpoint.node) :=
                          (renamedHostNode_rename occurrence compiled
                            removed generated sourceEndpoint.node).symm
                        _ = CNode.rename (regionEquiv occurrence)
                              (generated.diagram.nodes
                                (generated.hostEndpoint
                                  sourceEndpoint).node) := by
                          simp [ConcreteSpliceAttachment.hostEndpoint]
                    have portRequired :=
                      ConcreteDiagram.incident_port_required _
                        host.val host.property
                        ((attachmentWireEquiv occurrence compiled removed
                          generated).toFun
                          (generated.hostWire retained))
                        (Removal.sourceEndpoint occurrence sourceEndpoint)
                        (by simpa using hostIncident)
                    refine portCorresponds_of_renamed_node
                      (left := generated.diagram) (right := host.val)
                      (regions := regionEquiv occurrence)
                      (nodes := nodeEquiv occurrence)
                      (endpoint := generated.hostEndpoint sourceEndpoint)
                      (candidate :=
                        Removal.sourceEndpoint occurrence sourceEndpoint)
                      nodeAllocation.symm nodeTableRelation
                      portRequired ?_
                    rfl
                · exact fragmentCase
                    (generated.hostWire retained) endpoint generatedMember
              · intro fresh endpoint member
                unfold ConcreteSpliceAttachment.diagram
                  ConcreteSpliceAttachment.wireTable at member
                simp only [Fin.addCases_right] at member
                exact fragmentCase
                  (generated.freshWire fresh) endpoint member
          endpoint_backward := by
              have fragmentCorresponds :
                  ∀ (candidate : CEndpoint host.val.nodeCount)
                    (selected :
                      candidate.node ∈ occurrence.selection.nodes)
                    (portRequired :
                      candidate.port ∈
                        host.val.requiredPorts candidate.node),
                    PortCorresponds generated.diagram host.val
                      (nodeEquiv occurrence)
                      (generated.fragmentEndpoint
                        ⟨occurrence.nodeInverse candidate.node selected,
                          candidate.port⟩)
                      candidate := by
                intro candidate selected portRequired
                let sourceEndpoint :
                    CEndpoint compiled.checked.val.diagram.nodeCount :=
                  ⟨occurrence.nodeInverse candidate.node selected,
                    candidate.port⟩
                have fragmentAllocated :
                    generated.fragmentNode sourceEndpoint.node =
                      Fin.natAdd
                        (Removal.nodes occurrence).length
                        sourceEndpoint.node :=
                  Fin.ext (by
                    simp [generated,
                      ConcreteSpliceAttachment.fragmentNode])
                have nodeAllocation :
                    (nodeEquiv occurrence).toFun
                        (generated.fragmentEndpoint sourceEndpoint).node =
                      candidate.node := by
                  change
                    nodeForward occurrence
                        (generated.fragmentNode sourceEndpoint.node) =
                      candidate.node
                  rw [fragmentAllocated]
                  change
                    nodeForward occurrence
                        (Fin.natAdd (Removal.nodes occurrence).length
                          (occurrence.nodeInverse
                            candidate.node selected)) =
                      candidate.node
                  rw [nodeForward_fragmentNode occurrence]
                  exact occurrence.node_right_inverse
                    candidate.node selected
                have sourceNodeRelation :=
                  occurrence.extractedNode_rename sourceEndpoint.node
                have nodeTableRelation :
                    host.val.nodes
                        ((nodeEquiv occurrence).toFun
                          (generated.fragmentEndpoint sourceEndpoint).node) =
                      CNode.rename (regionEquiv occurrence)
                        (generated.diagram.nodes
                          (generated.fragmentEndpoint
                            sourceEndpoint).node) := by
                  calc
                    host.val.nodes
                        ((nodeEquiv occurrence).toFun
                          (generated.fragmentEndpoint
                            sourceEndpoint).node) =
                        host.val.nodes
                          (occurrence.nodeMap sourceEndpoint.node) := by
                      apply congrArg host.val.nodes
                      change
                        (nodeEquiv occurrence).toFun
                            (generated.fragmentEndpoint
                              sourceEndpoint).node =
                          occurrence.nodeMap sourceEndpoint.node
                      change
                        nodeForward occurrence
                            (generated.fragmentNode
                              sourceEndpoint.node) =
                          occurrence.nodeMap sourceEndpoint.node
                      rw [fragmentAllocated]
                      exact nodeForward_fragmentNode occurrence
                        sourceEndpoint.node
                    _ = mapNode occurrence.regionMap
                          (compiled.checked.val.diagram.nodes
                            sourceEndpoint.node) := by
                      simpa [ExtractionCompilation.checked,
                        checkedExtraction,
                        Occurrence.extractedOpen,
                        Occurrence.extractedDiagram] using
                        sourceNodeRelation
                    _ = CNode.rename (regionEquiv occurrence)
                          (ConcreteSpliceAttachment.renameFragmentNode
                            generated sourceEndpoint.node) :=
                      (renamedFragmentNode_rename occurrence compiled
                        removed generated sourceEndpoint.node).symm
                    _ = CNode.rename (regionEquiv occurrence)
                          (generated.diagram.nodes
                            (generated.fragmentEndpoint
                              sourceEndpoint).node) := by
                      simp [ConcreteSpliceAttachment.fragmentEndpoint]
                refine portCorresponds_of_renamed_node
                  (left := generated.diagram) (right := host.val)
                  (regions := regionEquiv occurrence)
                  (nodes := nodeEquiv occurrence)
                  (endpoint := generated.fragmentEndpoint sourceEndpoint)
                  (candidate := candidate)
                  nodeAllocation.symm nodeTableRelation portRequired ?_
                rfl
              have retainedCorresponds :
                  ∀ (sourceEndpoint :
                      CEndpoint removed.complement.val.nodeCount)
                    (portRequired :
                      (Removal.sourceEndpoint occurrence
                        sourceEndpoint).port ∈
                        host.val.requiredPorts
                          (Removal.sourceEndpoint occurrence
                            sourceEndpoint).node),
                    PortCorresponds generated.diagram host.val
                      (nodeEquiv occurrence)
                      (generated.hostEndpoint sourceEndpoint)
                      (Removal.sourceEndpoint occurrence
                        sourceEndpoint) := by
                intro sourceEndpoint portRequired
                have hostAllocated :
                    generated.hostNode sourceEndpoint.node =
                      Fin.castAdd pattern.val.nodeCount
                        sourceEndpoint.node :=
                  Fin.ext (by
                    simp [generated,
                      ConcreteSpliceAttachment.hostNode])
                have nodeAllocation :
                    (nodeEquiv occurrence).toFun
                        (generated.hostEndpoint sourceEndpoint).node =
                      (Removal.sourceEndpoint occurrence
                        sourceEndpoint).node := by
                  change
                    nodeForward occurrence
                        (generated.hostNode sourceEndpoint.node) =
                      Removal.sourceNode occurrence sourceEndpoint.node
                  rw [hostAllocated]
                  exact nodeForward_hostNode occurrence sourceEndpoint.node
                have sourceNodeRelation :=
                  Removal.diagramNode_rename occurrence sourceEndpoint.node
                have nodeTableRelation :
                    host.val.nodes
                        ((nodeEquiv occurrence).toFun
                          (generated.hostEndpoint sourceEndpoint).node) =
                      CNode.rename (regionEquiv occurrence)
                        (generated.diagram.nodes
                          (generated.hostEndpoint sourceEndpoint).node) := by
                  calc
                    host.val.nodes
                        ((nodeEquiv occurrence).toFun
                          (generated.hostEndpoint sourceEndpoint).node) =
                        host.val.nodes
                          (Removal.sourceNode occurrence
                            sourceEndpoint.node) :=
                      congrArg host.val.nodes nodeAllocation
                    _ = mapNode (Removal.sourceRegion occurrence)
                          (removed.complement.val.nodes
                            sourceEndpoint.node) := by
                      simpa only [RemovalResult.complement] using
                        sourceNodeRelation
                    _ = CNode.rename (regionEquiv occurrence)
                          (ConcreteSpliceAttachment.renameHostNode
                            generated sourceEndpoint.node) :=
                      (renamedHostNode_rename occurrence compiled
                        removed generated sourceEndpoint.node).symm
                    _ = CNode.rename (regionEquiv occurrence)
                          (generated.diagram.nodes
                            (generated.hostEndpoint
                              sourceEndpoint).node) := by
                      simp [ConcreteSpliceAttachment.hostEndpoint]
                refine portCorresponds_of_renamed_node
                  (left := generated.diagram) (right := host.val)
                  (regions := regionEquiv occurrence)
                  (nodes := nodeEquiv occurrence)
                  (endpoint := generated.hostEndpoint sourceEndpoint)
                  (candidate :=
                    Removal.sourceEndpoint occurrence sourceEndpoint)
                  nodeAllocation.symm nodeTableRelation portRequired ?_
                rfl
              intro wire
              refine Fin.addCases ?_ ?_ wire
              · intro retained candidate incident
                have hostIncident :
                    candidate ∈
                      (host.val.wires
                        (Removal.sourceWire occurrence retained)).endpoints := by
                  change
                    candidate ∈
                      (host.val.wires
                        ((attachmentWireEquiv occurrence compiled removed
                          generated).toFun
                          (generated.hostWire retained))).endpoints at incident
                  rw [attachmentWireEquiv_hostWire occurrence compiled
                    removed generated retained] at incident
                  exact incident
                have external :
                    (host.val.wires
                      (Removal.sourceWire occurrence retained)).scope ∉
                        occurrence.selection.regions :=
                  of_decide_eq_true
                    (List.mem_filter.mp
                      (List.get_mem
                        (Removal.wires occurrence) retained)).2
                by_cases selected :
                    candidate.node ∈ occurrence.selection.nodes
                · have selectedWire :
                      Removal.sourceWire occurrence retained ∈
                        occurrence.selection.wires :=
                    occurrence.selection.incident_wire_selected
                      (Removal.sourceWire occurrence retained)
                      ⟨candidate, hostIncident, selected⟩
                  let source :=
                    occurrence.wireInverse
                      (Removal.sourceWire occurrence retained)
                      selectedWire
                  have sourceMap :
                      occurrence.wireMap source =
                        Removal.sourceWire occurrence retained :=
                    occurrence.wire_right_inverse
                      (Removal.sourceWire occurrence retained)
                      selectedWire
                  let sourceEndpoint :
                      CEndpoint compiled.checked.val.diagram.nodeCount :=
                    ⟨occurrence.nodeInverse candidate.node selected,
                      candidate.port⟩
                  have sourceIncident :
                      sourceEndpoint ∈
                        (compiled.checked.val.diagram.wires
                          source).endpoints := by
                    have pushed :
                        occurrence.pushEndpoint sourceEndpoint =
                          candidate := by
                      dsimp [sourceEndpoint]
                      exact Occurrence.pushEndpoint_pull
                        occurrence candidate selected
                    have extractedIncident :
                        sourceEndpoint ∈
                          (occurrence.extractedWire source).endpoints :=
                      (occurrence.extractedEndpoint_mem_iff
                        source sourceEndpoint).mpr (by
                          rw [pushed]
                          rw [sourceMap]
                          exact hostIncident)
                    simpa [ExtractionCompilation.checked,
                      checkedExtraction, Occurrence.extractedOpen,
                      Occurrence.extractedDiagram] using extractedIncident
                  have generatedMember :=
                    generated.fragmentEndpoint_mem_generated rfl
                      source sourceEndpoint sourceIncident
                  have mappedWire :
                      generated.fragmentWire source =
                        generated.hostWire retained := by
                    apply
                      (attachmentWireEquiv occurrence compiled removed
                        generated).injective
                    rw [attachmentWireEquiv_fragmentWire occurrence
                      compiled removed generated generatedAccepted source]
                    rw [attachmentWireEquiv_hostWire occurrence compiled
                      removed generated retained]
                    exact sourceMap
                  rw [mappedWire] at generatedMember
                  refine
                    ⟨generated.fragmentEndpoint sourceEndpoint, ?_, ?_⟩
                  · unfold ConcreteSpliceAttachment.diagram
                      ConcreteSpliceAttachment.wireTable
                    simp only [Fin.addCases_left]
                    exact List.mem_append_right _ generatedMember
                  · have portRequired :=
                      ConcreteDiagram.incident_port_required _
                        host.val host.property
                        (Removal.sourceWire occurrence retained)
                        candidate hostIncident
                    exact fragmentCorresponds
                      candidate selected portRequired
                · have retainedNode :
                      candidate.node ∈ Removal.nodes occurrence := by
                    simp [Removal.nodes, ConcreteDiagram.nodesList,
                      Data.Finite.mem_allFin, selected]
                  let sourceEndpoint :
                      CEndpoint removed.complement.val.nodeCount :=
                    ⟨Removal.nodeIndex occurrence candidate.node
                        retainedNode,
                      candidate.port⟩
                  have sourceEquality :
                      Removal.sourceEndpoint occurrence sourceEndpoint =
                        candidate :=
                    Removal.sourceEndpoint_index occurrence candidate
                      retainedNode
                  have sourceIncident :
                      sourceEndpoint ∈
                        (removed.complement.val.wires
                          retained).endpoints := by
                    apply (Removal.diagramEndpoint_mem_iff occurrence
                      retained sourceEndpoint).mpr
                    simpa only [RemovalResult.complement,
                      sourceEquality] using hostIncident
                  refine
                    ⟨generated.hostEndpoint sourceEndpoint, ?_, ?_⟩
                  · unfold ConcreteSpliceAttachment.diagram
                      ConcreteSpliceAttachment.wireTable
                    simp only [Fin.addCases_left]
                    apply List.mem_append_left
                    exact List.mem_map.mpr
                      ⟨sourceEndpoint, sourceIncident, rfl⟩
                  · have portRequired :=
                      ConcreteDiagram.incident_port_required _
                        host.val host.property
                        (Removal.sourceWire occurrence retained)
                        (Removal.sourceEndpoint occurrence sourceEndpoint)
                        (by simpa only [sourceEquality] using hostIncident)
                    simpa only [sourceEquality] using
                      (retainedCorresponds sourceEndpoint portRequired)
              · intro fresh candidate incident
                let source :=
                  generated.fragmentInternalWires.get fresh
                have hostIncident :
                    candidate ∈
                      (host.val.wires
                        (occurrence.wireMap source)).endpoints := by
                  change
                    candidate ∈
                      (host.val.wires
                        ((attachmentWireEquiv occurrence compiled removed
                          generated).toFun
                          (generated.freshWire fresh))).endpoints at incident
                  rw [attachmentWireEquiv_freshWire occurrence compiled
                    removed generated fresh] at incident
                  exact incident
                have sourceMember :
                    source ∈ generated.fragmentInternalWires :=
                  List.get_mem _ fresh
                have sourceFresh : source ∈ freshWires occurrence := by
                  rw [← fragmentInternalWires_eq_freshWires occurrence
                    compiled removed generated]
                  exact sourceMember
                have internal :
                    (host.val.wires
                      (occurrence.wireMap source)).scope ∈
                        occurrence.selection.regions :=
                  of_decide_eq_true
                    (List.mem_filter.mp sourceFresh).2
                have selected :
                    candidate.node ∈ occurrence.selection.nodes :=
                  occurrence.selection.internal_endpoint_selected
                    (occurrence.wireMap source) candidate
                    internal hostIncident
                let sourceEndpoint :
                    CEndpoint compiled.checked.val.diagram.nodeCount :=
                  ⟨occurrence.nodeInverse candidate.node selected,
                    candidate.port⟩
                have sourceIncident :
                    sourceEndpoint ∈
                      (compiled.checked.val.diagram.wires
                        source).endpoints := by
                  have pushed :
                      occurrence.pushEndpoint sourceEndpoint =
                        candidate := by
                    dsimp [sourceEndpoint]
                    exact Occurrence.pushEndpoint_pull
                      occurrence candidate selected
                  have extractedIncident :
                      sourceEndpoint ∈
                        (occurrence.extractedWire source).endpoints :=
                    (occurrence.extractedEndpoint_mem_iff
                      source sourceEndpoint).mpr (by
                        rw [pushed]
                        exact hostIncident)
                  simpa [ExtractionCompilation.checked,
                    checkedExtraction, Occurrence.extractedOpen,
                    Occurrence.extractedDiagram] using extractedIncident
                have generatedMember :=
                  generated.fragmentEndpoint_mem_generated rfl
                    source sourceEndpoint sourceIncident
                have mappedWire :
                    generated.fragmentWire source =
                      generated.freshWire fresh := by
                  apply
                    (attachmentWireEquiv occurrence compiled removed
                      generated).injective
                  rw [attachmentWireEquiv_fragmentWire occurrence
                    compiled removed generated generatedAccepted source]
                  rw [attachmentWireEquiv_freshWire occurrence compiled
                    removed generated fresh]
                rw [mappedWire] at generatedMember
                refine
                  ⟨generated.fragmentEndpoint sourceEndpoint, ?_, ?_⟩
                · unfold ConcreteSpliceAttachment.diagram
                    ConcreteSpliceAttachment.wireTable
                  simp only [Fin.addCases_right]
                  exact generatedMember
                · have portRequired :=
                    ConcreteDiagram.incident_port_required _
                      host.val host.property
                      (occurrence.wireMap source)
                      candidate hostIncident
                  exact fragmentCorresponds
                    candidate selected portRequired }
    · contradiction
  · contradiction

end Reconstruction

end VisualProof
