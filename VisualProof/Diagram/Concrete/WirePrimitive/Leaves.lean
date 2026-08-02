import VisualProof.Diagram.Concrete.WirePrimitive.Arguments

namespace VisualProof

namespace ConcreteWirePrimitive

open ConcreteWireQuantifier
open WirePrimitive

namespace LeafConstruction

/-- Dense survivor order followed by the checker-owned replacement order. -/
def partitionOrder (selected : List (Fin count)) : List (Fin count) :=
  (Data.Finite.allFin count).filter (fun value => decide (value ∉ selected)) ++
    selected

theorem partitionOrder_nodup
    (selected : List (Fin count))
    (selectedNodup : selected.Nodup) :
    (partitionOrder selected).Nodup := by
  rw [partitionOrder, List.nodup_append]
  refine ⟨(Data.Finite.allFin_nodup count).filter _, selectedNodup, ?_⟩
  intro value retained candidate selectedMember same
  subst candidate
  exact (of_decide_eq_true (List.mem_filter.mp retained).2) selectedMember

theorem partitionOrder_complete
    (selected : List (Fin count))
    (value : Fin count) :
    value ∈ partitionOrder selected := by
  rw [partitionOrder, List.mem_append]
  by_cases selectedMember : value ∈ selected
  · exact Or.inr selectedMember
  · exact Or.inl (List.mem_filter.mpr
      ⟨Data.Finite.mem_allFin value, decide_eq_true selectedMember⟩)

/-- A duplicate-free complete identifier order is an executable carrier
equivalence.  Its inverse is the dense position in that supplied order; no
identifier permutation is searched for. -/
def enumerationEquiv
    (values : List α)
    [DecidableEq α]
    (nodup : values.Nodup)
    (complete : ∀ value : α, value ∈ values) :
    Data.Finite.FiniteEquiv (Fin values.length) α where
  toFun := values.get
  invFun := fun value => DenseList.index values value (complete value)
  left_inv := by
    intro position
    exact DenseList.index_get values nodup position
  right_inv := by
    intro value
    exact DenseList.get_index values value (complete value)

/-- Canonical partition/reappend equivalence selected by a checked node list. -/
def partitionEquiv
    (selected : List (Fin count))
    (selectedNodup : selected.Nodup) :
    Data.Finite.FiniteEquiv
      (Fin (partitionOrder selected).length) (Fin count) :=
  enumerationEquiv (partitionOrder selected)
    (partitionOrder_nodup selected selectedNodup)
    (partitionOrder_complete selected)

/-- A supplied finite carrier equivalence determines the corresponding dense
cardinality equality. -/
theorem finCount_eq
    (equiv : Data.Finite.FiniteEquiv (Fin left) (Fin right)) :
    left = right := by
  apply Nat.le_antisymm
  · exact Data.Finite.fin_card_le_of_injective equiv equiv.injective
  · exact Data.Finite.fin_card_le_of_injective equiv.invFun (by
      intro first second equality
      have := congrArg equiv.toFun equality
      simpa only [equiv.right_inv] using this)

/-- Extend an explicitly supplied carrier equivalence with one distinguished
last identifier on each side. -/
def addLastEquiv
    (equiv : Data.Finite.FiniteEquiv (Fin left) (Fin right)) :
    Data.Finite.FiniteEquiv (Fin (left + 1)) (Fin (right + 1)) where
  toFun := Fin.lastCases (Fin.last right)
    (fun value => Fin.castSucc (equiv value))
  invFun := Fin.lastCases (Fin.last left)
    (fun value => Fin.castSucc (equiv.symm value))
  left_inv := by
    intro value
    refine Fin.lastCases ?_ (fun predecessor => ?_) value
    · simp
    · simp only [Fin.lastCases_castSucc]
      rw [Data.Finite.FiniteEquiv.symm_apply_apply]
  right_inv := by
    intro value
    refine Fin.lastCases ?_ (fun predecessor => ?_) value
    · simp
    · simp only [Fin.lastCases_castSucc]
      rw [Data.Finite.FiniteEquiv.apply_symm_apply]

end LeafConstruction

/-- Stable refusal outcomes for formal, identity, and reference leaves. -/
inductive LeafError
  | expectedRelation
  | nonAppliedEndpoint
  | invalidPosition
  | formalSignature
  | identityArity
  | identitySignature
  | definitionSignature
  | emptySelection
  | duplicateSelection
  | wrongNodeKind
  | sharedShape
  | scopeDoesNotEnclose
  | invalidRemoval
  | malformedTarget (error : WFError)
  deriving Repr, DecidableEq

private def siteNodes
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sites : AllAppliedSites source wire) :
    List source.val.NodeId :=
  sites.sites.map AppliedSite.node

/-- Checker-owned local leaf shape selected for one rewritten application. -/
inductive LeafShape
    (source : CheckedDiagram definitions)
  | formal
      (arguments : List Sig)
      (head : source.val.WireId)
      (rest : List source.val.WireId)
  | identity
      (signature : Sig)
      (arguments : List source.val.WireId)
  | reference
      (definition : Fin definitions.length)
      (arguments : List Sig)
      (wires : List source.val.WireId)

/-- Exact retained-wire attachments and generated ports of a leaf shape. -/
def LeafShape.ports :
    LeafShape source → List (source.val.WireId × CPort)
  | .formal _ head rest =>
      (head, .head) ::
        (rest.zipIdx.map fun pair => (pair.1, .arg pair.2))
  | .identity _ arguments =>
      arguments.zipIdx.map fun pair => (pair.1, .identity pair.2)
  | .reference _ _ wires =>
      wires.zipIdx.map fun pair => (pair.1, .arg pair.2)

private structure LeafSpec
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sites : AllAppliedSites source wire) where
  shapes : Fin sites.sites.length → LeafShape source

private structure LeafPlan
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sites : AllAppliedSites source wire)
    (spec : LeafSpec source wire sites) where
  removal :
    Internal.BatchRemovalPlan source [] (siteNodes sites) [wire]

private def leafBase
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : LeafSpec source wire sites}
    (plan : LeafPlan source wire sites spec) :
    ConcreteDiagram definitions.length :=
  Internal.batchRemovalCandidate plan.removal

private def leafRegion
    (source : CheckedDiagram definitions)
    (region : source.val.RegionId) :
    Fin (Internal.retainedRegions source []).length :=
  Internal.retainedRegionIndex source [] region (by
    unfold Internal.retainedRegions
    apply List.mem_filter.mpr
    exact ⟨Data.Finite.mem_allFin _, by simp⟩)

private def leafNode
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : LeafSpec source wire sites}
    (plan : LeafPlan source wire sites spec)
    (site : Fin sites.sites.length) :
    Fin ((leafBase plan).nodeCount + sites.sites.length) :=
  Fin.natAdd (leafBase plan).nodeCount site

private def leafNodeData
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : LeafSpec source wire sites}
    (plan : LeafPlan source wire sites spec)
    (site : Fin sites.sites.length) :
    CNode (leafBase plan).regionCount definitions.length :=
  let region := leafRegion source (sites.sites.get site).region
  match spec.shapes site with
  | .formal arguments _ _ => .atom region arguments
  | .identity signature arguments =>
      .identity region signature arguments.length
  | .reference definition arguments _ =>
      .ref region definition arguments

private def leafEndpoints
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : LeafSpec source wire sites}
    (plan : LeafPlan source wire sites spec)
    (candidate : Fin (Internal.retainedWires source [wire]).length) :
    List
      (CEndpoint
        ((leafBase plan).nodeCount + sites.sites.length)) :=
  let sourceWire := Internal.sourceRetainedWire source [wire] candidate
  (Data.Finite.allFin sites.sites.length).flatMap fun site =>
    (spec.shapes site).ports.filterMap fun attachment =>
      if attachment.1 = sourceWire then
        some
          { node := leafNode plan site
            port := attachment.2 }
      else
        none

private def leafCandidate
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    {spec : LeafSpec source wire sites}
    (plan : LeafPlan source wire sites spec) :
    ConcreteDiagram definitions.length :=
  let base := leafBase plan
  {
    regionCount := base.regionCount
    nodeCount := base.nodeCount + sites.sites.length
    wireCount := base.wireCount
    root := base.root
    regions := base.regions
    nodes := Fin.addCases base.nodes (leafNodeData plan)
    wires := fun candidate =>
      let data := base.wires candidate
      { sig := data.sig
        scope := data.scope
        endpoints :=
          (data.endpoints.map fun endpoint =>
            { node := Fin.castAdd sites.sites.length endpoint.node
              port := endpoint.port }) ++
            leafEndpoints plan candidate }
  }

/-- Opaque checked result of consuming all applied heads into leaf nodes. -/
structure LeafResult
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) where
  private mk ::
  sites : AllAppliedSites source wire
  checked : CheckedDiagram definitions
  private spec : LeafSpec source wire sites
  private plan : LeafPlan source wire sites spec
  private generated : checked.val = leafCandidate plan

namespace LeafResult

def target
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire) :
    CheckedDiagram definitions :=
  result.checked

/-- Exact checker-selected leaf shape at one ordered source site. -/
def shapeAt
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire)
    (site : Fin result.sites.sites.length) :
    LeafShape source :=
  result.spec.shapes site

/-- Canonical checked region image of one source region. -/
def targetRegion
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire)
    (region : source.val.RegionId) :
    result.checked.val.RegionId :=
  Internal.checkedRegion result.generated (leafRegion source region)

/-- Canonical checked leaf node generated for one ordered source site. -/
def targetNode
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire)
    (site : Fin result.sites.sites.length) :
    result.checked.val.NodeId :=
  Internal.checkedNode result.generated (leafNode result.plan site)

/-- Source applications consumed by the leaf rewrite. -/
def sourceRemovedNodes
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire) :
    List source.val.NodeId :=
  siteNodes result.sites

/-- Target leaf nodes introduced by the rewrite. -/
def targetRemovedNodes
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
  (result : LeafResult source wire) :
    List result.checked.val.NodeId :=
  (Data.Finite.allFin result.sites.sites.length).map result.targetNode

/-- The consumed relation is the only source-local wire removed. -/
def sourceRemovedWires
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (_result : LeafResult source wire) :
    List source.val.WireId :=
  [wire]

/-- Leaf introduction creates no target-local wire. -/
def targetRemovedWires
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (_result : LeafResult source wire) :
    List _result.checked.val.WireId :=
  []

/-- Checked target image of the acted relation scope. -/
def targetScope
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire) :
    result.checked.val.RegionId :=
  result.targetRegion (source.val.wires wire).scope

theorem siteCount
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire) :
    result.sites.sites.length =
      (source.val.wires wire).endpoints.length :=
  result.sites.length

/-- Construction-owned target-to-source region carrier.  Leaf construction
removes no regions, so dense positions are preserved exactly. -/
def regionOriginEquiv
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire) :
    Data.Finite.FiniteEquiv result.checked.val.RegionId source.val.RegionId :=
  finEquivOfEq (by
    rw [congrArg ConcreteDiagram.regionCount result.generated]
    change (Internal.retainedRegions source []).length = _
    rw [Internal.retainedRegions_nil]
    simp [ConcreteDiagram.regionsList,
      Data.Finite.allFin_eq_finRange])

/-- The canonical target image of a source region has that exact source
origin. -/
@[simp] theorem regionOriginEquiv_targetRegion
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire)
    (region : source.val.RegionId) :
    result.regionOriginEquiv (result.targetRegion region) = region := by
  apply Fin.ext
  unfold regionOriginEquiv targetRegion finEquivOfEq
    Internal.checkedRegion
  change (leafRegion source region).val = region.val
  let sourcePosition : Fin source.val.regionsList.length :=
    Fin.cast (by
      simp [ConcreteDiagram.regionsList,
        Data.Finite.allFin_eq_finRange]) region
  let position : Fin (Internal.retainedRegions source []).length :=
    Fin.cast
      (congrArg List.length (Internal.retainedRegions_nil source)).symm
      sourcePosition
  have getExact :
      (Internal.retainedRegions source []).get position = region := by
    rw [get_of_list_eq (Internal.retainedRegions_nil source) sourcePosition]
    exact allFin_get region
  have indexExact : leafRegion source region = position := by
    unfold leafRegion Internal.retainedRegionIndex
    rw [← getExact]
    exact DenseList.index_get _
      (by
        rw [Internal.retainedRegions_nil]
        exact Data.Finite.allFin_nodup _)
      position
  exact congrArg Fin.val indexExact

/-- The canonical region image is exactly the inverse neutral-origin map. -/
theorem targetRegion_eq_regionOriginEquiv_symm
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire)
    (region : source.val.RegionId) :
    result.targetRegion region = result.regionOriginEquiv.symm region := by
  apply result.regionOriginEquiv.injective
  rw [result.regionOriginEquiv_targetRegion]
  exact result.regionOriginEquiv.right_inv region

/-- The target root is the canonical image of the source root. -/
theorem targetRoot_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire) :
    result.checked.val.root = result.targetRegion source.val.root := by
  unfold targetRegion
  calc
    result.checked.val.root =
        Internal.checkedRegion result.generated
          (leafCandidate result.plan).root :=
      Internal.checkedRoot_transport result.generated
    _ = Internal.checkedRegion result.generated
          (leafRegion source source.val.root) := by
      congr 1

/-- Region constructors and cut parents are transported exactly by the
construction-owned region origin equivalence. -/
theorem targetRegion_data
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire)
    (region : source.val.RegionId) :
    result.checked.val.regions (result.targetRegion region) =
      (source.val.regions region).rename result.regionOriginEquiv.symm := by
  unfold targetRegion
  change
    result.checked.val.regions
        (Internal.checkedRegionEquiv result.generated
          (leafRegion source region)) = _
  rw [Internal.checkedRegion_data_equiv]
  have candidateExact :
      (leafCandidate result.plan).regions (leafRegion source region) =
        (source.val.regions region).rename
          (Internal.noRegionRemovalEquiv source) := by
    change
      (Internal.batchRemovalCandidate result.plan.removal).regions
          (leafRegion source region) = _
    rw [show leafRegion source region =
        Internal.noRegionRemovalEquiv source region by
          apply Fin.ext
          rfl]
    exact Internal.batchRegionTable_noRegions result.plan.removal region
  rw [candidateExact]
  cases data : source.val.regions region with
  | sheet => rfl
  | cut parent =>
      simp only [CRegion.rename]
      congr 1
      rw [show Internal.checkedRegionEquiv result.generated
            (Internal.noRegionRemovalEquiv source parent) =
          result.targetRegion parent by
            unfold targetRegion
            congr 1]
      exact result.targetRegion_eq_regionOriginEquiv_symm parent

private theorem sourceNodesNodup
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire) :
    (siteNodes result.sites).Nodup := by
  have endpointsNodup := result.sites.endpoints_nodup
  have general : ∀ values : List (AppliedSite source wire),
      (values.map AppliedSite.endpoint).Nodup →
        (values.map AppliedSite.node).Nodup := by
    intro values
    induction values with
    | nil => simp
    | cons head tail induction =>
        simp only [List.map_cons, List.nodup_cons]
        rintro ⟨headFresh, tailNodup⟩
        constructor
        · intro headMember
          obtain ⟨candidate, candidateMember, nodeExact⟩ :=
            List.mem_map.mp headMember
          apply headFresh
          apply List.mem_map.mpr
          refine ⟨candidate, candidateMember, ?_⟩
          unfold AppliedSite.endpoint
          exact congrArg (fun node => CEndpoint.mk node .head) nodeExact
        · exact induction tailNodup
  exact general result.sites.sites endpointsNodup

/-- Construction-owned target-to-source node carrier.  Retained nodes occur
first and consumed applications are reintroduced in their checked endpoint
order. -/
def nodeOriginEquiv
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire) :
    Data.Finite.FiniteEquiv result.checked.val.NodeId source.val.NodeId :=
  (finEquivOfEq (by
    rw [congrArg ConcreteDiagram.nodeCount result.generated]
    simp [leafCandidate, leafBase, Internal.batchRemovalCandidate,
      LeafConstruction.partitionOrder, Internal.retainedNodes, siteNodes,
      ConcreteDiagram.nodesList])).trans
    (LeafConstruction.partitionEquiv (siteNodes result.sites)
      result.sourceNodesNodup)

/-- Canonical checked image of a source node retained by leaf construction. -/
def retainedNodeImage
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire)
    (node : source.val.NodeId)
    (retained : node ∉ siteNodes result.sites) :
    result.checked.val.NodeId :=
  Internal.checkedNode result.generated
    (Fin.castAdd result.sites.sites.length
      (Internal.retainedNodeIndex source (siteNodes result.sites) node (by
        unfold Internal.retainedNodes
        apply List.mem_filter.mpr
        exact ⟨Data.Finite.mem_allFin node, decide_eq_true retained⟩)))

/-- A retained target-node image has exactly its supplied source-node
origin. -/
@[simp] theorem nodeOriginEquiv_retainedNodeImage
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire)
    (node : source.val.NodeId)
    (retained : node ∉ siteNodes result.sites) :
    result.nodeOriginEquiv (result.retainedNodeImage node retained) = node := by
  let member : node ∈ Internal.retainedNodes source
      (siteNodes result.sites) := by
    unfold Internal.retainedNodes
    apply List.mem_filter.mpr
    exact ⟨Data.Finite.mem_allFin node, decide_eq_true retained⟩
  let retainedIndex := Internal.retainedNodeIndex source
    (siteNodes result.sites) node member
  unfold retainedNodeImage
  change result.nodeOriginEquiv
      (Internal.checkedNode result.generated
        (Fin.castAdd result.sites.sites.length retainedIndex)) = node
  unfold nodeOriginEquiv LeafConstruction.partitionEquiv
    LeafConstruction.enumerationEquiv finEquivOfEq
  simp only [Data.Finite.FiniteEquiv.trans_apply]
  simp [leafCandidate, leafBase, Internal.batchRemovalCandidate,
    LeafConstruction.partitionOrder]
  have checkedNodeVal :
      (Internal.checkedNode result.generated
        (Fin.castAdd result.sites.sites.length retainedIndex)).val =
      retainedIndex.val := by rfl
  have retainedListExact :
      (Data.Finite.allFin source.val.nodeCount).filter
          (fun value => !decide (value ∈ siteNodes result.sites)) =
        Internal.retainedNodes source (siteNodes result.sites) := by
    simp [Internal.retainedNodes, ConcreteDiagram.nodesList]
  rw [List.getElem_append_left]
  · simpa only [retainedListExact, checkedNodeVal,
        List.get_eq_getElem] using
      (Internal.sourceRetainedNode_retainedNodeIndex source
        (siteNodes result.sites) node member)
  · calc
      (Internal.checkedNode result.generated
          (Fin.castAdd result.sites.sites.length retainedIndex)).val =
          retainedIndex.val := by rfl
      _ < (Internal.retainedNodes source
            (siteNodes result.sites)).length := retainedIndex.isLt
      _ = ((Data.Finite.allFin source.val.nodeCount).filter
          (fun value => !decide
            (value ∈ siteNodes result.sites))).length :=
        (congrArg List.length retainedListExact).symm

/-- Retained node constructors and payloads are transported exactly through
the neutral region origin. -/
theorem retainedNodeImage_data
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire)
    (node : source.val.NodeId)
    (retained : node ∉ siteNodes result.sites) :
    result.checked.val.nodes (result.retainedNodeImage node retained) =
      (source.val.nodes node).rename result.regionOriginEquiv.symm := by
  unfold retainedNodeImage
  rw [Internal.checkedNode_data_transport]
  let member : node ∈ Internal.retainedNodes source
      (siteNodes result.sites) := by
    unfold Internal.retainedNodes
    apply List.mem_filter.mpr
    exact ⟨Data.Finite.mem_allFin node, decide_eq_true retained⟩
  let retainedIndex :=
    Internal.retainedNodeIndex source (siteNodes result.sites) node member
  unfold leafCandidate
  simp only [Fin.addCases_left]
  change
    Internal.checkedNodeData result.generated
        (Internal.batchNodeTable result.plan.removal retainedIndex) = _
  rw [Internal.batchNodeTable_noRegions]
  have sourceExact :
      Internal.sourceRetainedNode source (siteNodes result.sites)
          retainedIndex = node :=
    Internal.sourceRetainedNode_retainedNodeIndex source
      (siteNodes result.sites) node member
  rw [sourceExact]
  cases data : source.val.nodes node <;>
    simp only [CNode.rename, Internal.checkedNodeData]
  all_goals
    congr 1
    calc
      Internal.checkedRegion result.generated
          (Internal.noRegionRemovalEquiv source _) =
          result.targetRegion _ := by
        unfold targetRegion
        congr 1
      _ = result.regionOriginEquiv.symm _ :=
        result.targetRegion_eq_regionOriginEquiv_symm _

/-- The generated target node at an ordered site has that site's consumed
source application as its exact neutral origin. -/
@[simp] theorem nodeOriginEquiv_targetNode
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire)
    (site : Fin result.sites.sites.length) :
    result.nodeOriginEquiv (result.targetNode site) =
      (result.sites.sites.get site).node := by
  unfold nodeOriginEquiv targetNode LeafConstruction.partitionEquiv
    LeafConstruction.enumerationEquiv finEquivOfEq
  simp only [Data.Finite.FiniteEquiv.trans_apply]
  simp [leafNode, leafBase, Internal.batchRemovalCandidate,
    LeafConstruction.partitionOrder, siteNodes,
    Data.Finite.allFin_eq_finRange]
  have checkedNodeVal : (Internal.checkedNode result.generated
        (Fin.natAdd
          (Internal.retainedNodes source
            (List.map AppliedSite.node result.sites.sites)).length site)).val =
      (Internal.retainedNodes source
          (List.map AppliedSite.node result.sites.sites)).length +
        site.val := by rfl
  rw [List.getElem_append_right]
  · simp only [checkedNodeVal]
    simp [Internal.retainedNodes, ConcreteDiagram.nodesList,
      Data.Finite.allFin_eq_finRange]
  · rw [checkedNodeVal]
    simp [Internal.retainedNodes, ConcreteDiagram.nodesList,
      Data.Finite.allFin_eq_finRange]

/-- Generated leaf payloads are exactly the checker-selected local shape at
the canonical source-region image. -/
theorem targetNode_data
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire)
    (site : Fin result.sites.sites.length) :
    result.checked.val.nodes (result.targetNode site) =
      match result.shapeAt site with
      | .formal arguments _ _ =>
          .atom (result.targetRegion
            (result.sites.sites.get site).region) arguments
      | .identity signature arguments =>
          .identity (result.targetRegion
            (result.sites.sites.get site).region) signature arguments.length
      | .reference definition arguments _ =>
          .ref (result.targetRegion
            (result.sites.sites.get site).region) definition arguments := by
  unfold targetNode shapeAt targetRegion
  rw [Internal.checkedNode_data_transport]
  unfold leafCandidate leafNode
  simp only [Fin.addCases_right]
  unfold leafNodeData
  split <;> rfl

/-- Neutral origin of a target wire: precisely one source wire other than the
consumed relation. -/
abbrev WireOrigin
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :=
  { sourceWire : source.val.WireId // sourceWire ≠ wire }

private theorem wireOrigin_mem
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (origin : WireOrigin source wire) :
    origin.1 ∈ Internal.retainedWires source [wire] := by
  unfold Internal.retainedWires
  apply List.mem_filter.mpr
  exact ⟨Data.Finite.mem_allFin origin.1, by simp [origin.2]⟩

private theorem sourceRetainedWire_ne
    {source : CheckedDiagram definitions}
    (wire : source.val.WireId)
    (candidate : Fin (Internal.retainedWires source [wire]).length) :
    Internal.sourceRetainedWire source [wire] candidate ≠ wire := by
  have member := List.get_mem (Internal.retainedWires source [wire]) candidate
  have survives := (List.mem_filter.mp member).2
  have notRemoved :
      Internal.sourceRetainedWire source [wire] candidate ∉ [wire] := by
    exact of_decide_eq_true survives
  simpa using notRemoved

/-- Direct construction-owned target-wire classifier.  Its inverse is dense
retained-wire allocation; no isomorphism is searched for. -/
def wireOriginEquiv
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire) :
    Data.Finite.FiniteEquiv result.checked.val.WireId
      (WireOrigin source wire) where
  toFun := fun targetWire =>
    let candidate : Fin (Internal.retainedWires source [wire]).length :=
      Fin.cast (congrArg ConcreteDiagram.wireCount result.generated) targetWire
    ⟨Internal.sourceRetainedWire source [wire] candidate,
      sourceRetainedWire_ne wire candidate⟩
  invFun := fun origin =>
    Internal.checkedWire result.generated
      (Internal.retainedWireIndex source [wire] origin.1
        (wireOrigin_mem origin))
  left_inv := by
    intro targetWire
    apply Fin.ext
    simp only [Internal.checkedWire]
    rw [Internal.retainedWireIndex_sourceRetainedWire]
    rfl
  right_inv := by
    intro origin
    apply Subtype.ext
    exact Internal.sourceRetainedWire_retainedWireIndex source [wire] origin.1
      (wireOrigin_mem origin)

/-- Canonical checked image of one retained source-wire origin. -/
def targetWireImage
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire)
    (origin : WireOrigin source wire) :
    result.checked.val.WireId :=
  result.wireOriginEquiv.symm origin

@[simp] theorem wireOriginEquiv_targetWireImage
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire)
    (origin : WireOrigin source wire) :
    result.wireOriginEquiv (result.targetWireImage origin) = origin :=
  result.wireOriginEquiv.apply_symm_apply origin

/-- Retained wire signatures are unchanged. -/
theorem targetWireImage_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire)
    (origin : WireOrigin source wire) :
    (result.checked.val.wires (result.targetWireImage origin)).sig =
      (source.val.wires origin.1).sig := by
  unfold targetWireImage Data.Finite.FiniteEquiv.symm wireOriginEquiv
  rw [Internal.checkedWire_signature_transport]
  change
    (Internal.batchWireTable result.plan.removal
      (Internal.retainedWireIndex source [wire] origin.1
        (wireOrigin_mem origin))).sig = _
  rw [Internal.batchWireTable_signature,
    Internal.sourceRetainedWire_retainedWireIndex]

/-- Retained wire scopes are transported by the canonical region image. -/
theorem targetWireImage_scope
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire)
    (origin : WireOrigin source wire) :
    (result.checked.val.wires (result.targetWireImage origin)).scope =
      result.targetRegion (source.val.wires origin.1).scope := by
  unfold targetWireImage Data.Finite.FiniteEquiv.symm wireOriginEquiv
    targetRegion
  rw [Internal.checkedWire_scope_transport]
  change Internal.checkedRegion result.generated
      (Internal.batchWireTable result.plan.removal
        (Internal.retainedWireIndex source [wire] origin.1
          (wireOrigin_mem origin))).scope = _
  rw [Internal.batchWireTable_scope]
  simp only [Internal.sourceRetainedWire_retainedWireIndex]
  congr 1

/-- Target-to-source endpoint carrier induced by the exact neutral node
origin; ports are preserved verbatim. -/
def endpointOriginEquiv
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire) :
    Data.Finite.FiniteEquiv
      (CEndpoint result.checked.val.nodeCount)
      (CEndpoint source.val.nodeCount) where
  toFun := fun endpoint =>
    ⟨result.nodeOriginEquiv endpoint.node, endpoint.port⟩
  invFun := fun endpoint =>
    ⟨result.nodeOriginEquiv.symm endpoint.node, endpoint.port⟩
  left_inv := by
    intro endpoint
    cases endpoint with
    | mk node port =>
        congr
        exact result.nodeOriginEquiv.left_inv node
  right_inv := by
    intro endpoint
    cases endpoint with
    | mk node port =>
        congr
        exact result.nodeOriginEquiv.right_inv node

/-- Retained batch endpoints of one target wire, transported through leaf
node extension and checker acceptance. -/
def retainedTargetEndpoints
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire)
    (origin : WireOrigin source wire) :
    List (CEndpoint result.checked.val.nodeCount) :=
  let candidate := Internal.retainedWireIndex source [wire] origin.1
    (wireOrigin_mem origin)
  (Internal.batchWireTable result.plan.removal candidate).endpoints.map
    (fun endpoint => Internal.checkedEndpoint result.generated
      { node := Fin.castAdd result.sites.sites.length endpoint.node
        port := endpoint.port })

/-- Shape-selected generated attachments of one retained target wire. -/
def targetAttachments
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire)
    (origin : WireOrigin source wire) :
    List (CEndpoint result.checked.val.nodeCount) :=
  let candidate := Internal.retainedWireIndex source [wire] origin.1
    (wireOrigin_mem origin)
  (leafEndpoints result.plan candidate).map
    (Internal.checkedEndpoint result.generated)

/-- The generated-attachment table is exactly the ordered per-site leaf-shape
port table for this source-wire origin. -/
theorem targetAttachments_shape
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire)
    (origin : WireOrigin source wire) :
    result.targetAttachments origin =
      (Data.Finite.allFin result.sites.sites.length).flatMap fun site =>
        (result.shapeAt site).ports.filterMap fun attachment =>
          if attachment.1 = origin.1 then
            some
              { node := result.targetNode site
                port := attachment.2 }
          else
            none := by
  unfold targetAttachments leafEndpoints shapeAt targetNode
  simp only [Internal.sourceRetainedWire_retainedWireIndex]
  have mapPorts : ∀ (site : Fin result.sites.sites.length)
      (attachments : List (source.val.WireId × CPort)),
      ((attachments.filterMap fun attachment =>
          if attachment.1 = origin.1 then
            some
              ({ node := leafNode result.plan site
                 port := attachment.2 } :
                CEndpoint (leafCandidate result.plan).nodeCount)
          else none).map (Internal.checkedEndpoint result.generated)) =
        attachments.filterMap fun attachment =>
          if attachment.1 = origin.1 then
            some
              { node := Internal.checkedNode result.generated
                  (leafNode result.plan site)
                port := attachment.2 }
          else none := by
    intro site attachments
    induction attachments with
    | nil => rfl
    | cons attachment tail induction =>
        by_cases exact : attachment.1 = origin.1
        · simp [exact, induction, Internal.checkedEndpoint]
        · simp [exact, induction]
  induction Data.Finite.allFin result.sites.sites.length with
  | nil => rfl
  | cons site sites induction =>
      change
        List.map (Internal.checkedEndpoint result.generated)
            (((result.spec.shapes site).ports.filterMap fun attachment =>
              if attachment.1 = origin.1 then
                some
                  ({ node := leafNode result.plan site
                     port := attachment.2 } :
                    CEndpoint (leafCandidate result.plan).nodeCount)
              else none) ++
            (sites.flatMap fun nextSite =>
              (result.spec.shapes nextSite).ports.filterMap fun attachment =>
                if attachment.1 = origin.1 then
                  some
                    { node := leafNode result.plan nextSite
                      port := attachment.2 }
                else none)) = _
      rw [List.map_append, List.flatMap_cons]
      congr 1
      · exact mapPorts site (result.spec.shapes site).ports

/-- Exact ordered endpoint table for every retained target wire. -/
theorem targetWireImage_endpoints
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire)
    (origin : WireOrigin source wire) :
    (result.checked.val.wires
        (result.targetWireImage origin)).endpoints =
      result.retainedTargetEndpoints origin ++
        result.targetAttachments origin := by
  unfold targetWireImage Data.Finite.FiniteEquiv.symm wireOriginEquiv
    retainedTargetEndpoints targetAttachments
  rw [Internal.checkedWire_endpoints_transport]
  unfold leafCandidate
  simp only [List.map_append]
  congr 1
  unfold leafBase Internal.batchRemovalCandidate
  simp only [List.map_map]
  apply List.map_congr_left
  intro endpoint _member
  rfl

/-- Neutral endpoint list of one retained wire.  Together with
`targetAttachments_shape`, this is the exact shape-aware target-to-origin
incidence table. -/
def originEndpoints
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire)
    (origin : WireOrigin source wire) :
    List (CEndpoint source.val.nodeCount) :=
  (result.checked.val.wires
      (result.targetWireImage origin)).endpoints.map
    result.endpointOriginEquiv

/-- The neutral endpoint list decomposes into retained incidence followed by
the exact shape-selected generated attachments. -/
theorem originEndpoints_decomposition
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire)
    (origin : WireOrigin source wire) :
    result.originEndpoints origin =
      (result.retainedTargetEndpoints origin).map
          result.endpointOriginEquiv ++
        (result.targetAttachments origin).map
          result.endpointOriginEquiv := by
  unfold originEndpoints
  rw [result.targetWireImage_endpoints, List.map_append]

/-- Bidirectional endpoint fiber between one retained target wire and its
neutral source-node origins. -/
structure EndpointFiberEquiv
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire)
    (origin : WireOrigin source wire) where
  equivalence :
    Data.Finite.FiniteEquiv
      { endpoint // endpoint ∈
        (result.checked.val.wires
          (result.targetWireImage origin)).endpoints }
      { endpoint // endpoint ∈ result.originEndpoints origin }
  forward_exact : ∀ endpoint,
    (equivalence endpoint).1 = result.endpointOriginEquiv endpoint.1
  inverse_exact : ∀ endpoint,
    (equivalence.symm endpoint).1 =
      result.endpointOriginEquiv.symm endpoint.1

/-- The canonical endpoint fiber is obtained by restricting the explicit
endpoint-origin equivalence; both directions are construction-owned. -/
def endpointFiberEquiv
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire)
    (origin : WireOrigin source wire) :
    EndpointFiberEquiv result origin where
  equivalence :=
    { toFun := fun endpoint =>
        ⟨result.endpointOriginEquiv endpoint.1,
          List.mem_map.mpr ⟨endpoint.1, endpoint.2, rfl⟩⟩
      invFun := fun endpoint =>
        ⟨result.endpointOriginEquiv.symm endpoint.1, by
          rcases List.mem_map.mp endpoint.2 with
            ⟨targetEndpoint, targetMember, exact⟩
          have targetExact :
              targetEndpoint =
                result.endpointOriginEquiv.symm endpoint.1 := by
            apply result.endpointOriginEquiv.injective
            rw [result.endpointOriginEquiv.apply_symm_apply]
            exact exact
          simpa only [targetExact] using targetMember⟩
      left_inv := by
        intro endpoint
        apply Subtype.ext
        exact result.endpointOriginEquiv.left_inv endpoint.1
      right_inv := by
        intro endpoint
        apply Subtype.ext
        exact result.endpointOriginEquiv.right_inv endpoint.1 }
  forward_exact := by intro; rfl
  inverse_exact := by intro; rfl

/-- The target wires followed by the consumed relation recover the complete
source wire carrier in the checker-owned dense order. -/
def extendedWireOriginEquiv
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire) :
    Data.Finite.FiniteEquiv
      (Fin (result.checked.val.wireCount + 1)) source.val.WireId :=
  (finEquivOfEq (by
    rw [congrArg ConcreteDiagram.wireCount result.generated]
    simp [leafCandidate, leafBase, Internal.batchRemovalCandidate,
      LeafConstruction.partitionOrder, Internal.retainedWires,
      ConcreteDiagram.wiresList])).trans
    (LeafConstruction.partitionEquiv [wire] (by simp))

end LeafResult

private def checkedSites
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :
    Except LeafError (AllAppliedSites source wire) :=
  match checkAllAppliedSites source wire with
  | none => .error .nonAppliedEndpoint
  | some sites => .ok sites

private def relationArguments
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :
    Except LeafError (List Sig) :=
  match (source.val.wires wire).sig with
  | .iota => .error .expectedRelation
  | .rel arguments => .ok arguments

private def buildLeaf
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sites : AllAppliedSites source wire)
    (spec : LeafSpec source wire sites) :
    Except LeafError (LeafResult source wire) := by
  match Internal.checkBatchRemovalPlan? source [] (siteNodes sites) [wire] with
  | none => exact .error .invalidRemoval
  | some removal =>
      let plan : LeafPlan source wire sites spec := ⟨removal⟩
      let candidate := leafCandidate plan
      match accepted :
          ConcreteDiagram.checkWellFormed definitions candidate with
      | .error error => exact .error (.malformedTarget error)
      | .ok checked =>
          have generated : checked.val = candidate :=
            ConcreteDiagram.checkWellFormed_preserves_input accepted
          exact .ok ⟨sites, checked, spec, plan, generated⟩

/-- Consume every `W(z, ȳ)` as the per-site application `z(ȳ)`. -/
def applyFormal
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat) :
    Except LeafError (LeafResult source wire) := do
  let arguments ← relationArguments source wire
  if positionValid : position < arguments.length then
    let restSignatures := ConcreteWirePrimitive.eraseAt arguments position
    if formalExact :
        arguments[position]? = some (.rel restSignatures) then
      let sites ← checkedSites source wire
      let spec : LeafSpec source wire sites :=
        { shapes := fun site =>
            let applied := sites.sites.get site
            .formal restSignatures
              ((applied.arguments[position]?).getD wire)
              (ConcreteWirePrimitive.eraseAt applied.arguments position) }
      buildLeaf source wire sites spec
    else
      throw .formalSignature
  else
    throw .invalidPosition

/-- Consume every application as an identity node over equal arguments. -/
def identityLeaf
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :
    Except LeafError (LeafResult source wire) := do
  let arguments ← relationArguments source wire
  if arity : 2 ≤ arguments.length then
    match arguments with
    | [] => throw .identityArity
    | signature :: rest =>
        if rest.all fun candidate => candidate == signature then
          let sites ← checkedSites source wire
          let spec : LeafSpec source wire sites :=
            { shapes := fun site =>
                .identity signature (sites.sites.get site).arguments }
          buildLeaf source wire sites spec
        else
          throw .identitySignature
  else
    throw .identityArity

/-- Consume every application as one folded reference to a stored definition. -/
def refLeaf
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (definition : Fin definitions.length) :
    Except LeafError (LeafResult source wire) := do
  let arguments ← relationArguments source wire
  if exact : arguments = definitions.get definition then
    let sites ← checkedSites source wire
    let spec : LeafSpec source wire sites :=
      { shapes := fun site =>
          .reference definition arguments
            (sites.sites.get site).arguments }
    buildLeaf source wire sites spec
  else
    throw .definitionSignature

/-- Checker-owned selected-node abstraction specification. -/
private structure AbstractSpec
    (source : CheckedDiagram definitions) where
  nodes : List source.val.NodeId
  nodesNodup : nodes.Nodup
  scope : source.val.RegionId
  targetArguments : List Sig
  arguments : Fin nodes.length → List source.val.WireId

private structure AbstractPlan
    (source : CheckedDiagram definitions)
    (spec : AbstractSpec source) where
  removal :
    Internal.BatchRemovalPlan source [] spec.nodes []

private def abstractBase
    {source : CheckedDiagram definitions}
    {spec : AbstractSpec source}
    (plan : AbstractPlan source spec) :
    ConcreteDiagram definitions.length :=
  Internal.batchRemovalCandidate plan.removal

private def abstractNode
    {source : CheckedDiagram definitions}
    {spec : AbstractSpec source}
    (plan : AbstractPlan source spec)
    (site : Fin spec.nodes.length) :
    Fin ((abstractBase plan).nodeCount + spec.nodes.length) :=
  Fin.natAdd (abstractBase plan).nodeCount site

private def abstractArgumentEndpoints
    {source : CheckedDiagram definitions}
    {spec : AbstractSpec source}
    (plan : AbstractPlan source spec)
    (candidate : Fin (Internal.retainedWires source []).length) :
    List
      (CEndpoint
        ((abstractBase plan).nodeCount + spec.nodes.length)) :=
  let sourceWire := Internal.sourceRetainedWire source [] candidate
  (Data.Finite.allFin spec.nodes.length).flatMap fun site =>
    (spec.arguments site).zipIdx.filterMap fun pair =>
      if pair.1 = sourceWire then
        some
          { node := abstractNode plan site
            port := .arg pair.2 }
      else
        none

private def abstractCandidate
    {source : CheckedDiagram definitions}
    {spec : AbstractSpec source}
    (plan : AbstractPlan source spec) :
    ConcreteDiagram definitions.length :=
  let base := abstractBase plan
  {
    regionCount := base.regionCount
    nodeCount := base.nodeCount + spec.nodes.length
    wireCount := base.wireCount + 1
    root := base.root
    regions := base.regions
    nodes :=
      Fin.addCases base.nodes fun site =>
        .atom
          (leafRegion source (source.val.nodes (spec.nodes.get site)).region)
          spec.targetArguments
    wires :=
      Fin.addCases
        (fun candidate =>
          let data := base.wires candidate
          { sig := data.sig
            scope := data.scope
            endpoints :=
              (data.endpoints.map fun endpoint =>
                { node := Fin.castAdd spec.nodes.length endpoint.node
                  port := endpoint.port }) ++
                abstractArgumentEndpoints plan candidate })
        (fun _ =>
          { sig := .rel spec.targetArguments
            scope := leafRegion source spec.scope
            endpoints :=
              (Data.Finite.allFin spec.nodes.length).map fun site =>
                { node := abstractNode plan site
                  port := .head } })
  }

private def abstractCandidateWire
    {source : CheckedDiagram definitions}
    {spec : AbstractSpec source}
    (plan : AbstractPlan source spec) :
    (abstractCandidate plan).WireId :=
  ⟨(abstractBase plan).wireCount, by
    simp only [abstractCandidate]
    omega⟩

/-- Opaque checked result of abstracting the exact selected leaf set. -/
structure LeafAbstractResult
    (source : CheckedDiagram definitions) where
  private mk ::
  checked : CheckedDiagram definitions
  private spec : AbstractSpec source
  private plan : AbstractPlan source spec
  private generated : checked.val = abstractCandidate plan
  targetWire : checked.val.WireId
  private targetWire_exact :
    targetWire =
      Internal.checkedWire generated (abstractCandidateWire plan)

namespace LeafAbstractResult

def target
    {source : CheckedDiagram definitions}
    (result : LeafAbstractResult source) :
    CheckedDiagram definitions :=
  result.checked

/-- Target applications introduced for the selected source leaves. -/
def targetNodes
    {source : CheckedDiagram definitions}
    (result : LeafAbstractResult source) :
    List result.checked.val.NodeId :=
  (Data.Finite.allFin result.spec.nodes.length).map fun site =>
    Internal.checkedNode result.generated (abstractNode result.plan site)

def selectedNodes
    {source : CheckedDiagram definitions}
    (result : LeafAbstractResult source) :
    List source.val.NodeId :=
  result.spec.nodes

def targetArguments
    {source : CheckedDiagram definitions}
    (result : LeafAbstractResult source) :
    List Sig :=
  result.spec.targetArguments

theorem targetWire_signature
    {source : CheckedDiagram definitions}
    (result : LeafAbstractResult source) :
    (result.checked.val.wires result.targetWire).sig =
      .rel result.targetArguments := by
  rw [result.targetWire_exact,
    Internal.checkedWire_signature_transport result.generated]
  have targetExact :
      abstractCandidateWire result.plan =
        Fin.natAdd (abstractBase result.plan).wireCount
          (0 : Fin 1) := by
    apply Fin.ext
    rfl
  rw [targetExact]
  simp only [abstractCandidate, Fin.addCases_right]
  rfl

/-- Construction-owned target-to-source region carrier for abstraction. -/
def regionOriginEquiv
    {source : CheckedDiagram definitions}
    (result : LeafAbstractResult source) :
    Data.Finite.FiniteEquiv result.checked.val.RegionId source.val.RegionId :=
  finEquivOfEq (by
    rw [congrArg ConcreteDiagram.regionCount result.generated]
    change (Internal.retainedRegions source []).length = _
    rw [Internal.retainedRegions_nil]
    simp [ConcreteDiagram.regionsList,
      Data.Finite.allFin_eq_finRange])

/-- Construction-owned target-to-source node carrier for abstraction. -/
def nodeOriginEquiv
    {source : CheckedDiagram definitions}
    (result : LeafAbstractResult source) :
    Data.Finite.FiniteEquiv result.checked.val.NodeId source.val.NodeId :=
  (finEquivOfEq (by
    rw [congrArg ConcreteDiagram.nodeCount result.generated]
    simp [abstractCandidate, abstractBase, Internal.batchRemovalCandidate,
      LeafConstruction.partitionOrder, Internal.retainedNodes,
      ConcreteDiagram.nodesList])).trans
    (LeafConstruction.partitionEquiv result.spec.nodes
      result.spec.nodesNodup)

/-- Abstraction retains every source wire in dense order and appends exactly
the fresh uniformly applied relation. -/
def wireSplitEquiv
    {source : CheckedDiagram definitions}
    (result : LeafAbstractResult source) :
    Data.Finite.FiniteEquiv result.checked.val.WireId
      (Fin (source.val.wireCount + 1)) :=
  finEquivOfEq (by
    rw [congrArg ConcreteDiagram.wireCount result.generated]
    change (Internal.retainedWires source []).length + 1 = _
    have retained : Internal.retainedWires source [] =
        source.val.wiresList := by
      apply List.filter_eq_self.mpr
      intro candidate member
      simp
    rw [retained]
    simp [ConcreteDiagram.wiresList,
      Data.Finite.allFin_eq_finRange])

end LeafAbstractResult

private def buildAbstract
    (source : CheckedDiagram definitions)
    (spec : AbstractSpec source) :
    Except LeafError (LeafAbstractResult source) := by
  match Internal.checkBatchRemovalPlan? source [] spec.nodes [] with
  | none => exact .error .invalidRemoval
  | some removal =>
      let plan : AbstractPlan source spec := ⟨removal⟩
      let candidate := abstractCandidate plan
      match accepted :
          ConcreteDiagram.checkWellFormed definitions candidate with
      | .error error => exact .error (.malformedTarget error)
      | .ok checked =>
          have generated : checked.val = candidate :=
            ConcreteDiagram.checkWellFormed_preserves_input accepted
          exact .ok
            ⟨checked, spec, plan, generated,
              Internal.checkedWire generated
                (abstractCandidateWire plan),
              rfl⟩

private structure CheckedSelection
    (source : CheckedDiagram definitions)
    (nodes : List source.val.NodeId)
    (scope : source.val.RegionId) : Type where
  nodesNodup : nodes.Nodup

private def checkedSelection
    (source : CheckedDiagram definitions)
    (nodes : List source.val.NodeId)
    (scope : source.val.RegionId) :
    Except LeafError (CheckedSelection source nodes scope) := do
  if nodes.isEmpty then
    throw .emptySelection
  if nodesNodup : nodes.Nodup then
    if !(nodes.all fun node =>
        source.val.Encloses scope (source.val.nodes node).region) then
      throw .scopeDoesNotEnclose
    pure ⟨nodesNodup⟩
  else
    throw .duplicateSelection

private def portOwners?
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    : List CPort → Option (List source.val.WireId)
  | [] => some []
  | port :: ports => do
      let wire ← source.val.endpointOwner? ⟨node, port⟩
      let rest ← portOwners? source node ports
      pure (wire :: rest)

private def atomArgumentPorts
    (arguments : List Sig) :
    List CPort :=
  arguments.zipIdx.map fun pair => .arg pair.2

private def identityPorts
    (arity : Nat) :
    List CPort :=
  (List.range arity).map .identity

private def collectArguments?
    (source : CheckedDiagram definitions)
    (ports : source.val.NodeId → List CPort) :
    (nodes : List source.val.NodeId) →
      Option { arguments : List (List source.val.WireId) //
        arguments.length = nodes.length }
  | [] => some ⟨[], rfl⟩
  | node :: nodes => do
      let head ← portOwners? source node (ports node)
      let tail ← collectArguments? source ports nodes
      pure ⟨head :: tail.1, by simp [tail.2]⟩

private def collectedAt
    {source : CheckedDiagram definitions}
    {nodes : List source.val.NodeId}
    (collected : { arguments : List (List source.val.WireId) //
      arguments.length = nodes.length })
    (site : Fin nodes.length) :
    List source.val.WireId :=
  collected.1.get (Fin.cast collected.2.symm site)

/--
Abstract selected equal-signature atoms.  Their heads may be distinct; each
becomes the leading formal argument of one fresh uniformly applied wire.
-/
def abstractFormal
    (source : CheckedDiagram definitions)
    (nodes : List source.val.NodeId)
    (scope : source.val.RegionId) :
    Except LeafError (LeafAbstractResult source) := do
  match nodes with
  | [] => throw .emptySelection
  | first :: rest =>
      let selected := first :: rest
      let selection ← checkedSelection source selected scope
      match source.val.nodes first with
      | .atom _ arguments =>
          if !(selected.all fun node =>
              match source.val.nodes node with
              | .atom _ candidate => candidate == arguments
              | _ => false) then
            throw .sharedShape
          let ports := fun (_ : source.val.NodeId) =>
            .head :: atomArgumentPorts arguments
          match collectArguments? source ports selected with
          | none => throw .wrongNodeKind
          | some collected =>
              let spec : AbstractSpec source :=
                { nodes := selected
                  nodesNodup := selection.nodesNodup
                  scope := scope
                  targetArguments := .rel arguments :: arguments
                  arguments := collectedAt collected }
              buildAbstract source spec
      | _ => throw .wrongNodeKind

/-- Abstract selected identity nodes with one shared signature and arity. -/
def identityAbstract
    (source : CheckedDiagram definitions)
    (nodes : List source.val.NodeId)
    (scope : source.val.RegionId) :
    Except LeafError (LeafAbstractResult source) := do
  match nodes with
  | [] => throw .emptySelection
  | first :: rest =>
      let selected := first :: rest
      let selection ← checkedSelection source selected scope
      match source.val.nodes first with
      | .identity _ signature arity =>
          if !(selected.all fun node =>
              match source.val.nodes node with
              | .identity _ candidateSignature candidateArity =>
                  candidateSignature == signature &&
                    candidateArity == arity
              | _ => false) then
            throw .sharedShape
          let ports := fun (_ : source.val.NodeId) => identityPorts arity
          match collectArguments? source ports selected with
          | none => throw .wrongNodeKind
          | some collected =>
              let spec : AbstractSpec source :=
                { nodes := selected
                  nodesNodup := selection.nodesNodup
                  scope := scope
                  targetArguments :=
                    (List.range arity).map fun _ => signature
                  arguments := collectedAt collected }
              buildAbstract source spec
      | _ => throw .wrongNodeKind

/-- Abstract selected folded references to one shared stored definition. -/
def refAbstract
    (source : CheckedDiagram definitions)
    (nodes : List source.val.NodeId)
    (scope : source.val.RegionId) :
    Except LeafError (LeafAbstractResult source) := do
  match nodes with
  | [] => throw .emptySelection
  | first :: rest =>
      let selected := first :: rest
      let selection ← checkedSelection source selected scope
      match source.val.nodes first with
      | .ref _ definition arguments =>
          if !(selected.all fun node =>
              match source.val.nodes node with
              | .ref _ candidateDefinition candidateArguments =>
                  candidateDefinition == definition &&
                    candidateArguments == arguments
              | _ => false) then
            throw .sharedShape
          let ports := fun (_ : source.val.NodeId) =>
            atomArgumentPorts arguments
          match collectArguments? source ports selected with
          | none => throw .wrongNodeKind
          | some collected =>
              let spec : AbstractSpec source :=
                { nodes := selected
                  nodesNodup := selection.nodesNodup
                  scope := scope
                  targetArguments := arguments
                  arguments := collectedAt collected }
              buildAbstract source spec
      | _ => throw .wrongNodeKind

end ConcreteWirePrimitive

end VisualProof
