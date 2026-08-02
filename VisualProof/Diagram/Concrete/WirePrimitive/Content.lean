import VisualProof.Rule.WirePrimitive.Site
import VisualProof.Diagram.Concrete.WireQuantifierBatchRemoval
import VisualProof.Diagram.Concrete.IsomorphismSearch

namespace VisualProof

namespace ConcreteWirePrimitive

open ConcreteWireQuantifier
open WirePrimitive

/-- One checked location at which an endpoint-free relation wire is spawned. -/
structure EndSite
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) where
  region : source.val.RegionId
  arguments : List source.val.WireId

/-- Concrete failures shared by the six content-shape transformations. -/
inductive ContentError
  | expectedRelation
  | nonAppliedEndpoint
  | emptySites
  | wireHasEndpoints
  | sameWire
  | signatureMismatch
  | scopeMismatch
  | nonExactCut
  | parallelMismatch
  | argumentArity
  | argumentSignature (position : Nat)
  | siteOutsideScope
  | argumentInvisible (position : Nat)
  | invalidRemoval
  | malformedTarget (error : WFError)
  | inverseDeleteRejected
  | inverseIsomorphismRejected
  deriving Repr, DecidableEq

private def siteNodes
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sites : List (AppliedSite source wire)) :
    List source.val.NodeId :=
  sites.map AppliedSite.node

private def removedSiteNodes
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sites : AllAppliedSites source wire) :
    List source.val.NodeId :=
  siteNodes sites.sites

namespace ContentConstruction

theorem length_filter_true (values : List α) :
    (values.filter fun _ => true).length = values.length := by
  induction values with
  | nil => rfl
  | cons head tail induction => simp [induction]

def finEquivOfEq (exact : left = right) :
    Data.Finite.FiniteEquiv (Fin left) (Fin right) where
  toFun := Fin.cast exact
  invFun := Fin.cast exact.symm
  left_inv := by
    intro value
    apply Fin.ext
    rfl
  right_inv := by
    intro value
    apply Fin.ext
    rfl

theorem finCount_eq
    (equiv : Data.Finite.FiniteEquiv (Fin left) (Fin right)) :
    left = right := by
  apply Nat.le_antisymm
  · exact Data.Finite.fin_card_le_of_injective equiv equiv.injective
  · exact Data.Finite.fin_card_le_of_injective equiv.invFun (by
      intro first second equality
      have lifted := congrArg equiv.toFun equality
      simpa only [equiv.right_inv] using lifted)

theorem map_get_allFin (values : List α) :
    (Data.Finite.allFin values.length).map values.get = values := by
  rw [Data.Finite.allFin_eq_finRange]
  unfold List.finRange
  rw [List.map_ofFn]
  simpa only [Function.comp_apply, List.get_eq_getElem] using
    (List.ofFn_getElem (xs := values))

theorem siteNodes_nodup
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sites : AllAppliedSites source wire) :
    (siteNodes sites.sites).Nodup := by
  have endpointsNodup := sites.endpoints_nodup
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
  exact general sites.sites endpointsNodup

/-- Dense survivor order followed by the checker-owned selected order. -/
def partitionOrder (selected : List (Fin count)) : List (Fin count) :=
  (Data.Finite.allFin count).filter (fun value => decide (value ∉ selected)) ++
    selected

private theorem partitionOrder_nodup
    (selected : List (Fin count))
    (selectedNodup : selected.Nodup) :
    (partitionOrder selected).Nodup := by
  rw [partitionOrder, List.nodup_append]
  refine ⟨(Data.Finite.allFin_nodup count).filter _, selectedNodup, ?_⟩
  intro value retained candidate selectedMember same
  subst candidate
  exact (of_decide_eq_true (List.mem_filter.mp retained).2) selectedMember

private theorem partitionOrder_complete
    (selected : List (Fin count))
    (value : Fin count) :
    value ∈ partitionOrder selected := by
  rw [partitionOrder, List.mem_append]
  by_cases selectedMember : value ∈ selected
  · exact Or.inr selectedMember
  · exact Or.inl (List.mem_filter.mpr
      ⟨Data.Finite.mem_allFin value, decide_eq_true selectedMember⟩)

/-- A checked selected list determines the survivor/replacement carrier. -/
def partitionEquiv
    (selected : List (Fin count))
    (selectedNodup : selected.Nodup) :
    Data.Finite.FiniteEquiv
      (Fin (partitionOrder selected).length) (Fin count) where
  toFun := (partitionOrder selected).get
  invFun := fun value =>
    DenseList.index (partitionOrder selected) value
      (partitionOrder_complete selected value)
  left_inv := by
    intro position
    exact DenseList.index_get _
      (partitionOrder_nodup selected selectedNodup) position
  right_inv := by
    intro value
    exact DenseList.get_index _ value (partitionOrder_complete selected value)

/-- Dense left-summand position of one carrier not in the selected suffix. -/
def retainedPosition
    (selected : List (Fin count))
    (value : Fin count)
    (retained : value ∉ selected) :
    Fin (partitionOrder selected).length := by
  let index := DenseList.index
    ((Data.Finite.allFin count).filter
      (fun candidate => decide (candidate ∉ selected)))
    value (List.mem_filter.mpr
      ⟨Data.Finite.mem_allFin value, decide_eq_true retained⟩)
  exact ⟨index.val, by
    unfold partitionOrder
    simp only [List.length_append]
    omega⟩

/-- Dense right-summand position of one selected carrier. -/
def selectedPosition
    (selected : List (Fin count))
    (position : Fin selected.length) :
    Fin (partitionOrder selected).length :=
  ⟨((Data.Finite.allFin count).filter
      (fun candidate => decide (candidate ∉ selected))).length +
      position.val, by
    unfold partitionOrder
    simp only [List.length_append]
    omega⟩

@[simp] theorem partitionEquiv_retainedPosition
    (selected : List (Fin count))
    (selectedNodup : selected.Nodup)
    (value : Fin count)
    (retained : value ∉ selected) :
    partitionEquiv selected selectedNodup
        (retainedPosition selected value retained) = value := by
  change (partitionOrder selected).get
      (retainedPosition selected value retained) = value
  unfold retainedPosition partitionOrder
  rw [List.get_eq_getElem, List.getElem_append_left]
  exact DenseList.get_index _ value
    (List.mem_filter.mpr
      ⟨Data.Finite.mem_allFin value, decide_eq_true retained⟩)

@[simp] theorem partitionEquiv_selectedPosition
    (selected : List (Fin count))
    (selectedNodup : selected.Nodup)
    (position : Fin selected.length) :
    partitionEquiv selected selectedNodup
        (selectedPosition selected position) = selected.get position := by
  change (partitionOrder selected).get
      (selectedPosition selected position) = selected.get position
  simp [selectedPosition, partitionOrder]

/-- Extend a supplied equivalence by the same ordered generated suffix. -/
def addRightEquiv
    (equiv : Data.Finite.FiniteEquiv (Fin left) (Fin right))
    (suffix : Nat) :
    Data.Finite.FiniteEquiv (Fin (left + suffix)) (Fin (right + suffix)) where
  toFun := Fin.addCases (fun value => Fin.castAdd suffix (equiv value))
    (fun value => Fin.natAdd right value)
  invFun := Fin.addCases (fun value => Fin.castAdd suffix (equiv.symm value))
    (fun value => Fin.natAdd left value)
  left_inv := by
    intro value
    apply Fin.ext
    refine Fin.addCases (m := left) (n := suffix)
      (fun item => ?_) (fun generated => ?_) value
    · simpa only [Fin.addCases_left] using
        congrArg Fin.val (equiv.left_inv item)
    · simp only [Fin.addCases_right]
  right_inv := by
    intro value
    apply Fin.ext
    refine Fin.addCases (m := right) (n := suffix)
      (fun item => ?_) (fun generated => ?_) value
    · simpa only [Fin.addCases_left] using
        congrArg Fin.val (equiv.right_inv item)
    · simp only [Fin.addCases_right]

end ContentConstruction

private def sourceRegionAfterRemoval
    {source : CheckedDiagram definitions}
    (removed : List source.val.RegionId)
    (region : source.val.RegionId)
    (retained : region ∈ Internal.retainedRegions source removed) :
    Fin (Internal.retainedRegions source removed).length :=
  Internal.retainedRegionIndex source removed region retained

private def retainedWireArgumentEndpoints
    {source : CheckedDiagram definitions}
    {acted : source.val.WireId}
    (_removedRegions : List source.val.RegionId)
    (removedNodes : List source.val.NodeId)
    (removedWires : List source.val.WireId)
    (sites : List (AppliedSite source acted))
    (nodeFor : Fin sites.length → CEndpoint
      ((Internal.retainedNodes source removedNodes).length + sites.length))
    (candidate : Fin (Internal.retainedWires source removedWires).length) :
    List (CEndpoint
      ((Internal.retainedNodes source removedNodes).length + sites.length)) :=
  let sourceWire :=
    Internal.sourceRetainedWire source removedWires candidate
  (Data.Finite.allFin sites.length).flatMap fun site =>
    (List.range (sites.get site).arguments.length).filterMap fun position =>
      match (sites.get site).arguments[position]? with
      | some argument =>
          if argument = sourceWire then
            some
              { node := (nodeFor site).node
                port := .arg position }
          else
            none
      | none => none

private def retainedWireDoubleArgumentEndpoints
    {source : CheckedDiagram definitions}
    {acted : source.val.WireId}
    (_removedRegions : List source.val.RegionId)
    (removedNodes : List source.val.NodeId)
    (removedWires : List source.val.WireId)
    (sites : List (AppliedSite source acted))
    (firstNode secondNode :
      Fin sites.length →
        Fin ((Internal.retainedNodes source removedNodes).length +
          (sites.length + sites.length)))
    (candidate : Fin (Internal.retainedWires source removedWires).length) :
    List (CEndpoint
      ((Internal.retainedNodes source removedNodes).length +
        (sites.length + sites.length))) :=
  let sourceWire :=
    Internal.sourceRetainedWire source removedWires candidate
  (Data.Finite.allFin sites.length).flatMap fun site =>
    (List.range (sites.get site).arguments.length).flatMap fun position =>
      match (sites.get site).arguments[position]? with
      | some argument =>
          if argument = sourceWire then
            [ { node := firstNode site, port := .arg position },
              { node := secondNode site, port := .arg position } ]
          else
            []
      | none => []

private structure CutWrapPlan
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sites : AllAppliedSites source wire) where
  removal :
    Internal.BatchRemovalPlan source [] (removedSiteNodes sites) [wire]

private def cutWrapBase
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    (plan : CutWrapPlan source wire sites) :
    ConcreteDiagram definitions.length :=
  Internal.batchRemovalCandidate plan.removal

private def cutWrapRegion
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    (plan : CutWrapPlan source wire sites)
    (site : Fin sites.sites.length) :
    Fin ((cutWrapBase plan).regionCount + sites.sites.length) :=
  Fin.natAdd (cutWrapBase plan).regionCount site

private def cutWrapNode
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    (plan : CutWrapPlan source wire sites)
    (site : Fin sites.sites.length) :
    Fin ((cutWrapBase plan).nodeCount + sites.sites.length) :=
  Fin.natAdd (cutWrapBase plan).nodeCount site

private def cutWrapCandidate
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    (signature : List Sig)
    (plan : CutWrapPlan source wire sites) :
    ConcreteDiagram definitions.length :=
  let base := cutWrapBase plan
  let count := sites.sites.length
  {
    regionCount := base.regionCount + count
    nodeCount := base.nodeCount + count
    wireCount := base.wireCount + 1
    root := Fin.castAdd count base.root
    regions :=
      Fin.addCases
        (fun region =>
          match base.regions region with
          | .sheet => .sheet
          | .cut parent => .cut (Fin.castAdd count parent))
        (fun site =>
          .cut
            (Fin.castAdd count
              (sourceRegionAfterRemoval (source := source) []
                (sites.sites.get site).region (by
                  unfold Internal.retainedRegions
                  apply List.mem_filter.mpr
                  exact ⟨Data.Finite.mem_allFin _, by simp⟩))))
    nodes :=
      Fin.addCases
        (fun node =>
          match base.nodes node with
          | .atom region args => .atom (Fin.castAdd count region) args
          | .ref region definition args =>
              .ref (Fin.castAdd count region) definition args
          | .identity region sig arity =>
              .identity (Fin.castAdd count region) sig arity)
        (fun site => .atom (cutWrapRegion plan site) signature)
    wires :=
      Fin.addCases
        (fun candidate =>
          let data := base.wires candidate
          { sig := data.sig
            scope := Fin.castAdd count data.scope
            endpoints :=
              (data.endpoints.map fun endpoint =>
                { node := Fin.castAdd count endpoint.node
                  port := endpoint.port }) ++
              retainedWireArgumentEndpoints (source := source)
                [] (removedSiteNodes sites)
                [wire] sites.sites
                (fun site =>
                  ({ node := cutWrapNode plan site, port := .head } :
                    CEndpoint (base.nodeCount + count)))
                candidate })
        (fun _ =>
          { sig := .rel signature
            scope :=
              Fin.castAdd count
                (sourceRegionAfterRemoval (source := source) []
                  (source.val.wires wire).scope (by
                    unfold Internal.retainedRegions
                    apply List.mem_filter.mpr
                    exact ⟨Data.Finite.mem_allFin _, by simp⟩))
            endpoints :=
              (Data.Finite.allFin count).map fun site =>
                { node := cutWrapNode plan site, port := .head } })
  }

private def cutWrapCandidateWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    (signature : List Sig)
    (plan : CutWrapPlan source wire sites) :
    (cutWrapCandidate signature plan).WireId :=
  ⟨(cutWrapBase plan).wireCount, by
    simp [cutWrapCandidate]⟩

/-- Checked result of wrapping every applied end in its own fresh cut. -/
structure CutWrapResult
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) where
  private mk ::
  sites : AllAppliedSites source wire
  checked : CheckedDiagram definitions
  private signature : List Sig
  private signature_exact : (source.val.wires wire).sig = .rel signature
  private plan : CutWrapPlan source wire sites
  private generated : checked.val = cutWrapCandidate signature plan
  targetWire : checked.val.WireId
  private targetWire_exact :
    targetWire =
      Internal.checkedWire generated (cutWrapCandidateWire signature plan)

namespace CutWrapResult

/-- Relation argument signature selected by the successful cut-wrap check. -/
def targetArguments
    (result : CutWrapResult source wire) : List Sig :=
  result.signature

/-- Canonical checked image of one source region retained by cut wrapping. -/
def targetRegion
    (result : CutWrapResult source wire)
    (region : source.val.RegionId) :
    result.checked.val.RegionId :=
  Internal.checkedRegion result.generated
    (Fin.castAdd result.sites.sites.length
      (Internal.noRegionRemovalEquiv source region))

/-- Canonical checked cut region generated for one ordered source site. -/
def targetCutRegion
    (result : CutWrapResult source wire)
    (site : Fin result.sites.sites.length) :
    result.checked.val.RegionId :=
  Internal.checkedRegion result.generated (cutWrapRegion result.plan site)

/-- Source application nodes consumed by cut wrapping. -/
def sourceRemovedNodes
    (result : CutWrapResult source wire) :
    List source.val.NodeId :=
  removedSiteNodes result.sites

/-- The acted relation is the only source wire consumed by cut wrapping. -/
def sourceRemovedWires
    (_result : CutWrapResult source wire) :
    List source.val.WireId :=
  [wire]

/-- Canonical checked image of one source node retained by cut wrapping. -/
def retainedNodeImage
    (result : CutWrapResult source wire)
    (node : source.val.NodeId)
    (retained : node ∉ result.sourceRemovedNodes) :
    result.checked.val.NodeId :=
  Internal.checkedNode result.generated
    (Fin.castAdd result.sites.sites.length
      (Internal.retainedNodeIndex source result.sourceRemovedNodes node (by
        unfold Internal.retainedNodes
        apply List.mem_filter.mpr
        exact ⟨Data.Finite.mem_allFin node, decide_eq_true retained⟩)))

/-- Canonical checked atom node generated for one ordered source site. -/
def targetNode
    (result : CutWrapResult source wire)
    (site : Fin result.sites.sites.length) :
    result.checked.val.NodeId :=
  Internal.checkedNode result.generated (cutWrapNode result.plan site)

/-- Canonical checked image of one source wire retained by cut wrapping. -/
def retainedWireImage
    (result : CutWrapResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ result.sourceRemovedWires) :
    result.checked.val.WireId :=
  Internal.checkedWire result.generated
    (Fin.castAdd 1
      (Internal.retainedWireIndex source result.sourceRemovedWires sourceWire
        (by
          unfold Internal.retainedWires
          apply List.mem_filter.mpr
          exact ⟨Data.Finite.mem_allFin sourceWire,
            decide_eq_true retained⟩)))

/-- Wrap checking identifies its checked region carrier with the original
regions followed by the exact generated-cut positions. -/
def extendedRegionOriginEquiv
    (result : CutWrapResult source wire) :
    Data.Finite.FiniteEquiv result.checked.val.RegionId
      (Fin (source.val.regionCount + result.sites.sites.length)) :=
  ContentConstruction.finEquivOfEq (by
    rw [congrArg ConcreteDiagram.regionCount result.generated]
    change (cutWrapBase result.plan).regionCount +
      result.sites.sites.length = _
    simp [cutWrapBase, Internal.batchRemovalCandidate,
      Internal.retainedRegions, ConcreteDiagram.regionsList,
      Data.Finite.allFin_eq_finRange,
      ContentConstruction.length_filter_true])

/-- A retained source region has its exact left-summand origin. -/
@[simp] theorem extendedRegionOriginEquiv_targetRegion
    (result : CutWrapResult source wire)
    (region : source.val.RegionId) :
    result.extendedRegionOriginEquiv (result.targetRegion region) =
      Fin.castAdd result.sites.sites.length region := by
  apply Fin.ext
  unfold extendedRegionOriginEquiv targetRegion
    ContentConstruction.finEquivOfEq Internal.checkedRegion
  change (sourceRegionAfterRemoval (source := source) [] region _).val =
    region.val
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
    simpa [position, sourcePosition, ConcreteDiagram.regionsList,
      Data.Finite.allFin_eq_finRange] using allFin_get region
  have regionRetained : region ∈ Internal.retainedRegions source [] := by
    rw [Internal.retainedRegions_nil]
    exact Data.Finite.mem_allFin region
  have indexExact :
      sourceRegionAfterRemoval (source := source) [] region regionRetained =
        position := by
    unfold sourceRegionAfterRemoval Internal.retainedRegionIndex
    have sameIndex :
        DenseList.index (Internal.retainedRegions source []) region
            regionRetained =
          DenseList.index (Internal.retainedRegions source [])
            ((Internal.retainedRegions source []).get position)
            (List.get_mem _ position) := by
      congr
      exact getExact.symm
    rw [sameIndex]
    exact DenseList.index_get _ (by
      rw [Internal.retainedRegions_nil]
      exact Data.Finite.allFin_nodup _) position
  exact congrArg Fin.val indexExact

/-- A generated cut has its exact right-summand site origin. -/
@[simp] theorem extendedRegionOriginEquiv_targetCutRegion
    (result : CutWrapResult source wire)
    (site : Fin result.sites.sites.length) :
    result.extendedRegionOriginEquiv (result.targetCutRegion site) =
      Fin.natAdd source.val.regionCount site := by
  apply Fin.ext
  unfold extendedRegionOriginEquiv targetCutRegion cutWrapRegion
    ContentConstruction.finEquivOfEq Internal.checkedRegion
  change (cutWrapBase result.plan).regionCount + site.val =
    source.val.regionCount + site.val
  congr 1
  exact Internal.batchRemovalCandidate_regionCount_noRegions
    result.plan.removal

/-- Exact checked-node allocation count for the retained/source-site
partition used by cut wrapping. -/
private theorem nodeCountExact
    (result : CutWrapResult source wire) :
    result.checked.val.nodeCount =
      (ContentConstruction.partitionOrder
        (removedSiteNodes result.sites)).length := by
  rw [congrArg ConcreteDiagram.nodeCount result.generated]
  simp [cutWrapCandidate, cutWrapBase,
    Internal.batchRemovalCandidate, ContentConstruction.partitionOrder,
    removedSiteNodes, siteNodes, Internal.retainedNodes,
    ConcreteDiagram.nodesList, Data.Finite.allFin_eq_finRange]

/-- Wrap checking reorders source nodes as retained nodes followed by the
exact acted-site nodes. -/
def nodeOriginEquiv
    (result : CutWrapResult source wire) :
    Data.Finite.FiniteEquiv result.checked.val.NodeId source.val.NodeId :=
  (ContentConstruction.finEquivOfEq (nodeCountExact result)).trans
    (ContentConstruction.partitionEquiv (removedSiteNodes result.sites)
      (ContentConstruction.siteNodes_nodup result.sites))

/-- A retained checked node has its supplied source-node origin. -/
@[simp] theorem nodeOriginEquiv_retainedNodeImage
    (result : CutWrapResult source wire)
    (node : source.val.NodeId)
    (retained : node ∉ result.sourceRemovedNodes) :
    result.nodeOriginEquiv (result.retainedNodeImage node retained) = node := by
  change node ∉ removedSiteNodes result.sites at retained
  unfold retainedNodeImage sourceRemovedNodes nodeOriginEquiv
  simp only [Data.Finite.FiniteEquiv.trans_apply]
  let allocated : Fin
      (ContentConstruction.partitionOrder
        (removedSiteNodes result.sites)).length :=
    Fin.cast (nodeCountExact result)
      (Internal.checkedNode result.generated
        (Fin.castAdd result.sites.sites.length
          (Internal.retainedNodeIndex source
            (removedSiteNodes result.sites) node (by
              unfold Internal.retainedNodes
              apply List.mem_filter.mpr
              exact ⟨Data.Finite.mem_allFin node,
                decide_eq_true retained⟩))))
  change
    ContentConstruction.partitionEquiv (removedSiteNodes result.sites)
        (ContentConstruction.siteNodes_nodup result.sites) allocated = node
  have allocatedExact : allocated =
      ContentConstruction.retainedPosition
        (removedSiteNodes result.sites) node retained := by
    apply Fin.ext
    rfl
  rw [allocatedExact]
  exact ContentConstruction.partitionEquiv_retainedPosition _ _ _ _

/-- A generated checked atom has the consumed source application at that
site as its exact neutral node origin. -/
@[simp] theorem nodeOriginEquiv_targetNode
    (result : CutWrapResult source wire)
    (site : Fin result.sites.sites.length) :
    result.nodeOriginEquiv (result.targetNode site) =
      (result.sites.sites.get site).node := by
  unfold nodeOriginEquiv targetNode ContentConstruction.finEquivOfEq
  simp only [Data.Finite.FiniteEquiv.trans_apply]
  let selectedSite : Fin (removedSiteNodes result.sites).length :=
    Fin.cast (by simp [removedSiteNodes, siteNodes]) site
  let allocated : Fin
      (ContentConstruction.partitionOrder
        (removedSiteNodes result.sites)).length :=
    Fin.cast (nodeCountExact result)
      (Internal.checkedNode result.generated
        (cutWrapNode result.plan site))
  change
    ContentConstruction.partitionEquiv (removedSiteNodes result.sites)
        (ContentConstruction.siteNodes_nodup result.sites) allocated =
      (result.sites.sites.get site).node
  have allocatedExact : allocated =
      ContentConstruction.selectedPosition
        (removedSiteNodes result.sites) selectedSite := by
    apply Fin.ext
    rfl
  rw [allocatedExact,
    ContentConstruction.partitionEquiv_selectedPosition]
  simp [selectedSite, removedSiteNodes, siteNodes]

/-- Exact checked-wire allocation count for the retained/acted partition
used by cut wrapping. -/
private theorem wireCountExact
    (result : CutWrapResult source wire) :
    result.checked.val.wireCount =
      (ContentConstruction.partitionOrder [wire]).length := by
  rw [congrArg ConcreteDiagram.wireCount result.generated]
  simp [cutWrapCandidate, cutWrapBase,
    Internal.batchRemovalCandidate, ContentConstruction.partitionOrder,
    Internal.retainedWires, ConcreteDiagram.wiresList,
    Data.Finite.allFin_eq_finRange,
    ContentConstruction.length_filter_true]

/-- Wrap checking reorders wires as retained wires followed by the acted
relation wire. -/
def wireOriginEquiv
    (result : CutWrapResult source wire) :
    Data.Finite.FiniteEquiv result.checked.val.WireId source.val.WireId :=
  (ContentConstruction.finEquivOfEq (wireCountExact result)).trans
      (ContentConstruction.partitionEquiv [wire] (by simp))

/-- A retained checked wire has its supplied source-wire origin. -/
@[simp] theorem wireOriginEquiv_retainedWireImage
    (result : CutWrapResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ result.sourceRemovedWires) :
    result.wireOriginEquiv
        (result.retainedWireImage sourceWire retained) = sourceWire := by
  change sourceWire ∉ [wire] at retained
  unfold retainedWireImage sourceRemovedWires wireOriginEquiv
  simp only [Data.Finite.FiniteEquiv.trans_apply]
  let allocated : Fin (ContentConstruction.partitionOrder [wire]).length :=
    Fin.cast (wireCountExact result)
      (Internal.checkedWire result.generated
        (Fin.castAdd 1
          (Internal.retainedWireIndex source [wire] sourceWire (by
            unfold Internal.retainedWires
            apply List.mem_filter.mpr
            exact ⟨Data.Finite.mem_allFin sourceWire,
              decide_eq_true retained⟩))))
  change ContentConstruction.partitionEquiv [wire] (by simp) allocated =
    sourceWire
  have allocatedExact : allocated =
      ContentConstruction.retainedPosition [wire] sourceWire retained := by
    apply Fin.ext
    rfl
  rw [allocatedExact]
  exact ContentConstruction.partitionEquiv_retainedPosition _ _ _ _

/-- The generated acted-wire witness has the consumed source relation as its
exact neutral wire origin. -/
@[simp] theorem wireOriginEquiv_targetWire
    (result : CutWrapResult source wire) :
    result.wireOriginEquiv result.targetWire = wire := by
  rw [result.targetWire_exact]
  unfold wireOriginEquiv ContentConstruction.finEquivOfEq
  simp only [Data.Finite.FiniteEquiv.trans_apply]
  let position : Fin ([wire] : List source.val.WireId).length := ⟨0, by simp⟩
  let allocated : Fin (ContentConstruction.partitionOrder [wire]).length :=
    Fin.cast (wireCountExact result)
      (Internal.checkedWire result.generated
        (cutWrapCandidateWire result.signature result.plan))
  change ContentConstruction.partitionEquiv [wire] (by simp) allocated = wire
  have allocatedExact : allocated =
      ContentConstruction.selectedPosition [wire] position := by
    apply Fin.ext
    rfl
  rw [allocatedExact,
    ContentConstruction.partitionEquiv_selectedPosition]
  simp [position]

/-- Canonical checked image of any source wire under the total cut-wrap
wire-origin classifier. -/
def targetWireImage
    (result : CutWrapResult source wire)
    (sourceWire : source.val.WireId) :
    result.checked.val.WireId :=
  result.wireOriginEquiv.symm sourceWire

@[simp] theorem wireOriginEquiv_targetWireImage
    (result : CutWrapResult source wire)
    (sourceWire : source.val.WireId) :
    result.wireOriginEquiv (result.targetWireImage sourceWire) = sourceWire :=
  result.wireOriginEquiv.apply_symm_apply sourceWire

/-- The total source-wire image agrees with the direct retained allocation. -/
theorem targetWireImage_eq_retainedWireImage
    (result : CutWrapResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ result.sourceRemovedWires) :
    result.targetWireImage sourceWire =
      result.retainedWireImage sourceWire retained := by
  apply result.wireOriginEquiv.injective
  rw [result.wireOriginEquiv_targetWireImage,
    result.wireOriginEquiv_retainedWireImage]

/-- The total source-wire image sends the acted relation to the generated
cut-wrap witness. -/
theorem targetWireImage_acted
    (result : CutWrapResult source wire) :
    result.targetWireImage wire = result.targetWire := by
  apply result.wireOriginEquiv.injective
  rw [result.wireOriginEquiv_targetWireImage,
    result.wireOriginEquiv_targetWire]

/-- The target root is the direct retained image of the source root. -/
theorem targetRoot_exact
    (result : CutWrapResult source wire) :
    result.checked.val.root = result.targetRegion source.val.root := by
  unfold targetRegion
  rw [Internal.checkedRoot_transport result.generated]
  congr 1

/-- Exact constructor and parent table for every retained source region. -/
theorem targetRegion_data
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : CutWrapResult source wire)
    (region : source.val.RegionId) :
    result.checked.val.regions (result.targetRegion region) =
      (match source.val.regions region with
      | .sheet => .sheet
      | .cut parent => .cut (result.targetRegion parent) :
        CRegion result.checked.val.regionCount) := by
  unfold targetRegion
  rw [Internal.checkedRegion_data_transport result.generated]
  unfold cutWrapCandidate cutWrapBase Internal.batchRemovalCandidate
  simp only [Fin.addCases_left]
  rw [Internal.batchRegionTable_noRegions]
  cases data : source.val.regions region with
  | sheet => rfl
  | cut parent =>
      simp only [data, CRegion.rename]
      rfl

/-- Exact generated-cut region table in checker-owned site order. -/
theorem targetCutRegion_data
    (result : CutWrapResult source wire)
    (site : Fin result.sites.sites.length) :
    result.checked.val.regions (result.targetCutRegion site) =
      .cut (result.targetRegion (result.sites.sites.get site).region) := by
  unfold targetCutRegion targetRegion
  rw [Internal.checkedRegion_data_transport result.generated]
  unfold cutWrapCandidate cutWrapRegion
  simp only [Fin.addCases_right]
  congr 1

/-- Exact constructor, payload, and retained-region table for a retained
source node. -/
theorem retainedNodeImage_data
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : CutWrapResult source wire)
    (node : source.val.NodeId)
    (retained : node ∉ result.sourceRemovedNodes) :
    result.checked.val.nodes (result.retainedNodeImage node retained) =
      (match source.val.nodes node with
      | .atom region arguments =>
          .atom (result.targetRegion region) arguments
      | .ref region definition arguments =>
          .ref (result.targetRegion region) definition arguments
      | .identity region signature arity =>
          .identity (result.targetRegion region) signature arity :
        CNode result.checked.val.regionCount definitions.length) := by
  unfold retainedNodeImage sourceRemovedNodes
  rw [Internal.checkedNode_data_transport result.generated]
  unfold cutWrapCandidate cutWrapBase Internal.batchRemovalCandidate
  simp only [Fin.addCases_left]
  let member : node ∈ Internal.retainedNodes source
      (removedSiteNodes result.sites) := by
    unfold Internal.retainedNodes
    apply List.mem_filter.mpr
    exact ⟨Data.Finite.mem_allFin node, decide_eq_true retained⟩
  let retainedIndex := Internal.retainedNodeIndex source
    (removedSiteNodes result.sites) node member
  rw [Internal.batchNodeTable_noRegions,
    Internal.sourceRetainedNode_retainedNodeIndex]
  cases data : source.val.nodes node <;>
    simp only [data, CNode.rename, Internal.checkedNodeData]
  all_goals rfl

/-- The generated atom at a site has the exact cut region and acted
relation arguments selected by the checker. -/
theorem targetNode_data
    (result : CutWrapResult source wire)
    (site : Fin result.sites.sites.length) :
    result.checked.val.nodes (result.targetNode site) =
      .atom (result.targetCutRegion site) result.targetArguments := by
  unfold targetNode targetCutRegion targetArguments
  rw [Internal.checkedNode_data_transport result.generated]
  unfold cutWrapCandidate cutWrapNode
  simp only [Fin.addCases_right]
  rfl

/-- Retained wire signatures are unchanged. -/
theorem retainedWireImage_signature
    (result : CutWrapResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ result.sourceRemovedWires) :
    (result.checked.val.wires
      (result.retainedWireImage sourceWire retained)).sig =
      (source.val.wires sourceWire).sig := by
  unfold retainedWireImage sourceRemovedWires
  rw [Internal.checkedWire_signature_transport result.generated]
  unfold cutWrapCandidate cutWrapBase
  simp only [Fin.addCases_left]
  change
    (Internal.batchWireTable result.plan.removal
      (Internal.retainedWireIndex source [wire] sourceWire _)).sig = _
  rw [Internal.batchWireTable_signature,
    Internal.sourceRetainedWire_retainedWireIndex]

/-- Retained wire scopes are transported to the exact retained-region image. -/
theorem retainedWireImage_scope
    (result : CutWrapResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ result.sourceRemovedWires) :
    (result.checked.val.wires
      (result.retainedWireImage sourceWire retained)).scope =
      result.targetRegion (source.val.wires sourceWire).scope := by
  unfold retainedWireImage sourceRemovedWires targetRegion
  rw [Internal.checkedWire_scope_transport result.generated]
  unfold cutWrapCandidate cutWrapBase
  simp only [Fin.addCases_left]
  change Internal.checkedRegion result.generated
      (Fin.castAdd result.sites.sites.length
        (Internal.batchWireTable result.plan.removal
          (Internal.retainedWireIndex source [wire] sourceWire _)).scope) = _
  simp only [Internal.batchWireTable_scope,
    Internal.sourceRetainedWire_retainedWireIndex]
  rfl

/-- The generated acted wire remains at the exact retained image of its
source scope. -/
theorem targetWire_scope
    (result : CutWrapResult source wire) :
    (result.checked.val.wires result.targetWire).scope =
      result.targetRegion (source.val.wires wire).scope := by
  rw [result.targetWire_exact,
    Internal.checkedWire_scope_transport result.generated]
  have targetExact :
      cutWrapCandidateWire result.signature result.plan =
        Fin.natAdd (cutWrapBase result.plan).wireCount (0 : Fin 1) := by
    apply Fin.ext
    rfl
  rw [targetExact]
  unfold cutWrapCandidate targetRegion
  simp only [Fin.addCases_right]
  congr 1

/-- Retained batch endpoints of one retained source-wire image. -/
def retainedTargetEndpoints
    (result : CutWrapResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ result.sourceRemovedWires) :
    List (CEndpoint result.checked.val.nodeCount) :=
  let candidate := Internal.retainedWireIndex source [wire] sourceWire (by
    unfold Internal.retainedWires
    apply List.mem_filter.mpr
    exact ⟨Data.Finite.mem_allFin sourceWire, by
      simpa [sourceRemovedWires] using decide_eq_true retained⟩)
  (Internal.batchWireTable result.plan.removal candidate).endpoints.map
    (fun endpoint => Internal.checkedEndpoint result.generated
      { node := Fin.castAdd result.sites.sites.length endpoint.node
        port := endpoint.port })

/-- Generated argument attachments of one retained source-wire image. -/
def targetArgumentEndpoints
    (result : CutWrapResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ result.sourceRemovedWires) :
    List (CEndpoint result.checked.val.nodeCount) :=
  let candidate := Internal.retainedWireIndex source [wire] sourceWire (by
    unfold Internal.retainedWires
    apply List.mem_filter.mpr
    exact ⟨Data.Finite.mem_allFin sourceWire, by
      simpa [sourceRemovedWires] using decide_eq_true retained⟩)
  (retainedWireArgumentEndpoints (source := source)
      [] (removedSiteNodes result.sites) [wire] result.sites.sites
      (fun site =>
        ({ node := cutWrapNode result.plan site, port := .head } :
          CEndpoint ((cutWrapBase result.plan).nodeCount +
            result.sites.sites.length))) candidate).map
    (Internal.checkedEndpoint result.generated)

/-- Exact ordered endpoint table for every retained target wire. -/
theorem retainedWireImage_endpoints
    (result : CutWrapResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ result.sourceRemovedWires) :
    (result.checked.val.wires
      (result.retainedWireImage sourceWire retained)).endpoints =
      result.retainedTargetEndpoints sourceWire retained ++
        result.targetArgumentEndpoints sourceWire retained := by
  unfold retainedWireImage sourceRemovedWires retainedTargetEndpoints
    targetArgumentEndpoints
  rw [Internal.checkedWire_endpoints_transport result.generated]
  unfold cutWrapCandidate cutWrapBase
  simp only [Fin.addCases_left, Internal.batchRemovalCandidate]
  rw [List.map_append, List.map_map]
  rfl

/-- Exact ordered endpoint table for the generated acted wire. -/
theorem targetWire_endpoints
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : CutWrapResult source wire) :
    (result.checked.val.wires result.targetWire).endpoints =
      (Data.Finite.allFin result.sites.sites.length).map (fun site =>
        ({ node := result.targetNode site, port := .head } :
          CEndpoint result.checked.val.nodeCount)) := by
  rw [result.targetWire_exact,
    Internal.checkedWire_endpoints_transport result.generated]
  have targetExact :
      cutWrapCandidateWire result.signature result.plan =
        Fin.natAdd (cutWrapBase result.plan).wireCount (0 : Fin 1) := by
    apply Fin.ext
    rfl
  rw [targetExact]
  unfold cutWrapCandidate targetNode
  simp only [Fin.addCases_right, List.map_map]
  rfl

/-- Target-to-source endpoint carrier induced by the exact neutral node
origin; ports are preserved verbatim. -/
def endpointOriginEquiv
    (result : CutWrapResult source wire) :
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

/-- Construction-owned neutral endpoint table for the target image of every
source wire. -/
def originEndpoints
    (result : CutWrapResult source wire)
    (sourceWire : source.val.WireId) :
    List (CEndpoint source.val.nodeCount) :=
  (result.checked.val.wires
      (result.targetWireImage sourceWire)).endpoints.map
    result.endpointOriginEquiv

/-- The acted wire's neutral endpoint table is exactly its original ordered
applied-site endpoint table. -/
theorem originEndpoints_acted
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : CutWrapResult source wire) :
    result.originEndpoints wire =
      (source.val.wires wire).endpoints := by
  unfold originEndpoints
  rw [result.targetWireImage_acted, result.targetWire_endpoints,
    List.map_map, ← result.sites.exhaustive]
  calc
    (Data.Finite.allFin result.sites.sites.length).map
        (result.endpointOriginEquiv.toFun ∘ fun site =>
          ({ node := result.targetNode site, port := .head } :
            CEndpoint result.checked.val.nodeCount)) =
      (Data.Finite.allFin result.sites.sites.length).map
        (AppliedSite.endpoint ∘ result.sites.sites.get) := by
          apply List.map_congr_left
          intro site _member
          unfold Function.comp AppliedSite.endpoint endpointOriginEquiv
          change
            ({ node := result.nodeOriginEquiv (result.targetNode site)
               port := .head } : CEndpoint source.val.nodeCount) =
              { node := (result.sites.sites.get site).node
                port := .head }
          rw [result.nodeOriginEquiv_targetNode]
    _ = result.sites.sites.map AppliedSite.endpoint := by
      rw [← List.map_map, ContentConstruction.map_get_allFin]

/-- The neutral endpoint table of a retained wire decomposes into exact
retained batch incidence followed by exact generated argument incidence. -/
theorem originEndpoints_retained_decomposition
    (result : CutWrapResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ result.sourceRemovedWires) :
    result.originEndpoints sourceWire =
      (result.retainedTargetEndpoints sourceWire retained).map
          result.endpointOriginEquiv ++
        (result.targetArgumentEndpoints sourceWire retained).map
          result.endpointOriginEquiv := by
  unfold originEndpoints
  rw [result.targetWireImage_eq_retainedWireImage sourceWire retained,
    result.retainedWireImage_endpoints, List.map_append]

/-- Bidirectional endpoint fiber between one target wire image and its exact
construction-owned neutral endpoint table. -/
structure EndpointFiberEquiv
    (result : CutWrapResult source wire)
    (sourceWire : source.val.WireId) where
  equivalence :
    Data.Finite.FiniteEquiv
      { endpoint // endpoint ∈
        (result.checked.val.wires
          (result.targetWireImage sourceWire)).endpoints }
      { endpoint // endpoint ∈ result.originEndpoints sourceWire }
  forward_exact : ∀ endpoint,
    (equivalence endpoint).1 = result.endpointOriginEquiv endpoint.1
  inverse_exact : ∀ endpoint,
    (equivalence.symm endpoint).1 =
      result.endpointOriginEquiv.symm endpoint.1

/-- Total endpoint-fiber restriction for every source-wire origin.  Both
directions are induced only by the checker-owned node-origin equivalence. -/
def endpointFiberEquiv
    (result : CutWrapResult source wire)
    (sourceWire : source.val.WireId) :
    EndpointFiberEquiv result sourceWire where
  equivalence :=
    { toFun := fun endpoint =>
        ⟨result.endpointOriginEquiv endpoint.1,
          List.mem_map.mpr ⟨endpoint.1, endpoint.2, rfl⟩⟩
      invFun := fun endpoint =>
        ⟨result.endpointOriginEquiv.symm endpoint.1, by
          rcases List.mem_map.mp endpoint.2 with
            ⟨targetEndpoint, targetMember, exact⟩
          have targetExact : targetEndpoint =
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

end CutWrapResult

/-- The generated cut witness retains the acted relation signature. -/
theorem CutWrapResult.targetWire_signature
    (result : CutWrapResult source wire) :
    (result.checked.val.wires result.targetWire).sig =
      (source.val.wires wire).sig := by
  rw [result.targetWire_exact,
    Internal.checkedWire_signature_transport result.generated]
  have targetExact :
      cutWrapCandidateWire result.signature result.plan =
        Fin.natAdd (cutWrapBase result.plan).wireCount (0 : Fin 1) := by
    apply Fin.ext
    rfl
  rw [targetExact]
  simpa only [cutWrapCandidate, Fin.addCases_right] using
    result.signature_exact.symm

/-- Replace every applied end `R(x̄)` by a fresh cut containing `W(x̄)`. -/
def cutWrap
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :
    Except ContentError (CutWrapResult source wire) := by
  match signature : (source.val.wires wire).sig with
  | .iota => exact .error .expectedRelation
  | .rel arguments =>
      match checkedSites : checkAllAppliedSites source wire with
      | none => exact .error .nonAppliedEndpoint
      | some sites =>
          match removalAccepted :
              Internal.checkBatchRemovalPlan? source []
                (removedSiteNodes sites) [wire] with
          | none => exact .error .invalidRemoval
          | some removal =>
              let plan : CutWrapPlan source wire sites := ⟨removal⟩
              let candidate := cutWrapCandidate arguments plan
              match accepted :
                  ConcreteDiagram.checkWellFormed definitions candidate with
              | .error error => exact .error (.malformedTarget error)
              | .ok checked =>
                  let generated :=
                    ConcreteDiagram.checkWellFormed_preserves_input accepted
                  exact .ok
                    (CutWrapResult.mk sites checked arguments signature plan
                      generated
                      (Internal.checkedWire generated
                        (cutWrapCandidateWire arguments plan)) rfl)

private def absorbRegions
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sites : AllAppliedSites source wire) :
    List source.val.RegionId :=
  sites.sites.map AppliedSite.region

private def absorbParent
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (site : AppliedSite source wire) :
    source.val.RegionId :=
  match source.val.regions site.region with
  | .sheet => source.val.root
  | .cut parent => parent

private def absorbSiteExact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sites : AllAppliedSites source wire)
    (site : AppliedSite source wire) : Bool :=
  match source.val.regions site.region with
  | .sheet => false
  | .cut parent =>
      decide (
        source.val.nodesAt site.region = [site.node] ∧
        source.val.childrenOf site.region = [] ∧
        source.val.wiresAt site.region = [] ∧
        parent ∉ absorbRegions sites)

private structure CutAbsorbPlan
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sites : AllAppliedSites source wire) where
  removal :
    Internal.BatchRemovalPlan source (absorbRegions sites)
      (removedSiteNodes sites) [wire]
  exactCuts :
    sites.sites.all (absorbSiteExact sites) = true
  scopeRetained :
    (source.val.wires wire).scope ∈
      Internal.retainedRegions source (absorbRegions sites)

private theorem CutAbsorbPlan.parentRetained
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    (plan : CutAbsorbPlan source wire sites)
    (position : Fin sites.sites.length) :
    absorbParent (sites.sites.get position) ∈
      Internal.retainedRegions source (absorbRegions sites) := by
  let site := sites.sites.get position
  have accepted :=
    (List.all_eq_true.mp plan.exactCuts) site (List.get_mem _ position)
  unfold absorbSiteExact at accepted
  cases regionData : source.val.regions site.region with
  | sheet =>
      simp [regionData] at accepted
  | cut parent =>
      have facts :
          source.val.nodesAt site.region = [site.node] ∧
          source.val.childrenOf site.region = [] ∧
          source.val.wiresAt site.region = [] ∧
          parent ∉ absorbRegions sites := by
        exact of_decide_eq_true (by simpa [regionData] using accepted)
      unfold absorbParent
      rw [regionData]
      unfold Internal.retainedRegions
      apply List.mem_filter.mpr
      exact ⟨Data.Finite.mem_allFin _, decide_eq_true facts.2.2.2⟩

private def cutAbsorbBase
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    (plan : CutAbsorbPlan source wire sites) :
    ConcreteDiagram definitions.length :=
  Internal.batchRemovalCandidate plan.removal

private def cutAbsorbNode
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    (plan : CutAbsorbPlan source wire sites)
    (site : Fin sites.sites.length) :
    Fin ((cutAbsorbBase plan).nodeCount + sites.sites.length) :=
  Fin.natAdd (cutAbsorbBase plan).nodeCount site

private def cutAbsorbCandidate
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    (signature : List Sig)
    (plan : CutAbsorbPlan source wire sites) :
    ConcreteDiagram definitions.length :=
  let base := cutAbsorbBase plan
  let count := sites.sites.length
  {
    regionCount := base.regionCount
    nodeCount := base.nodeCount + count
    wireCount := base.wireCount + 1
    root := base.root
    regions := base.regions
    nodes :=
      Fin.addCases base.nodes fun site =>
        .atom
          (sourceRegionAfterRemoval (source := source)
            (absorbRegions sites)
            (absorbParent (sites.sites.get site))
            (plan.parentRetained site))
          signature
    wires :=
      Fin.addCases
        (fun candidate =>
          let data := base.wires candidate
          { data with
            endpoints :=
              (data.endpoints.map fun endpoint =>
                { node := Fin.castAdd count endpoint.node
                  port := endpoint.port }) ++
              retainedWireArgumentEndpoints (source := source)
                (absorbRegions sites) (removedSiteNodes sites)
                [wire] sites.sites
                (fun site =>
                  ({ node := cutAbsorbNode plan site, port := .head } :
                    CEndpoint (base.nodeCount + count)))
                candidate })
        (fun _ =>
          { sig := .rel signature
            scope :=
              sourceRegionAfterRemoval (source := source)
                (absorbRegions sites) (source.val.wires wire).scope
                plan.scopeRetained
            endpoints :=
              (Data.Finite.allFin count).map fun site =>
                { node := cutAbsorbNode plan site, port := .head } })
  }

private def cutAbsorbCandidateWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    (signature : List Sig)
    (plan : CutAbsorbPlan source wire sites) :
    (cutAbsorbCandidate signature plan).WireId :=
  ⟨(cutAbsorbBase plan).wireCount, by
    simp [cutAbsorbCandidate]⟩

/-- Checked inverse of cut wrap, including exact normalized reconstruction. -/
structure CutAbsorbResult
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) where
  private mk ::
  sites : AllAppliedSites source wire
  checked : CheckedDiagram definitions
  private signature : List Sig
  private signature_exact : (source.val.wires wire).sig = .rel signature
  private plan : CutAbsorbPlan source wire sites
  private generated : checked.val = cutAbsorbCandidate signature plan
  targetWire : checked.val.WireId
  private targetWire_exact :
    targetWire =
      Internal.checkedWire generated
        (cutAbsorbCandidateWire signature plan)
  inverse : CutWrapResult checked targetWire
  inverseIso : ConcreteIso inverse.checked.val source.val

namespace CutAbsorbResult

private theorem absorbRegions_nodup
    (result : CutAbsorbResult source wire) :
    (absorbRegions result.sites).Nodup := by
  have nodeNodup := ContentConstruction.siteNodes_nodup result.sites
  have nodesAtExact : ∀ site ∈ result.sites.sites,
      source.val.nodesAt site.region = [site.node] := by
    intro site member
    have accepted :=
      (List.all_eq_true.mp result.plan.exactCuts) site member
    unfold absorbSiteExact at accepted
    cases regionData : source.val.regions site.region with
    | sheet => simp [regionData] at accepted
    | cut parent =>
        have facts :
            source.val.nodesAt site.region = [site.node] ∧
            source.val.childrenOf site.region = [] ∧
            source.val.wiresAt site.region = [] ∧
            parent ∉ absorbRegions result.sites := by
          exact of_decide_eq_true (by
            simpa [regionData] using accepted)
        exact facts.1
  unfold absorbRegions
  have general : ∀ values : List (AppliedSite source wire),
      values ⊆ result.sites.sites →
      (values.map AppliedSite.node).Nodup →
      (values.map AppliedSite.region).Nodup := by
    intro values subset nodesDistinct
    induction values with
    | nil => simp
    | cons head tail induction =>
        simp only [List.map_cons, List.nodup_cons] at nodesDistinct ⊢
        constructor
        · intro regionMember
          obtain ⟨candidate, candidateMember, sameRegion⟩ :=
            List.mem_map.mp regionMember
          have headMember : head ∈ result.sites.sites :=
            subset (by simp)
          have candidateFull : candidate ∈ result.sites.sites :=
            subset (by simp [candidateMember])
          have headNodes := nodesAtExact head headMember
          have candidateNodes := nodesAtExact candidate candidateFull
          rw [sameRegion] at candidateNodes
          have sameNode : head.node = candidate.node := by
            simpa using congrArg List.head? (headNodes.symm.trans candidateNodes)
          exact nodesDistinct.1
            (List.mem_map.mpr ⟨candidate, candidateMember, sameNode.symm⟩)
        · exact induction (fun value member => subset (by simp [member]))
            nodesDistinct.2
  exact general result.sites.sites (fun _ member => member) nodeNodup

/-- Reappend the removed exact cuts after the checked absorb target and
recover the complete source region carrier. -/
def reconstructionRegionEquiv
    (result : CutAbsorbResult source wire) :
    Data.Finite.FiniteEquiv
      (Fin (result.checked.val.regionCount + result.sites.sites.length))
      source.val.RegionId :=
  (ContentConstruction.finEquivOfEq (by
    rw [congrArg ConcreteDiagram.regionCount result.generated]
    simp [cutAbsorbCandidate, cutAbsorbBase,
      Internal.batchRemovalCandidate, ContentConstruction.partitionOrder,
      absorbRegions, Internal.retainedRegions, ConcreteDiagram.regionsList,
      Data.Finite.allFin_eq_finRange])).trans
    (ContentConstruction.partitionEquiv (absorbRegions result.sites)
      result.absorbRegions_nodup)

/-- Absorb checking reorders source nodes as retained nodes followed by the
exact absorbed-site nodes. -/
def nodeOriginEquiv
    (result : CutAbsorbResult source wire) :
    Data.Finite.FiniteEquiv result.checked.val.NodeId source.val.NodeId :=
  (ContentConstruction.finEquivOfEq (by
    rw [congrArg ConcreteDiagram.nodeCount result.generated]
    simp [cutAbsorbCandidate, cutAbsorbBase,
      Internal.batchRemovalCandidate, ContentConstruction.partitionOrder,
      removedSiteNodes, siteNodes, Internal.retainedNodes,
      ConcreteDiagram.nodesList, Data.Finite.allFin_eq_finRange])).trans
    (ContentConstruction.partitionEquiv (removedSiteNodes result.sites)
      (ContentConstruction.siteNodes_nodup result.sites))

/-- Absorb checking reorders wires as retained wires followed by the acted
relation wire. -/
def wireOriginEquiv
    (result : CutAbsorbResult source wire) :
    Data.Finite.FiniteEquiv result.checked.val.WireId source.val.WireId :=
  (ContentConstruction.finEquivOfEq (by
    rw [congrArg ConcreteDiagram.wireCount result.generated]
    simp [cutAbsorbCandidate, cutAbsorbBase,
      Internal.batchRemovalCandidate, ContentConstruction.partitionOrder,
      Internal.retainedWires, ConcreteDiagram.wiresList,
      Data.Finite.allFin_eq_finRange,
      ContentConstruction.length_filter_true])).trans
    (ContentConstruction.partitionEquiv [wire] (by simp))

end CutAbsorbResult

/-- Dissolve every exact single-atom cut occupied by the acted wire. -/
def cutAbsorb
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :
    Except ContentError (CutAbsorbResult source wire) := by
  match signature : (source.val.wires wire).sig with
  | .iota => exact .error .expectedRelation
  | .rel arguments =>
      match checkAllAppliedSites source wire with
      | none => exact .error .nonAppliedEndpoint
      | some sites =>
          if exactCuts :
              sites.sites.all (absorbSiteExact sites) = true then
            if scopeRetained :
                (source.val.wires wire).scope ∈
                  Internal.retainedRegions source (absorbRegions sites) then
              match removalAccepted :
                  Internal.checkBatchRemovalPlan? source (absorbRegions sites)
                    (removedSiteNodes sites) [wire] with
              | none => exact .error .invalidRemoval
              | some removal =>
                  let plan : CutAbsorbPlan source wire sites :=
                    ⟨removal, exactCuts, scopeRetained⟩
                  let candidate := cutAbsorbCandidate arguments plan
                  match accepted :
                      ConcreteDiagram.checkWellFormed definitions candidate with
                  | .error error => exact .error (.malformedTarget error)
                  | .ok checked =>
                      let generated :=
                        ConcreteDiagram.checkWellFormed_preserves_input accepted
                      let targetWire :=
                        Internal.checkedWire generated
                          (cutAbsorbCandidateWire arguments plan)
                      match inverseAccepted : cutWrap checked targetWire with
                      | .error _ => exact .error .inverseDeleteRejected
                      | .ok inverse =>
                          match
                            ConcreteIsoSearch.findConcreteIso?
                                inverse.checked.val source.val with
                          | none => exact .error .inverseIsomorphismRejected
                          | some inverseIso =>
                              exact .ok
                                (CutAbsorbResult.mk sites checked arguments
                                  signature plan generated targetWire rfl
                                  inverse inverseIso)
            else
              exact .error .nonExactCut
          else
            exact .error .nonExactCut

private structure ParallelSplitPlan
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sites : AllAppliedSites source wire) where
  removal :
    Internal.BatchRemovalPlan source [] (removedSiteNodes sites) [wire]

private def parallelSplitBase
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    (plan : ParallelSplitPlan source wire sites) :
    ConcreteDiagram definitions.length :=
  Internal.batchRemovalCandidate plan.removal

private def parallelSplitFirstNode
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    (plan : ParallelSplitPlan source wire sites)
    (site : Fin sites.sites.length) :
    Fin ((parallelSplitBase plan).nodeCount +
      (sites.sites.length + sites.sites.length)) :=
  Fin.natAdd (parallelSplitBase plan).nodeCount
    (Fin.castAdd sites.sites.length site)

private def parallelSplitSecondNode
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    (plan : ParallelSplitPlan source wire sites)
    (site : Fin sites.sites.length) :
    Fin ((parallelSplitBase plan).nodeCount +
      (sites.sites.length + sites.sites.length)) :=
  Fin.natAdd (parallelSplitBase plan).nodeCount
    (Fin.natAdd sites.sites.length site)

private def parallelSplitCandidate
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    (signature : List Sig)
    (plan : ParallelSplitPlan source wire sites) :
    ConcreteDiagram definitions.length :=
  let base := parallelSplitBase plan
  let count := sites.sites.length
  let added := count + count
  {
    regionCount := base.regionCount
    nodeCount := base.nodeCount + added
    wireCount := base.wireCount + 2
    root := base.root
    regions := base.regions
    nodes :=
      Fin.addCases base.nodes
        (Fin.addCases
          (fun site =>
            .atom
              (sourceRegionAfterRemoval (source := source) []
                (sites.sites.get site).region (by
                  unfold Internal.retainedRegions
                  apply List.mem_filter.mpr
                  exact ⟨Data.Finite.mem_allFin _, by simp⟩))
              signature)
          (fun site =>
            .atom
              (sourceRegionAfterRemoval (source := source) []
                (sites.sites.get site).region (by
                  unfold Internal.retainedRegions
                  apply List.mem_filter.mpr
                  exact ⟨Data.Finite.mem_allFin _, by simp⟩))
              signature))
    wires :=
      Fin.addCases
        (fun candidate =>
          let data := base.wires candidate
          { data with
            endpoints :=
              (data.endpoints.map fun endpoint =>
                { node := Fin.castAdd added endpoint.node
                  port := endpoint.port }) ++
              retainedWireDoubleArgumentEndpoints (source := source)
                [] (removedSiteNodes sites) [wire] sites.sites
                (parallelSplitFirstNode plan)
                (parallelSplitSecondNode plan) candidate })
        (fun branch =>
          { sig := .rel signature
            scope :=
              sourceRegionAfterRemoval (source := source) []
                (source.val.wires wire).scope (by
                  unfold Internal.retainedRegions
                  apply List.mem_filter.mpr
                  exact ⟨Data.Finite.mem_allFin _, by simp⟩)
            endpoints :=
              (Data.Finite.allFin count).map fun site =>
                { node :=
                    if branch.val = 0 then
                      parallelSplitFirstNode plan site
                    else
                      parallelSplitSecondNode plan site
                  port := .head } })
  }

private def parallelSplitCandidateWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    (signature : List Sig)
    (plan : ParallelSplitPlan source wire sites)
    (branch : Fin 2) :
    (parallelSplitCandidate signature plan).WireId :=
  ⟨(parallelSplitBase plan).wireCount + branch.val, by
    have branchBound := branch.isLt
    simp only [parallelSplitCandidate]
    omega⟩

/-- Checked simultaneous replacement of one wire by two parallel wires. -/
structure ParallelSplitResult
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) where
  private mk ::
  sites : AllAppliedSites source wire
  checked : CheckedDiagram definitions
  private signature : List Sig
  private signature_exact : (source.val.wires wire).sig = .rel signature
  private plan : ParallelSplitPlan source wire sites
  private generated : checked.val = parallelSplitCandidate signature plan
  firstWire : checked.val.WireId
  secondWire : checked.val.WireId
  private firstWire_exact :
    firstWire =
      Internal.checkedWire generated
        (parallelSplitCandidateWire signature plan (0 : Fin 2))
  private secondWire_exact :
    secondWire =
      Internal.checkedWire generated
        (parallelSplitCandidateWire signature plan (1 : Fin 2))

namespace ParallelSplitResult

def targetArguments
    (result : ParallelSplitResult source wire) : List Sig :=
  result.signature

def targetRegion
    (result : ParallelSplitResult source wire)
    (region : source.val.RegionId) : result.checked.val.RegionId :=
  Internal.checkedRegion result.generated
    (Internal.noRegionRemovalEquiv source region)

def sourceRemovedNodes
    (result : ParallelSplitResult source wire) : List source.val.NodeId :=
  removedSiteNodes result.sites

def sourceRemovedWires
    (_result : ParallelSplitResult source wire) : List source.val.WireId :=
  [wire]

def retainedNodeCount
    (result : ParallelSplitResult source wire) : Nat :=
  (Internal.retainedNodes source result.sourceRemovedNodes).length

def nodeAllocationCount
    (result : ParallelSplitResult source wire) : Nat :=
  result.retainedNodeCount +
    (result.sites.sites.length + result.sites.sites.length)

def retainedWireCount
    (result : ParallelSplitResult source wire) : Nat :=
  (Internal.retainedWires source result.sourceRemovedWires).length

def wireAllocationCount
    (result : ParallelSplitResult source wire) : Nat :=
  result.retainedWireCount + 2

def retainedNodeImage
    (result : ParallelSplitResult source wire)
    (node : source.val.NodeId)
    (retained : node ∉ result.sourceRemovedNodes) :
    result.checked.val.NodeId :=
  Internal.checkedNode result.generated
    (Fin.castAdd (result.sites.sites.length + result.sites.sites.length)
      (Internal.retainedNodeIndex source result.sourceRemovedNodes node (by
        unfold Internal.retainedNodes
        exact List.mem_filter.mpr
          ⟨Data.Finite.mem_allFin node, decide_eq_true retained⟩)))

def firstNode
    (result : ParallelSplitResult source wire)
    (site : Fin result.sites.sites.length) : result.checked.val.NodeId :=
  Internal.checkedNode result.generated
    (parallelSplitFirstNode result.plan site)

def secondNode
    (result : ParallelSplitResult source wire)
    (site : Fin result.sites.sites.length) : result.checked.val.NodeId :=
  Internal.checkedNode result.generated
    (parallelSplitSecondNode result.plan site)

def retainedWireImage
    (result : ParallelSplitResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ result.sourceRemovedWires) :
    result.checked.val.WireId :=
  Internal.checkedWire result.generated
    (Fin.castAdd 2
      (Internal.retainedWireIndex source result.sourceRemovedWires sourceWire
        (by
          unfold Internal.retainedWires
          exact List.mem_filter.mpr
            ⟨Data.Finite.mem_allFin sourceWire, decide_eq_true retained⟩)))

/-- Parallel splitting preserves the region carrier. -/
def regionOriginEquiv
    (result : ParallelSplitResult source wire) :
    Data.Finite.FiniteEquiv result.checked.val.RegionId source.val.RegionId :=
  ContentConstruction.finEquivOfEq (by
    rw [congrArg ConcreteDiagram.regionCount result.generated]
    simp [parallelSplitCandidate, parallelSplitBase,
      Internal.batchRemovalCandidate, Internal.retainedRegions,
      ConcreteDiagram.regionsList, Data.Finite.allFin_eq_finRange,
      ContentConstruction.length_filter_true])

@[simp] theorem regionOriginEquiv_targetRegion
    (result : ParallelSplitResult source wire)
    (region : source.val.RegionId) :
    result.regionOriginEquiv (result.targetRegion region) = region := by
  apply Fin.ext
  unfold regionOriginEquiv targetRegion ContentConstruction.finEquivOfEq
    Internal.checkedRegion
  change (Internal.noRegionRemovalEquiv source region).val = region.val
  have inverseExact :=
    Internal.sourceRetainedRegion_noRegionRemovalEquiv source region
  simpa [Internal.sourceRetainedRegion, Internal.retainedRegions_nil,
    ConcreteDiagram.regionsList, Data.Finite.allFin_eq_finRange] using
      congrArg Fin.val inverseExact

/-- Split checking identifies its complete checked node carrier with retained
nodes followed by the two ordered generated branches. -/
def constructionNodeEquiv
    (result : ParallelSplitResult source wire) :
    Data.Finite.FiniteEquiv result.checked.val.NodeId
      (Fin result.nodeAllocationCount) :=
  ContentConstruction.finEquivOfEq (by
    rw [congrArg ConcreteDiagram.nodeCount result.generated]
    rfl)

@[simp] theorem constructionNodeEquiv_retainedNodeImage
    (result : ParallelSplitResult source wire)
    (node : source.val.NodeId)
    (retained : node ∉ result.sourceRemovedNodes) :
    result.constructionNodeEquiv (result.retainedNodeImage node retained) =
      Fin.castAdd (result.sites.sites.length + result.sites.sites.length)
        (Internal.retainedNodeIndex source result.sourceRemovedNodes node (by
          unfold Internal.retainedNodes
          exact List.mem_filter.mpr
            ⟨Data.Finite.mem_allFin node, decide_eq_true retained⟩)) := by
  apply Fin.ext
  rfl

@[simp] theorem constructionNodeEquiv_firstNode
    (result : ParallelSplitResult source wire)
    (site : Fin result.sites.sites.length) :
    result.constructionNodeEquiv (result.firstNode site) =
      Fin.natAdd result.retainedNodeCount
        (Fin.castAdd result.sites.sites.length site) := by
  apply Fin.ext
  rfl

@[simp] theorem constructionNodeEquiv_secondNode
    (result : ParallelSplitResult source wire)
    (site : Fin result.sites.sites.length) :
    result.constructionNodeEquiv (result.secondNode site) =
      Fin.natAdd result.retainedNodeCount
        (Fin.natAdd result.sites.sites.length site) := by
  apply Fin.ext
  rfl

/-- Split checking identifies its complete checked wire carrier with retained
wires followed by the two ordered generated branches. -/
def constructionWireEquiv
    (result : ParallelSplitResult source wire) :
    Data.Finite.FiniteEquiv result.checked.val.WireId
      (Fin result.wireAllocationCount) :=
  ContentConstruction.finEquivOfEq (by
    rw [congrArg ConcreteDiagram.wireCount result.generated]
    rfl)

@[simp] theorem constructionWireEquiv_retainedWireImage
    (result : ParallelSplitResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ result.sourceRemovedWires) :
    result.constructionWireEquiv
        (result.retainedWireImage sourceWire retained) =
      Fin.castAdd 2
        (Internal.retainedWireIndex source result.sourceRemovedWires
          sourceWire (by
            unfold Internal.retainedWires
            exact List.mem_filter.mpr
              ⟨Data.Finite.mem_allFin sourceWire,
                decide_eq_true retained⟩)) := by
  apply Fin.ext
  rfl

@[simp] theorem constructionWireEquiv_firstWire
    (result : ParallelSplitResult source wire) :
    result.constructionWireEquiv result.firstWire =
      Fin.natAdd result.retainedWireCount (0 : Fin 2) := by
  rw [result.firstWire_exact]
  apply Fin.ext
  rfl

@[simp] theorem constructionWireEquiv_secondWire
    (result : ParallelSplitResult source wire) :
    result.constructionWireEquiv result.secondWire =
      Fin.natAdd result.retainedWireCount (1 : Fin 2) := by
  rw [result.secondWire_exact]
  apply Fin.ext
  rfl

/-- Retained nodes followed by either generated branch reconstruct the
source node carrier. -/
def reconstructionNodeEquiv
    (result : ParallelSplitResult source wire) :
    Data.Finite.FiniteEquiv
      (Fin ((parallelSplitBase result.plan).nodeCount +
        result.sites.sites.length))
      source.val.NodeId :=
  (ContentConstruction.finEquivOfEq (by
    simp [parallelSplitBase, Internal.batchRemovalCandidate,
      ContentConstruction.partitionOrder, removedSiteNodes, siteNodes,
      Internal.retainedNodes, ConcreteDiagram.nodesList,
      Data.Finite.allFin_eq_finRange])).trans
    (ContentConstruction.partitionEquiv (removedSiteNodes result.sites)
      (ContentConstruction.siteNodes_nodup result.sites))

/-- Retained wires followed by either generated branch reconstruct the
source wire carrier. -/
def reconstructionWireEquiv
    (result : ParallelSplitResult source wire) :
    Data.Finite.FiniteEquiv
      (Fin ((parallelSplitBase result.plan).wireCount + 1))
      source.val.WireId :=
  (ContentConstruction.finEquivOfEq (by
    simp [parallelSplitBase, Internal.batchRemovalCandidate,
      ContentConstruction.partitionOrder, Internal.retainedWires,
      ConcreteDiagram.wiresList, Data.Finite.allFin_eq_finRange])).trans
      (ContentConstruction.partitionEquiv [wire] (by simp))

theorem targetRoot_exact
    (result : ParallelSplitResult source wire) :
    result.checked.val.root = result.targetRegion source.val.root := by
  unfold targetRegion
  rw [Internal.checkedRoot_transport result.generated]
  rfl

theorem targetRegion_data
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ParallelSplitResult source wire)
    (region : source.val.RegionId) :
    result.checked.val.regions (result.targetRegion region) =
      (match source.val.regions region with
      | .sheet => .sheet
      | .cut parent => .cut (result.targetRegion parent) :
        CRegion result.checked.val.regionCount) := by
  unfold targetRegion
  rw [Internal.checkedRegion_data_transport result.generated]
  simp only [parallelSplitCandidate, parallelSplitBase,
    Internal.batchRemovalCandidate]
  rw [Internal.batchRegionTable_noRegions]
  cases source.val.regions region <;> rfl

theorem retainedNodeImage_data
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ParallelSplitResult source wire)
    (node : source.val.NodeId)
    (retained : node ∉ result.sourceRemovedNodes) :
    result.checked.val.nodes (result.retainedNodeImage node retained) =
      (match source.val.nodes node with
      | .atom region arguments =>
          .atom (result.targetRegion region) arguments
      | .ref region definition arguments =>
          .ref (result.targetRegion region) definition arguments
      | .identity region signature arity =>
          .identity (result.targetRegion region) signature arity :
        CNode result.checked.val.regionCount definitions.length) := by
  unfold retainedNodeImage sourceRemovedNodes
  rw [Internal.checkedNode_data_transport result.generated]
  unfold parallelSplitCandidate parallelSplitBase
  simp only [Fin.addCases_left, Internal.batchRemovalCandidate]
  rw [Internal.batchNodeTable_noRegions,
    Internal.sourceRetainedNode_retainedNodeIndex]
  cases source.val.nodes node <;> rfl

theorem firstNode_data
    (result : ParallelSplitResult source wire)
    (site : Fin result.sites.sites.length) :
    result.checked.val.nodes (result.firstNode site) =
      .atom (result.targetRegion (result.sites.sites.get site).region)
        result.targetArguments := by
  unfold firstNode targetRegion targetArguments
  rw [Internal.checkedNode_data_transport result.generated]
  unfold parallelSplitCandidate parallelSplitFirstNode
  simp only [Fin.addCases_right, Fin.addCases_left]
  rfl

theorem secondNode_data
    (result : ParallelSplitResult source wire)
    (site : Fin result.sites.sites.length) :
    result.checked.val.nodes (result.secondNode site) =
      .atom (result.targetRegion (result.sites.sites.get site).region)
        result.targetArguments := by
  unfold secondNode targetRegion targetArguments
  rw [Internal.checkedNode_data_transport result.generated]
  unfold parallelSplitCandidate parallelSplitSecondNode
  simp only [Fin.addCases_right]
  rfl

theorem retainedWireImage_signature
    (result : ParallelSplitResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ result.sourceRemovedWires) :
    (result.checked.val.wires
      (result.retainedWireImage sourceWire retained)).sig =
      (source.val.wires sourceWire).sig := by
  unfold retainedWireImage sourceRemovedWires
  rw [Internal.checkedWire_signature_transport result.generated]
  unfold parallelSplitCandidate parallelSplitBase
  simp only [Fin.addCases_left, Internal.batchRemovalCandidate]
  rw [Internal.batchWireTable_signature,
    Internal.sourceRetainedWire_retainedWireIndex]

theorem retainedWireImage_scope
    (result : ParallelSplitResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ result.sourceRemovedWires) :
    (result.checked.val.wires
      (result.retainedWireImage sourceWire retained)).scope =
      result.targetRegion (source.val.wires sourceWire).scope := by
  unfold retainedWireImage sourceRemovedWires targetRegion
  rw [Internal.checkedWire_scope_transport result.generated]
  unfold parallelSplitCandidate parallelSplitBase
  simp only [Fin.addCases_left, Internal.batchRemovalCandidate,
    Internal.batchWireTable_scope,
    Internal.sourceRetainedWire_retainedWireIndex]
  rfl

theorem firstWire_scope
    (result : ParallelSplitResult source wire) :
    (result.checked.val.wires result.firstWire).scope =
      result.targetRegion (source.val.wires wire).scope := by
  rw [result.firstWire_exact,
    Internal.checkedWire_scope_transport result.generated]
  have exact : parallelSplitCandidateWire result.signature result.plan
      (0 : Fin 2) = Fin.natAdd (parallelSplitBase result.plan).wireCount
        (0 : Fin 2) := by apply Fin.ext; rfl
  rw [exact]
  unfold parallelSplitCandidate targetRegion
  simp only [Fin.addCases_right]
  rfl

theorem secondWire_scope
    (result : ParallelSplitResult source wire) :
    (result.checked.val.wires result.secondWire).scope =
      result.targetRegion (source.val.wires wire).scope := by
  rw [result.secondWire_exact,
    Internal.checkedWire_scope_transport result.generated]
  have exact : parallelSplitCandidateWire result.signature result.plan
      (1 : Fin 2) = Fin.natAdd (parallelSplitBase result.plan).wireCount
        (1 : Fin 2) := by apply Fin.ext; rfl
  rw [exact]
  unfold parallelSplitCandidate targetRegion
  simp only [Fin.addCases_right]
  rfl

def retainedTargetEndpoints
    (result : ParallelSplitResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ result.sourceRemovedWires) :
    List (CEndpoint result.checked.val.nodeCount) :=
  let candidate := Internal.retainedWireIndex source [wire] sourceWire (by
    unfold Internal.retainedWires
    exact List.mem_filter.mpr ⟨Data.Finite.mem_allFin sourceWire, by
      simpa [sourceRemovedWires] using decide_eq_true retained⟩)
  (Internal.batchWireTable result.plan.removal candidate).endpoints.map
    (fun endpoint => Internal.checkedEndpoint result.generated
      { node := Fin.castAdd
          (result.sites.sites.length + result.sites.sites.length)
          endpoint.node
        port := endpoint.port })

def targetArgumentEndpoints
    (result : ParallelSplitResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ result.sourceRemovedWires) :
    List (CEndpoint result.checked.val.nodeCount) :=
  let candidate := Internal.retainedWireIndex source [wire] sourceWire (by
    unfold Internal.retainedWires
    exact List.mem_filter.mpr ⟨Data.Finite.mem_allFin sourceWire, by
      simpa [sourceRemovedWires] using decide_eq_true retained⟩)
  (retainedWireDoubleArgumentEndpoints (source := source)
      [] (removedSiteNodes result.sites) [wire] result.sites.sites
      (parallelSplitFirstNode result.plan)
      (parallelSplitSecondNode result.plan) candidate).map
    (Internal.checkedEndpoint result.generated)

theorem retainedWireImage_endpoints
    (result : ParallelSplitResult source wire)
    (sourceWire : source.val.WireId)
    (retained : sourceWire ∉ result.sourceRemovedWires) :
    (result.checked.val.wires
      (result.retainedWireImage sourceWire retained)).endpoints =
      result.retainedTargetEndpoints sourceWire retained ++
        result.targetArgumentEndpoints sourceWire retained := by
  unfold retainedWireImage sourceRemovedWires retainedTargetEndpoints
    targetArgumentEndpoints
  rw [Internal.checkedWire_endpoints_transport result.generated]
  unfold parallelSplitCandidate parallelSplitBase
  simp only [Fin.addCases_left, Internal.batchRemovalCandidate]
  rw [List.map_append, List.map_map]
  rfl

theorem firstWire_endpoints
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ParallelSplitResult source wire) :
    (result.checked.val.wires result.firstWire).endpoints =
      (Data.Finite.allFin result.sites.sites.length).map (fun site =>
        ({ node := result.firstNode site, port := .head } :
          CEndpoint result.checked.val.nodeCount)) := by
  rw [result.firstWire_exact,
    Internal.checkedWire_endpoints_transport result.generated]
  have exact : parallelSplitCandidateWire result.signature result.plan
      (0 : Fin 2) = Fin.natAdd (parallelSplitBase result.plan).wireCount
        (0 : Fin 2) := by apply Fin.ext; rfl
  rw [exact]
  unfold parallelSplitCandidate firstNode
  simp only [Fin.addCases_right, List.map_map]
  rfl

theorem secondWire_endpoints
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : ParallelSplitResult source wire) :
    (result.checked.val.wires result.secondWire).endpoints =
      (Data.Finite.allFin result.sites.sites.length).map (fun site =>
        ({ node := result.secondNode site, port := .head } :
          CEndpoint result.checked.val.nodeCount)) := by
  rw [result.secondWire_exact,
    Internal.checkedWire_endpoints_transport result.generated]
  have exact : parallelSplitCandidateWire result.signature result.plan
      (1 : Fin 2) = Fin.natAdd (parallelSplitBase result.plan).wireCount
        (1 : Fin 2) := by apply Fin.ext; rfl
  rw [exact]
  unfold parallelSplitCandidate secondNode
  simp only [Fin.addCases_right, List.map_map]
  rfl

end ParallelSplitResult

/-- The first generated parallel witness retains the acted signature. -/
theorem ParallelSplitResult.firstWire_signature
    (result : ParallelSplitResult source wire) :
    (result.checked.val.wires result.firstWire).sig =
      (source.val.wires wire).sig := by
  rw [result.firstWire_exact,
    Internal.checkedWire_signature_transport result.generated]
  have firstExact :
      parallelSplitCandidateWire result.signature result.plan (0 : Fin 2) =
        Fin.natAdd (parallelSplitBase result.plan).wireCount
          (0 : Fin 2) := by
    apply Fin.ext
    rfl
  rw [firstExact]
  simpa only [parallelSplitCandidate, Fin.addCases_right] using
    result.signature_exact.symm

/-- The second generated parallel witness retains the acted signature. -/
theorem ParallelSplitResult.secondWire_signature
    (result : ParallelSplitResult source wire) :
    (result.checked.val.wires result.secondWire).sig =
      (source.val.wires wire).sig := by
  rw [result.secondWire_exact,
    Internal.checkedWire_signature_transport result.generated]
  have secondExact :
      parallelSplitCandidateWire result.signature result.plan (1 : Fin 2) =
        Fin.natAdd (parallelSplitBase result.plan).wireCount
          (1 : Fin 2) := by
    apply Fin.ext
    rfl
  rw [secondExact]
  simpa only [parallelSplitCandidate, Fin.addCases_right] using
    result.signature_exact.symm

/-- Both generated parallel witnesses occupy the same acted scope. -/
theorem ParallelSplitResult.wireScopes_eq
    (result : ParallelSplitResult source wire) :
    (result.checked.val.wires result.firstWire).scope =
      (result.checked.val.wires result.secondWire).scope := by
  rw [result.firstWire_exact, result.secondWire_exact,
    Internal.checkedWire_scope_transport,
    Internal.checkedWire_scope_transport]
  have firstExact :
      parallelSplitCandidateWire result.signature result.plan (0 : Fin 2) =
        Fin.natAdd (parallelSplitBase result.plan).wireCount
          (0 : Fin 2) := by
    apply Fin.ext
    rfl
  have secondExact :
      parallelSplitCandidateWire result.signature result.plan (1 : Fin 2) =
        Fin.natAdd (parallelSplitBase result.plan).wireCount
          (1 : Fin 2) := by
    apply Fin.ext
    rfl
  rw [firstExact, secondExact]
  simp only [parallelSplitCandidate, Fin.addCases_right]

/-- Replace every `R(x̄)` by co-located `W₁(x̄)` and `W₂(x̄)`. -/
def parallelSplit
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :
    Except ContentError (ParallelSplitResult source wire) := by
  match signature : (source.val.wires wire).sig with
  | .iota => exact .error .expectedRelation
  | .rel arguments =>
      match checkAllAppliedSites source wire with
      | none => exact .error .nonAppliedEndpoint
      | some sites =>
          match removalAccepted :
              Internal.checkBatchRemovalPlan? source []
                (removedSiteNodes sites) [wire] with
          | none => exact .error .invalidRemoval
          | some removal =>
              let plan : ParallelSplitPlan source wire sites := ⟨removal⟩
              let candidate := parallelSplitCandidate arguments plan
              match accepted :
                  ConcreteDiagram.checkWellFormed definitions candidate with
              | .error error => exact .error (.malformedTarget error)
              | .ok checked =>
                  let generated :=
                    ConcreteDiagram.checkWellFormed_preserves_input accepted
                  exact .ok
                    (ParallelSplitResult.mk sites checked arguments signature
                      plan generated
                      (Internal.checkedWire generated
                        (parallelSplitCandidateWire arguments plan
                          (0 : Fin 2)))
                      (Internal.checkedWire generated
                        (parallelSplitCandidateWire arguments plan
                          (1 : Fin 2)))
                      rfl rfl)

private structure ParallelPair
    (source : CheckedDiagram definitions)
    (left right : source.val.WireId) where
  leftSite : AppliedSite source left
  rightSite : AppliedSite source right

private def sameParallelSite
    {source : CheckedDiagram definitions}
    {left right : source.val.WireId}
    (leftSite : AppliedSite source left)
    (rightSite : AppliedSite source right) : Bool :=
  leftSite.region == rightSite.region &&
    leftSite.arguments == rightSite.arguments

private def pullParallelSite?
    {source : CheckedDiagram definitions}
    {left right : source.val.WireId}
    (target : AppliedSite source right) :
    List (AppliedSite source left) →
      Option
        (AppliedSite source left × List (AppliedSite source left))
  | [] => none
  | candidate :: tail =>
      if sameParallelSite candidate target then
        some (candidate, tail)
      else
        match pullParallelSite? target tail with
        | none => none
        | some (partner, rest) => some (partner, candidate :: rest)

private def pairParallelSitesAux?
    {source : CheckedDiagram definitions}
    {left right : source.val.WireId} :
    List (AppliedSite source left) →
      List (AppliedSite source right) →
        Option
          (List (ParallelPair source left right) ×
            List (AppliedSite source left))
  | leftSites, [] => some ([], leftSites)
  | leftSites, rightSite :: rightSites => do
      let (leftSite, remaining) ← pullParallelSite? rightSite leftSites
      let (pairs, leftover) ← pairParallelSitesAux? remaining rightSites
      pure (⟨leftSite, rightSite⟩ :: pairs, leftover)

private def pairParallelSites?
    {source : CheckedDiagram definitions}
    {left right : source.val.WireId}
    (leftSites : List (AppliedSite source left))
    (rightSites : List (AppliedSite source right)) :
    Option (List (ParallelPair source left right)) := do
  let (pairs, leftover) ← pairParallelSitesAux? leftSites rightSites
  if leftover = [] then
    pure pairs
  else
    none

private theorem pairParallelSitesAux_length
    {source : CheckedDiagram definitions}
    {left right : source.val.WireId} :
    ∀ (leftSites : List (AppliedSite source left))
      (rightSites : List (AppliedSite source right)) pairs leftover,
      pairParallelSitesAux? leftSites rightSites = some (pairs, leftover) →
        pairs.length = rightSites.length := by
  intro leftSites rightSites
  induction rightSites generalizing leftSites with
  | nil =>
      intro pairs leftover accepted
      simp [pairParallelSitesAux?] at accepted
      exact congrArg List.length accepted.1
  | cons rightSite rightSites induction =>
      intro pairs leftover accepted
      simp only [pairParallelSitesAux?] at accepted
      cases pulled : pullParallelSite? rightSite leftSites with
      | none => simp [pulled] at accepted
      | some result =>
          obtain ⟨leftSite, remaining⟩ := result
          cases paired : pairParallelSitesAux? remaining rightSites with
          | none => simp [pulled, paired] at accepted
          | some result =>
              obtain ⟨tailPairs, tailLeftover⟩ := result
              simp [pulled, paired] at accepted
              rcases accepted with ⟨rfl, rfl⟩
              have tailLength := induction remaining tailPairs tailLeftover paired
              simp [tailLength]

private theorem pairParallelSites_length
    {source : CheckedDiagram definitions}
    {left right : source.val.WireId}
    (leftSites : List (AppliedSite source left))
    (rightSites : List (AppliedSite source right))
    (pairs : List (ParallelPair source left right))
    (accepted : pairParallelSites? leftSites rightSites = some pairs) :
    pairs.length = rightSites.length := by
  unfold pairParallelSites? at accepted
  cases paired : pairParallelSitesAux? leftSites rightSites with
  | none => simp [paired] at accepted
  | some result =>
      obtain ⟨candidate, leftover⟩ := result
      by_cases empty : leftover = []
      · simp [paired, empty] at accepted
        subst candidate
        exact pairParallelSitesAux_length leftSites rightSites pairs leftover
          paired
      · simp [paired, empty] at accepted

private def parallelPairNodes
    {source : CheckedDiagram definitions}
    {left right : source.val.WireId}
    (pairs : List (ParallelPair source left right)) :
    List source.val.NodeId :=
  pairs.flatMap fun pair => [pair.leftSite.node, pair.rightSite.node]

private structure ParallelFusePlan
    (source : CheckedDiagram definitions)
    (left right : source.val.WireId)
    (pairs : List (ParallelPair source left right)) where
  removal :
    Internal.BatchRemovalPlan source []
      (parallelPairNodes pairs) [left, right]

private def parallelFuseBase
    {source : CheckedDiagram definitions}
    {left right : source.val.WireId}
    {pairs : List (ParallelPair source left right)}
    (plan : ParallelFusePlan source left right pairs) :
    ConcreteDiagram definitions.length :=
  Internal.batchRemovalCandidate plan.removal

private def parallelFuseNode
    {source : CheckedDiagram definitions}
    {left right : source.val.WireId}
    {pairs : List (ParallelPair source left right)}
    (plan : ParallelFusePlan source left right pairs)
    (pair : Fin pairs.length) :
    Fin ((parallelFuseBase plan).nodeCount + pairs.length) :=
  Fin.natAdd (parallelFuseBase plan).nodeCount pair

private def parallelPairArgumentEndpoints
    {source : CheckedDiagram definitions}
    {left right : source.val.WireId}
    (pairs : List (ParallelPair source left right))
    (removedNodes : List source.val.NodeId)
    (candidate :
      Fin (Internal.retainedWires source [left, right]).length) :
    List (CEndpoint
      ((Internal.retainedNodes source removedNodes).length + pairs.length)) :=
  let sourceWire :=
    Internal.sourceRetainedWire source [left, right] candidate
  (Data.Finite.allFin pairs.length).flatMap fun pair =>
    (List.range (pairs.get pair).leftSite.arguments.length).filterMap
      fun position =>
        match (pairs.get pair).leftSite.arguments[position]? with
        | some argument =>
            if argument = sourceWire then
              some
                { node :=
                    Fin.natAdd
                      (Internal.retainedNodes source removedNodes).length pair
                  port := .arg position }
            else
              none
        | none => none

private def parallelFuseCandidate
    {source : CheckedDiagram definitions}
    {left right : source.val.WireId}
    {pairs : List (ParallelPair source left right)}
    (signature : List Sig)
    (plan : ParallelFusePlan source left right pairs) :
    ConcreteDiagram definitions.length :=
  let base := parallelFuseBase plan
  let count := pairs.length
  {
    regionCount := base.regionCount
    nodeCount := base.nodeCount + count
    wireCount := base.wireCount + 1
    root := base.root
    regions := base.regions
    nodes :=
      Fin.addCases base.nodes fun pair =>
        .atom
          (sourceRegionAfterRemoval (source := source) []
            (pairs.get pair).leftSite.region (by
              unfold Internal.retainedRegions
              apply List.mem_filter.mpr
              exact ⟨Data.Finite.mem_allFin _, by simp⟩))
          signature
    wires :=
      Fin.addCases
        (fun candidate =>
          let data := base.wires candidate
          { data with
            endpoints :=
              (data.endpoints.map fun endpoint =>
                { node := Fin.castAdd count endpoint.node
                  port := endpoint.port }) ++
              parallelPairArgumentEndpoints pairs (parallelPairNodes pairs)
                candidate })
        (fun _ =>
          { sig := .rel signature
            scope :=
              sourceRegionAfterRemoval (source := source) []
                (source.val.wires left).scope (by
                  unfold Internal.retainedRegions
                  apply List.mem_filter.mpr
                  exact ⟨Data.Finite.mem_allFin _, by simp⟩)
            endpoints :=
              (Data.Finite.allFin count).map fun pair =>
                { node := parallelFuseNode plan pair, port := .head } })
  }

private def parallelFuseCandidateWire
    {source : CheckedDiagram definitions}
    {left right : source.val.WireId}
    {pairs : List (ParallelPair source left right)}
    (signature : List Sig)
    (plan : ParallelFusePlan source left right pairs) :
    (parallelFuseCandidate signature plan).WireId :=
  ⟨(parallelFuseBase plan).wireCount, by
    simp [parallelFuseCandidate]⟩

/-- Checked pairwise parallel fusion with exact split reconstruction. -/
structure ParallelFuseResult
    (source : CheckedDiagram definitions)
    (left right : source.val.WireId) where
  private mk ::
  leftSites : AllAppliedSites source left
  rightSites : AllAppliedSites source right
  private pairs : List (ParallelPair source left right)
  private pairs_length : pairs.length = rightSites.sites.length
  checked : CheckedDiagram definitions
  private signature : List Sig
  private leftSignature : (source.val.wires left).sig = .rel signature
  private rightSignature : (source.val.wires right).sig = .rel signature
  private plan : ParallelFusePlan source left right pairs
  private generated : checked.val = parallelFuseCandidate signature plan
  targetWire : checked.val.WireId
  private targetWire_exact :
    targetWire =
      Internal.checkedWire generated
        (parallelFuseCandidateWire signature plan)
  inverse : ParallelSplitResult checked targetWire
  inverseIso : ConcreteIso inverse.checked.val source.val

namespace ParallelFuseResult

/-- The inverse split sees exactly one fused site for every paired right-hand
site retained by the fuse receipt. -/
theorem inverseSites_length
    (result : ParallelFuseResult source left right) :
    result.inverse.sites.sites.length = result.rightSites.sites.length := by
  rw [result.inverse.sites.length]
  rw [result.targetWire_exact,
    Internal.checkedWire_endpoints_transport result.generated]
  have targetExact :
      parallelFuseCandidateWire result.signature result.plan =
        Fin.natAdd (parallelFuseBase result.plan).wireCount (0 : Fin 1) := by
    apply Fin.ext
    rfl
  rw [targetExact]
  simp only [parallelFuseCandidate, Fin.addCases_right, List.length_map,
    Data.Finite.allFin_eq_finRange, List.length_finRange]
  exact result.pairs_length

/-- Parallel fusion preserves the region carrier. -/
def regionOriginEquiv
    (result : ParallelFuseResult source left right) :
    Data.Finite.FiniteEquiv result.checked.val.RegionId source.val.RegionId :=
  ContentConstruction.finEquivOfEq (by
    rw [congrArg ConcreteDiagram.regionCount result.generated]
    simp [parallelFuseCandidate, parallelFuseBase,
      Internal.batchRemovalCandidate, Internal.retainedRegions,
      ConcreteDiagram.regionsList, Data.Finite.allFin_eq_finRange,
      ContentConstruction.length_filter_true])

/-- The checked fuse target is the retained-node carrier followed by one
node for every exact right-hand site. -/
def constructionNodeEquiv
    (result : ParallelFuseResult source left right) :
    Data.Finite.FiniteEquiv result.checked.val.NodeId
      (Fin ((parallelFuseBase result.plan).nodeCount +
        result.rightSites.sites.length)) :=
  ContentConstruction.finEquivOfEq (by
    rw [congrArg ConcreteDiagram.nodeCount result.generated]
    change (parallelFuseBase result.plan).nodeCount + result.pairs.length = _
    rw [result.pairs_length])

/-- The checked fuse target is the retained-wire carrier followed by its
single fused witness. -/
def constructionWireEquiv
    (result : ParallelFuseResult source left right) :
    Data.Finite.FiniteEquiv result.checked.val.WireId
      (Fin ((parallelFuseBase result.plan).wireCount + 1)) :=
  ContentConstruction.finEquivOfEq (by
    rw [congrArg ConcreteDiagram.wireCount result.generated]
    rfl)

end ParallelFuseResult

/-- Fuse two co-scoped, equal-signature, pairwise co-located applied wires. -/
def parallelFuse
    (source : CheckedDiagram definitions)
    (left right : source.val.WireId) :
    Except ContentError (ParallelFuseResult source left right) := by
  if same : left = right then
    exact .error .sameWire
  else
    match leftSignature : (source.val.wires left).sig with
    | .iota => exact .error .expectedRelation
    | .rel arguments =>
        match rightSignature : (source.val.wires right).sig with
        | .iota => exact .error .signatureMismatch
        | .rel rightArguments =>
            if signatures : rightArguments = arguments then
              if scopes :
                  (source.val.wires left).scope =
                    (source.val.wires right).scope then
                match checkAllAppliedSites source left,
                    checkAllAppliedSites source right with
                | some leftSites, some rightSites =>
                    match paired :
                        pairParallelSites? leftSites.sites
                          rightSites.sites with
                    | none => exact .error .parallelMismatch
                    | some pairs =>
                        match removalAccepted :
                            Internal.checkBatchRemovalPlan? source []
                              (parallelPairNodes pairs) [left, right] with
                        | none => exact .error .invalidRemoval
                        | some removal =>
                            let plan :
                                ParallelFusePlan source left right pairs :=
                              ⟨removal⟩
                            let candidate :=
                              parallelFuseCandidate arguments plan
                            match accepted :
                                ConcreteDiagram.checkWellFormed definitions
                                  candidate with
                            | .error error =>
                                exact .error (.malformedTarget error)
                            | .ok checked =>
                                let generated :=
                                  ConcreteDiagram.checkWellFormed_preserves_input
                                    accepted
                                let targetWire :=
                                  Internal.checkedWire generated
                                    (parallelFuseCandidateWire arguments plan)
                                match inverseAccepted :
                                    parallelSplit checked targetWire with
                                | .error _ =>
                                    exact .error .inverseDeleteRejected
                                | .ok inverse =>
                                    match
                                        ConcreteIsoSearch.findConcreteIso?
                                          inverse.checked.val source.val with
                                    | none =>
                                        exact .error
                                          .inverseIsomorphismRejected
                                    | some inverseIso =>
                                        exact .ok
                                          (ParallelFuseResult.mk leftSites
                                            rightSites pairs
                                            (pairParallelSites_length
                                              leftSites.sites rightSites.sites
                                              pairs paired)
                                            checked arguments
                                            leftSignature
                                            (by simpa [signatures] using
                                              rightSignature)
                                            plan generated targetWire rfl
                                            inverse inverseIso)
                | _, _ => exact .error .nonAppliedEndpoint
              else
                exact .error .scopeMismatch
            else
              exact .error .signatureMismatch

private structure EndsDeletePlan
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sites : AllAppliedSites source wire) where
  removal :
    Internal.BatchRemovalPlan source [] (removedSiteNodes sites) []

private def endsDeleteCandidate
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : AllAppliedSites source wire}
    (plan : EndsDeletePlan source wire sites) :
    ConcreteDiagram definitions.length :=
  Internal.batchRemovalCandidate plan.removal

/-- Checked dense removal of every applied head of one relation wire. -/
structure EndsDeleteResult
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) where
  private mk ::
  sites : AllAppliedSites source wire
  checked : CheckedDiagram definitions
  private plan : EndsDeletePlan source wire sites
  private generated : checked.val = endsDeleteCandidate plan

/-- Delete all and only the applied-head nodes of `wire`. -/
def deleteEnds
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :
    Except ContentError (EndsDeleteResult source wire) := by
  match checkedSites : checkAllAppliedSites source wire with
  | none => exact .error .nonAppliedEndpoint
  | some sites =>
      match removalAccepted :
          Internal.checkBatchRemovalPlan? source []
            (removedSiteNodes sites) [] with
      | none => exact .error .invalidRemoval
      | some removal =>
          let plan : EndsDeletePlan source wire sites := ⟨removal⟩
          let candidate := endsDeleteCandidate plan
          match accepted :
              ConcreteDiagram.checkWellFormed definitions candidate with
          | .error error => exact .error (.malformedTarget error)
          | .ok checked =>
              exact .ok
                (EndsDeleteResult.mk sites checked plan
                  (ConcreteDiagram.checkWellFormed_preserves_input accepted))

namespace EndsDeleteResult

/-- Exact source application nodes consumed by all-end deletion. -/
def sourceRemovedNodes
    (result : EndsDeleteResult source wire) : List source.val.NodeId :=
  removedSiteNodes result.sites

def retainedNodeCount
    (result : EndsDeleteResult source wire) : Nat :=
  (Internal.retainedNodes source result.sourceRemovedNodes).length

/-- Checked target nodes in dense retained-source allocation order. -/
def constructionNodeEquiv
    (result : EndsDeleteResult source wire) :
    Data.Finite.FiniteEquiv result.checked.val.NodeId
      (Fin result.retainedNodeCount) :=
  ContentConstruction.finEquivOfEq (by
    rw [congrArg ConcreteDiagram.nodeCount result.generated]
    rfl)

/-- Canonical checked image of one source node retained by deletion. -/
def retainedNodeImage
    (result : EndsDeleteResult source wire)
    (node : source.val.NodeId)
    (retained : node ∉ result.sourceRemovedNodes) :
    result.checked.val.NodeId :=
  Internal.checkedNode result.generated
    (Internal.retainedNodeIndex source result.sourceRemovedNodes node (by
      unfold Internal.retainedNodes
      exact List.mem_filter.mpr
        ⟨Data.Finite.mem_allFin node, decide_eq_true retained⟩))

@[simp] theorem constructionNodeEquiv_retainedNodeImage
    (result : EndsDeleteResult source wire)
    (node : source.val.NodeId)
    (retained : node ∉ result.sourceRemovedNodes) :
    result.constructionNodeEquiv
        (result.retainedNodeImage node retained) =
      Internal.retainedNodeIndex source result.sourceRemovedNodes node (by
        unfold Internal.retainedNodes
        exact List.mem_filter.mpr
          ⟨Data.Finite.mem_allFin node, decide_eq_true retained⟩) := by
  apply Fin.ext
  rfl

/-- Target-to-source region carrier of dense all-end deletion. -/
def regionOriginEquiv
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : EndsDeleteResult source wire) :
    Data.Finite.FiniteEquiv result.checked.val.RegionId source.val.RegionId :=
  ContentConstruction.finEquivOfEq (by
    rw [congrArg ConcreteDiagram.regionCount result.generated]
    change (Internal.retainedRegions source []).length = _
    rw [Internal.retainedRegions_nil]
    simp [ConcreteDiagram.regionsList,
      Data.Finite.allFin_eq_finRange])

/-- Target-to-source wire carrier of dense all-end deletion. -/
def wireOriginEquiv
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : EndsDeleteResult source wire) :
    Data.Finite.FiniteEquiv result.checked.val.WireId source.val.WireId :=
  ContentConstruction.finEquivOfEq (by
    rw [congrArg ConcreteDiagram.wireCount result.generated]
    change (Internal.retainedWires source []).length = _
    simp [Internal.retainedWires, ConcreteDiagram.wiresList,
      Data.Finite.allFin_eq_finRange,
      ContentConstruction.length_filter_true])

/-- Reappend the exact deleted nodes after the checked dense target and recover
the complete source node carrier in checker-owned site order. -/
def reconstructionNodeEquiv
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : EndsDeleteResult source wire) :
    Data.Finite.FiniteEquiv
      (Fin (result.checked.val.nodeCount + result.sites.sites.length))
      source.val.NodeId :=
  (ContentConstruction.finEquivOfEq (by
    rw [congrArg ConcreteDiagram.nodeCount result.generated]
    simp [endsDeleteCandidate, Internal.batchRemovalCandidate,
      ContentConstruction.partitionOrder, removedSiteNodes, siteNodes,
      Internal.retainedNodes, ConcreteDiagram.nodesList,
      Data.Finite.allFin_eq_finRange])).trans
    (ContentConstruction.partitionEquiv (removedSiteNodes result.sites)
      (ContentConstruction.siteNodes_nodup result.sites))

/-- Image of any retained source region in the exact dense deletion target. -/
def targetRegion
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : EndsDeleteResult source wire)
    (region : source.val.RegionId) :
    result.checked.val.RegionId :=
  have retained : region ∈ Internal.retainedRegions source [] := by
    unfold Internal.retainedRegions
    apply List.mem_filter.mpr
    exact ⟨Data.Finite.mem_allFin _, by simp⟩
  Internal.checkedRegion result.generated
    (Internal.retainedRegionIndex source [] region retained)

/-- Image of any retained source wire in the exact dense deletion target. -/
def targetWireImage
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : EndsDeleteResult source wire)
    (sourceWire : source.val.WireId) :
    result.checked.val.WireId :=
  have retained : sourceWire ∈ Internal.retainedWires source [] := by
    unfold Internal.retainedWires
    apply List.mem_filter.mpr
    exact ⟨Data.Finite.mem_allFin _, by simp⟩
  Internal.checkedWire result.generated
    (Internal.retainedWireIndex source [] sourceWire retained)

/-- Image of the retained acted wire in the exact dense deletion target. -/
def targetWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : EndsDeleteResult source wire) :
    result.checked.val.WireId :=
  have retained : wire ∈ Internal.retainedWires source [] := by
    unfold Internal.retainedWires
    apply List.mem_filter.mpr
    exact ⟨Data.Finite.mem_allFin _, by simp⟩
  Internal.checkedWire result.generated
    (Internal.retainedWireIndex source [] wire retained)

theorem targetRoot_exact
    (result : EndsDeleteResult source wire) :
    result.checked.val.root = result.targetRegion source.val.root := by
  unfold targetRegion
  rw [Internal.checkedRoot_transport result.generated]
  rfl

theorem targetRegion_data
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : EndsDeleteResult source wire)
    (region : source.val.RegionId) :
    result.checked.val.regions (result.targetRegion region) =
      (match source.val.regions region with
      | .sheet => .sheet
      | .cut parent => .cut (result.targetRegion parent) :
        CRegion result.checked.val.regionCount) := by
  let retained : region ∈ Internal.retainedRegions source [] := by
    rw [Internal.retainedRegions_nil]
    exact Data.Finite.mem_allFin region
  cases data : source.val.regions region with
  | sheet =>
      apply Internal.checkedRegion_data_transport_sheet result.generated
      exact Internal.batchRegionTable_retained_sheet
        result.plan.removal region retained data
  | cut parent =>
      let parentRetained : parent ∈ Internal.retainedRegions source [] := by
        rw [Internal.retainedRegions_nil]
        exact Data.Finite.mem_allFin parent
      simpa [targetRegion] using
        Internal.checkedRegion_data_transport_cut result.generated
          (Internal.retainedRegionIndex source [] region retained)
          (Internal.retainedRegionIndex source [] parent parentRetained)
          (Internal.batchRegionTable_retained_cut result.plan.removal
            region retained parent data parentRetained)

theorem retainedNodeImage_data
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : EndsDeleteResult source wire)
    (node : source.val.NodeId)
    (retained : node ∉ result.sourceRemovedNodes) :
    result.checked.val.nodes (result.retainedNodeImage node retained) =
      (match source.val.nodes node with
      | .atom region arguments =>
          .atom (result.targetRegion region) arguments
      | .ref region definition arguments =>
          .ref (result.targetRegion region) definition arguments
      | .identity region signature arity =>
          .identity (result.targetRegion region) signature arity :
        CNode result.checked.val.regionCount definitions.length) := by
  unfold retainedNodeImage sourceRemovedNodes targetRegion
  rw [Internal.checkedNode_data_transport result.generated]
  simp only [endsDeleteCandidate, Internal.batchRemovalCandidate]
  rw [Internal.batchNodeTable_noRegions,
    Internal.sourceRetainedNode_retainedNodeIndex]
  cases source.val.nodes node <;> rfl

theorem targetWireImage_signature
    (result : EndsDeleteResult source wire)
    (sourceWire : source.val.WireId) :
    (result.checked.val.wires (result.targetWireImage sourceWire)).sig =
      (source.val.wires sourceWire).sig := by
  unfold targetWireImage
  rw [Internal.checkedWire_signature_transport result.generated]
  simp [endsDeleteCandidate, Internal.batchRemovalCandidate]

theorem targetWireImage_scope
    (result : EndsDeleteResult source wire)
    (sourceWire : source.val.WireId) :
    (result.checked.val.wires (result.targetWireImage sourceWire)).scope =
      result.targetRegion (source.val.wires sourceWire).scope := by
  unfold targetWireImage targetRegion
  rw [Internal.checkedWire_scope_transport result.generated]
  simp [endsDeleteCandidate, Internal.batchRemovalCandidate]

/-- Source-filtered endpoint construction for one retained wire. -/
def targetEndpoints
    (result : EndsDeleteResult source wire)
    (sourceWire : source.val.WireId) :
    List (CEndpoint result.checked.val.nodeCount) :=
  ((source.val.wires sourceWire).endpoints.filterMap
    (Internal.batchEndpoint? source result.sourceRemovedNodes)).map
      (Internal.checkedEndpoint result.generated)

theorem targetWireImage_endpoints
    (result : EndsDeleteResult source wire)
    (sourceWire : source.val.WireId) :
    (result.checked.val.wires
      (result.targetWireImage sourceWire)).endpoints =
      result.targetEndpoints sourceWire := by
  unfold targetWireImage targetEndpoints sourceRemovedNodes
  rw [Internal.checkedWire_endpoints_transport result.generated]
  simp only [endsDeleteCandidate, Internal.batchRemovalCandidate]
  simp only [Internal.batchWireTable]
  rw [Internal.sourceRetainedWire_retainedWireIndex]

end EndsDeleteResult

private def spawnNode
    {definitions : List (List Sig)}
    (source : CheckedDiagram definitions)
    {wire : source.val.WireId}
    (sites : List (EndSite source wire))
    (site : Fin sites.length) :
    Fin (source.val.nodeCount + sites.length) :=
  Fin.natAdd source.val.nodeCount site

private def spawnArgumentEndpoints
    {definitions : List (List Sig)}
    (source : CheckedDiagram definitions)
    {target : source.val.WireId}
    (sites : List (EndSite source target))
    (candidate : source.val.WireId) :
    List (CEndpoint (source.val.nodeCount + sites.length)) :=
  (Data.Finite.allFin sites.length).flatMap fun site =>
    (List.range (sites.get site).arguments.length).filterMap fun position =>
      match (sites.get site).arguments[position]? with
      | some argument =>
          if argument = candidate then
            some
              { node := spawnNode source sites site
                port := .arg position }
          else
            none
      | none => none

private def endsSpawnCandidate
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (signature : List Sig)
    (sites : List (EndSite source wire)) :
    ConcreteDiagram definitions.length where
  regionCount := source.val.regionCount
  nodeCount := source.val.nodeCount + sites.length
  wireCount := source.val.wireCount
  root := source.val.root
  regions := source.val.regions
  nodes :=
    Fin.addCases source.val.nodes fun site =>
      .atom (sites.get site).region signature
  wires := fun candidate =>
    let data := source.val.wires candidate
    { data with
      endpoints :=
        (data.endpoints.map fun endpoint =>
          ({ node := Fin.castAdd sites.length endpoint.node
             port := endpoint.port } :
            CEndpoint (source.val.nodeCount + sites.length)))
        ++
        (if candidate = wire then
          ((Data.Finite.allFin sites.length).map fun site =>
            ({ node := spawnNode source sites site
               port := .head } :
              CEndpoint (source.val.nodeCount + sites.length)))
        else
          [])
        ++ spawnArgumentEndpoints source sites candidate }

private def siteArgumentsValid
    (source : CheckedDiagram definitions)
    (signature : List Sig)
    (arguments : List source.val.WireId) : Bool :=
  arguments.length = signature.length &&
    (List.zip arguments signature).all fun pair =>
      (source.val.wires pair.1).sig == pair.2

private def siteVisible
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (site : EndSite source wire) : Bool :=
  source.val.Encloses (source.val.wires wire).scope site.region &&
    site.arguments.all fun argument =>
      decide
        (source.val.Encloses
          (source.val.wires argument).scope site.region)

/-- Checked dense spawning of one applied head at every requested site. -/
structure EndsSpawnResult
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sites : List (EndSite source wire)) where
  private mk ::
  checked : CheckedDiagram definitions
  private signature : List Sig
  private signature_exact :
    (source.val.wires wire).sig = .rel signature
  private generated :
    checked.val =
      endsSpawnCandidate source wire signature sites
  inverseWire : checked.val.WireId
  private inverseWire_exact :
    inverseWire = Internal.checkedWire generated wire
  inverse : EndsDeleteResult checked inverseWire
  inverseIso : ConcreteIso inverse.checked.val source.val

namespace EndsSpawnResult

/-- Spawn checking transports the raw prefix/suffix node carrier exactly. -/
def constructionNodeEquiv
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : List (EndSite source wire)}
    (result : EndsSpawnResult source wire sites) :
    Data.Finite.FiniteEquiv result.checked.val.NodeId
      (Fin (source.val.nodeCount + sites.length)) :=
  ContentConstruction.finEquivOfEq (by
    rw [congrArg ConcreteDiagram.nodeCount result.generated]
    rfl)

/-- Spawn checking preserves the source region carrier exactly. -/
def regionOriginEquiv
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : List (EndSite source wire)}
    (result : EndsSpawnResult source wire sites) :
    Data.Finite.FiniteEquiv result.checked.val.RegionId source.val.RegionId :=
  ContentConstruction.finEquivOfEq (by
    rw [congrArg ConcreteDiagram.regionCount result.generated]
    rfl)

/-- Spawn checking preserves the source wire carrier exactly. -/
def wireOriginEquiv
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {sites : List (EndSite source wire)}
    (result : EndsSpawnResult source wire sites) :
    Data.Finite.FiniteEquiv result.checked.val.WireId source.val.WireId :=
  ContentConstruction.finEquivOfEq (by
    rw [congrArg ConcreteDiagram.wireCount result.generated]
    rfl)

end EndsSpawnResult

/-- Spawn applied heads on an endpoint-free relation wire at checked sites. -/
def spawnEnds
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (sites : List (EndSite source wire)) :
    Except ContentError (EndsSpawnResult source wire sites) := by
  match signature : (source.val.wires wire).sig with
  | .iota => exact .error .expectedRelation
  | .rel arguments =>
      if occupied : (source.val.wires wire).endpoints ≠ [] then
        exact .error .wireHasEndpoints
      else if empty : sites = [] then
        exact .error .emptySites
      else if arity :
          !(sites.all fun site =>
            siteArgumentsValid source arguments site.arguments) then
        exact .error .argumentArity
      else if visible :
          !(sites.all fun site => siteVisible source wire site) then
        exact .error .siteOutsideScope
      else
        let candidate := endsSpawnCandidate source wire arguments sites
        match accepted :
            ConcreteDiagram.checkWellFormed definitions candidate with
        | .error error => exact .error (.malformedTarget error)
        | .ok checked =>
            let generated :=
              ConcreteDiagram.checkWellFormed_preserves_input accepted
            let inverseWire := Internal.checkedWire generated wire
            match inverseAccepted : deleteEnds checked inverseWire with
            | .error _ => exact .error .inverseDeleteRejected
            | .ok inverse =>
                match
                    ConcreteIsoSearch.findConcreteIso?
                      inverse.checked.val source.val with
                | none => exact .error .inverseIsomorphismRejected
                | some inverseIso =>
                    exact .ok
                      (EndsSpawnResult.mk checked arguments signature generated
                        inverseWire rfl inverse inverseIso)

end ConcreteWirePrimitive

end VisualProof
