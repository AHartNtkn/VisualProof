import VisualProof.Diagram.Context
import VisualProof.Diagram.Concrete.Elaborate
import VisualProof.Diagram.Concrete.OpenCompilation
import VisualProof.Diagram.Concrete.Subgraph.Occurrence

namespace VisualProof

def mapRegion (map : Fin sourceCount → Fin targetCount) :
    CRegion sourceCount → CRegion targetCount
  | .sheet => .sheet
  | .cut parent => .cut (map parent)

def mapNode (map : Fin sourceCount → Fin targetCount) :
    CNode sourceCount definitionCount → CNode targetCount definitionCount
  | .atom region args => .atom (map region) args
  | .ref region definition args => .ref (map region) definition args
  | .identity region sig arity => .identity (map region) sig arity

namespace DenseList

/-- Executable dense index of a proved list member. -/
def index [DecidableEq α]
    (values : List α) (value : α) (member : value ∈ values) :
    Fin values.length :=
  (Data.Finite.indexOf? values value).get
    (Data.Finite.indexOf?_isSome_iff.mpr member)

theorem get_index [DecidableEq α]
    (values : List α) (value : α) (member : value ∈ values) :
    values.get (index values value member) = value := by
  unfold index
  let hsome : (Data.Finite.indexOf? values value).isSome = true :=
    Data.Finite.indexOf?_isSome_iff.mpr member
  obtain ⟨found, hfound⟩ := Option.isSome_iff_exists.mp hsome
  calc
    values.get ((Data.Finite.indexOf? values value).get _) =
        values.get found := congrArg values.get
          (Option.get_of_eq_some hsome hfound)
    _ = value := by
      simpa only [List.get_eq_getElem] using
        Data.Finite.indexOf?_sound hfound

theorem index_get [DecidableEq α]
    (values : List α) (nodup : values.Nodup)
    (position : Fin values.length) :
    index values (values.get position) (List.get_mem values position) =
      position := by
  unfold index
  let hsome :
      (Data.Finite.indexOf? values (values.get position)).isSome = true :=
    Data.Finite.indexOf?_isSome_iff.mpr (List.get_mem values position)
  exact Option.get_of_eq_some hsome
    (Data.Finite.indexOf?_get_eq_some_of_nodup nodup position)

end DenseList

private instance selectionInputDecidableEq
    {definitions : List (List Sig)}
    {host : CheckedDiagram definitions} :
    DecidableEq (SelectionInput host) := by
  intro left right
  cases left
  cases right
  simp only [SelectionInput.mk.injEq]
  infer_instance

/-- Stable refusal vocabulary for checked occurrence extraction. -/
inductive ExtractionError
  | selectionMismatch
  | boundaryMismatch
  | compilationFailed
  deriving Repr, DecidableEq

/--
Proof-independent receipt that a checked occurrence is being consumed through
the supplied exact selection and that its authoritative open pattern compiled.
-/
structure CheckedExtraction
    {definitions : List (List Sig)}
    {pattern : CheckedOpenDiagram definitions}
    {host : CheckedDiagram definitions}
    (selection : CheckedSelection host)
    (occurrence : Occurrence pattern host) where
  private mk ::
  private selection_input :
    occurrence.toSelection.input = selection.input
  private boundary_seam :
    occurrence.boundaryAttachments = selection.touchingWires
  compilation : OpenCompilation pattern

namespace CheckedExtraction

/-- The checked fragment is exactly the occurrence's authoritative pattern. -/
def checked
    {definitions : List (List Sig)}
    {pattern : CheckedOpenDiagram definitions}
    {host : CheckedDiagram definitions}
    {selection : CheckedSelection host}
    {occurrence : Occurrence pattern host}
    (_extraction : CheckedExtraction selection occurrence) :
    CheckedOpenDiagram definitions :=
  pattern

theorem selection_matches
    {definitions : List (List Sig)}
    {pattern : CheckedOpenDiagram definitions}
    {host : CheckedDiagram definitions}
    {selection : CheckedSelection host}
    {occurrence : Occurrence pattern host}
    (extraction : CheckedExtraction selection occurrence) :
    occurrence.toSelection.input = selection.input :=
  extraction.selection_input

theorem boundary_matches
    {definitions : List (List Sig)}
    {pattern : CheckedOpenDiagram definitions}
    {host : CheckedDiagram definitions}
    {selection : CheckedSelection host}
    {occurrence : Occurrence pattern host}
    (extraction : CheckedExtraction selection occurrence) :
    occurrence.boundaryAttachments = selection.touchingWires :=
  extraction.boundary_seam

def openDiagram
    {definitions : List (List Sig)}
    {pattern : CheckedOpenDiagram definitions}
    {host : CheckedDiagram definitions}
    {selection : CheckedSelection host}
    {occurrence : Occurrence pattern host}
    (extraction : CheckedExtraction selection occurrence) :
    OpenDiagram definitions (checkedBoundarySigs pattern) :=
  extraction.compilation.openDiagram

end CheckedExtraction

/--
Validate exact selection identity and the exact ordered boundary seam, then
compile the occurrence-owned pattern.
-/
def checkExtraction
    {definitions : List (List Sig)}
    {pattern : CheckedOpenDiagram definitions}
    {host : CheckedDiagram definitions}
    (selection : CheckedSelection host)
    (occurrence : Occurrence pattern host) :
    Except ExtractionError (CheckedExtraction selection occurrence) := by
  if same : occurrence.toSelection.input = selection.input then
    if seam :
        occurrence.boundaryAttachments = selection.touchingWires then
      match accepted : compileOpen pattern with
      | none => exact .error .compilationFailed
      | some compilation =>
          exact .ok (CheckedExtraction.mk same seam compilation)
    else
      exact .error .boundaryMismatch
  else
    exact .error .selectionMismatch

/--
The occurrence's exact derived selection passes when its ordered boundary is
exactly the touching-wire seam and its pattern compiles.
-/
theorem checkExtraction_accepts_exact
    {definitions : List (List Sig)}
    {pattern : CheckedOpenDiagram definitions}
    {host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host)
    (seam :
      occurrence.boundaryAttachments =
        occurrence.toSelection.touchingWires)
    (compilation : OpenCompilation pattern)
    (accepted : compileOpen pattern = some compilation) :
    ∃ extraction,
      checkExtraction occurrence.toSelection occurrence = .ok extraction := by
  unfold checkExtraction
  split
  · split
    · rename_i rejected
      rw [accepted] at rejected
      contradiction
    · exact ⟨_, rfl⟩
  · rename_i mismatch
    exact False.elim (mismatch rfl)

/-- A different durable selection input is refused before compilation. -/
theorem checkExtraction_rejects_mismatch
    {definitions : List (List Sig)}
    {pattern : CheckedOpenDiagram definitions}
    {host : CheckedDiagram definitions}
    (selection : CheckedSelection host)
    (occurrence : Occurrence pattern host)
    (mismatch : occurrence.toSelection.input ≠ selection.input) :
    checkExtraction selection occurrence = .error .selectionMismatch := by
  simp [checkExtraction, mismatch]

/-- A non-exact ordered boundary seam is refused before compilation. -/
theorem checkExtraction_rejects_boundary_mismatch
    {definitions : List (List Sig)}
    {pattern : CheckedOpenDiagram definitions}
    {host : CheckedDiagram definitions}
    (selection : CheckedSelection host)
    (occurrence : Occurrence pattern host)
    (selectionSame :
      occurrence.toSelection.input = selection.input)
    (mismatch :
      occurrence.boundaryAttachments ≠ selection.touchingWires) :
    checkExtraction selection occurrence = .error .boundaryMismatch := by
  simp [checkExtraction, selectionSame, mismatch]

namespace Removal

private def selection
    (occurrence : Occurrence pattern host) :
    CheckedSelection host :=
  occurrence.toSelection

/--
Retain the host frame in host order. The host root and selection anchor are
explicitly retained; selected proper subtrees are dropped.
-/
def regions (occurrence : Occurrence pattern host) :
    List host.val.RegionId :=
  host.val.regionsList.filter fun region =>
    decide (
      region = host.val.root ∨
      region = (selection occurrence).region ∨
      region ∉ (selection occurrence).allRegions)

/-- Retain exactly the nodes outside the selected node closure. -/
def nodes (occurrence : Occurrence pattern host) :
    List host.val.NodeId :=
  host.val.nodesList.filter fun node =>
    decide (node ∉ (selection occurrence).allNodes)

/-- Retain exactly the wires not internalized by the selection. -/
def wires (occurrence : Occurrence pattern host) :
    List host.val.WireId :=
  host.val.wiresList.filter fun wire =>
    decide (wire ∉ (selection occurrence).internalWires)

theorem regions_nodup (occurrence : Occurrence pattern host) :
    (regions occurrence).Nodup :=
  Data.Finite.allFin_nodup host.val.regionCount |>.filter _

theorem nodes_nodup (occurrence : Occurrence pattern host) :
    (nodes occurrence).Nodup :=
  Data.Finite.allFin_nodup host.val.nodeCount |>.filter _

theorem wires_nodup (occurrence : Occurrence pattern host) :
    (wires occurrence).Nodup :=
  Data.Finite.allFin_nodup host.val.wireCount |>.filter _

theorem host_root_mem (occurrence : Occurrence pattern host) :
    host.val.root ∈ regions occurrence := by
  simp [regions, ConcreteDiagram.regionsList,
    Data.Finite.mem_allFin]

theorem anchor_mem (occurrence : Occurrence pattern host) :
    (selection occurrence).region ∈ regions occurrence := by
  simp [regions, ConcreteDiagram.regionsList,
    Data.Finite.mem_allFin]

theorem touchingWire_retained
    (occurrence : Occurrence pattern host)
    (wire : host.val.WireId)
    (touching : wire ∈ (selection occurrence).touchingWires) :
    wire ∈ wires occurrence := by
  simp only [wires, List.mem_filter, ConcreteDiagram.wiresList,
    Data.Finite.mem_allFin, true_and]
  apply decide_eq_true
  intro internal
  exact (selection occurrence).internal_not_touching wire internal touching

def regionIndex (occurrence : Occurrence pattern host)
    (region : host.val.RegionId)
    (member : region ∈ regions occurrence) :
    Fin (regions occurrence).length :=
  DenseList.index (regions occurrence) region member

def nodeIndex (occurrence : Occurrence pattern host)
    (node : host.val.NodeId)
    (member : node ∈ nodes occurrence) :
    Fin (nodes occurrence).length :=
  DenseList.index (nodes occurrence) node member

def wireIndex (occurrence : Occurrence pattern host)
    (wire : host.val.WireId)
    (member : wire ∈ wires occurrence) :
    Fin (wires occurrence).length :=
  DenseList.index (wires occurrence) wire member

def sourceRegion (occurrence : Occurrence pattern host)
    (region : Fin (regions occurrence).length) : host.val.RegionId :=
  (regions occurrence).get region

def sourceNode (occurrence : Occurrence pattern host)
    (node : Fin (nodes occurrence).length) : host.val.NodeId :=
  (nodes occurrence).get node

def sourceWire (occurrence : Occurrence pattern host)
    (wire : Fin (wires occurrence).length) : host.val.WireId :=
  (wires occurrence).get wire

@[simp] theorem sourceRegion_regionIndex
    (occurrence : Occurrence pattern host)
    (region : host.val.RegionId)
    (member : region ∈ regions occurrence) :
    sourceRegion occurrence (regionIndex occurrence region member) = region :=
  DenseList.get_index _ _ _

@[simp] theorem sourceNode_nodeIndex
    (occurrence : Occurrence pattern host)
    (node : host.val.NodeId)
    (member : node ∈ nodes occurrence) :
    sourceNode occurrence (nodeIndex occurrence node member) = node :=
  DenseList.get_index _ _ _

@[simp] theorem sourceWire_wireIndex
    (occurrence : Occurrence pattern host)
    (wire : host.val.WireId)
    (member : wire ∈ wires occurrence) :
    sourceWire occurrence (wireIndex occurrence wire member) = wire :=
  DenseList.get_index _ _ _

@[simp] theorem regionIndex_sourceRegion
    (occurrence : Occurrence pattern host)
    (region : Fin (regions occurrence).length) :
    regionIndex occurrence (sourceRegion occurrence region)
      (List.get_mem _ region) = region :=
  DenseList.index_get _ (regions_nodup occurrence) region

@[simp] theorem nodeIndex_sourceNode
    (occurrence : Occurrence pattern host)
    (node : Fin (nodes occurrence).length) :
    nodeIndex occurrence (sourceNode occurrence node)
      (List.get_mem _ node) = node :=
  DenseList.index_get _ (nodes_nodup occurrence) node

@[simp] theorem wireIndex_sourceWire
    (occurrence : Occurrence pattern host)
    (wire : Fin (wires occurrence).length) :
    wireIndex occurrence (sourceWire occurrence wire)
      (List.get_mem _ wire) = wire :=
  DenseList.index_get _ (wires_nodup occurrence) wire

private def endpoint?
    (occurrence : Occurrence pattern host)
    (endpoint : CEndpoint host.val.nodeCount) :
    Option (CEndpoint (nodes occurrence).length) :=
  if retained : endpoint.node ∈ nodes occurrence then
    some ⟨nodeIndex occurrence endpoint.node retained, endpoint.port⟩
  else
    none

def sourceEndpoint
    (occurrence : Occurrence pattern host)
    (endpoint : CEndpoint (nodes occurrence).length) :
    CEndpoint host.val.nodeCount :=
  ⟨sourceNode occurrence endpoint.node, endpoint.port⟩

@[simp] theorem sourceEndpoint_index
    (occurrence : Occurrence pattern host)
    (endpoint : CEndpoint host.val.nodeCount)
    (retained : endpoint.node ∈ nodes occurrence) :
    sourceEndpoint occurrence
        ⟨nodeIndex occurrence endpoint.node retained, endpoint.port⟩ =
      endpoint := by
  cases endpoint
  simp [sourceEndpoint, sourceNode_nodeIndex]

private theorem retainedRegion_parent_mem
    (occurrence : Occurrence pattern host)
    (region parent : host.val.RegionId)
    (retained : region ∈ regions occurrence)
    (regionData : host.val.regions region = .cut parent) :
    parent ∈ regions occurrence := by
  apply List.mem_filter.mpr
  refine ⟨Data.Finite.mem_allFin _, decide_eq_true (.inr (.inr ?_))⟩
  intro parentSelected
  have regionSelected :
      region ∈ occurrence.toSelection.allRegions := by
    obtain ⟨patternParent, parentNonroot, parentMapped⟩ :=
      (Occurrence.mem_toSelection_allRegions_iff_image occurrence parent).mp
        parentSelected
    have hostChild :
        region ∈ host.val.childrenOf
          (occurrence.regionMap patternParent) := by
      simp [ConcreteDiagram.childrenOf,
        ConcreteDiagram.regionsList, Data.Finite.mem_allFin,
        regionData, parentMapped]
    have mappedChild :
        region ∈
          (pattern.val.diagram.childrenOf patternParent).map
            occurrence.regionMap :=
      (occurrence.properChildren_exact patternParent
        parentNonroot).mem_iff.mpr hostChild
    obtain ⟨patternChild, childMember, childMapped⟩ :=
      List.mem_map.mp mappedChild
    have childNonroot :
        patternChild ≠ pattern.val.diagram.root := by
      intro same
      subst patternChild
      simp [ConcreteDiagram.childrenOf,
        ConcreteDiagram.regionsList,
        Data.Finite.mem_allFin] at childMember
      rw [pattern.property.diagram.root_is_sheet] at childMember
      contradiction
    exact
      (Occurrence.mem_toSelection_allRegions_iff_image occurrence region).mpr
        ⟨patternChild, childNonroot, childMapped⟩
  have retainedCase :
      region = host.val.root ∨
        region = occurrence.toSelection.region ∨
          region ∉ occurrence.toSelection.allRegions := by
    exact of_decide_eq_true
      (List.mem_filter.mp retained).2
  rcases retainedCase with root | anchor | outside
  · subst region
    rw [host.property.root_is_sheet] at regionData
    contradiction
  · subst region
    obtain ⟨patternRegion, nonroot, mapped⟩ :=
      (Occurrence.mem_toSelection_allRegions_iff_image occurrence
        occurrence.toSelection.region).mp regionSelected
    have same :
        occurrence.regionMap patternRegion =
          occurrence.regionMap pattern.val.diagram.root := by
      calc
        occurrence.regionMap patternRegion =
            occurrence.toSelection.region := mapped
        _ = occurrence.region := Occurrence.toSelection_region occurrence
        _ = occurrence.regionMap pattern.val.diagram.root :=
          occurrence.maps_root.symm
    exact nonroot (occurrence.regionMap_injective same)
  · exact outside regionSelected

private def regionTable
    (occurrence : Occurrence pattern host)
    (region : Fin (regions occurrence).length) :
    CRegion (regions occurrence).length :=
  match host.val.regions (sourceRegion occurrence region) with
  | .sheet => .sheet
  | .cut parent =>
      if retained : parent ∈ regions occurrence then
        .cut (regionIndex occurrence parent retained)
      else
        .sheet

private theorem sourceNode_region_mem
    (occurrence : Occurrence pattern host)
    (node : Fin (nodes occurrence).length) :
    (host.val.nodes (sourceNode occurrence node)).region ∈
      regions occurrence := by
  have outside :
      sourceNode occurrence node ∉ (selection occurrence).allNodes :=
    of_decide_eq_true
      (List.mem_filter.mp (List.get_mem (nodes occurrence) node)).2
  have regionOutside :
      (host.val.nodes (sourceNode occurrence node)).region ∉
        (selection occurrence).allRegions := by
    intro selected
    apply outside
    rw [CheckedSelection.mem_allNodes]
    exact .inr selected
  apply List.mem_filter.mpr
  refine ⟨Data.Finite.mem_allFin _, decide_eq_true ?_⟩
  exact .inr (.inr regionOutside)

private def nodeRegion
    (occurrence : Occurrence pattern host)
    (node : Fin (nodes occurrence).length) :
    Fin (regions occurrence).length :=
  regionIndex occurrence
    (host.val.nodes (sourceNode occurrence node)).region
    (sourceNode_region_mem occurrence node)

private def nodeTable
    {definitions : List (List Sig)}
    {pattern : CheckedOpenDiagram definitions}
    {host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host)
    (node : Fin (nodes occurrence).length) :
    CNode (regions occurrence).length definitions.length :=
  match host.val.nodes (sourceNode occurrence node) with
  | .atom _ args => .atom (nodeRegion occurrence node) args
  | .ref _ definition args =>
      .ref (nodeRegion occurrence node) definition args
  | .identity _ sig arity =>
      .identity (nodeRegion occurrence node) sig arity

private theorem sourceWire_scope_mem
    (occurrence : Occurrence pattern host)
    (wire : Fin (wires occurrence).length) :
    (host.val.wires (sourceWire occurrence wire)).scope ∈
      regions occurrence := by
  have external :
      sourceWire occurrence wire ∉
        (selection occurrence).internalWires :=
    of_decide_eq_true
      (List.mem_filter.mp (List.get_mem (wires occurrence) wire)).2
  have scopeOutside :
      (host.val.wires (sourceWire occurrence wire)).scope ∉
        (selection occurrence).allRegions := by
    intro selected
    apply external
    rw [CheckedSelection.mem_internalWires]
    exact .inl selected
  apply List.mem_filter.mpr
  refine ⟨Data.Finite.mem_allFin _, decide_eq_true ?_⟩
  exact .inr (.inr scopeOutside)

private def wireScope
    (occurrence : Occurrence pattern host)
    (wire : Fin (wires occurrence).length) :
    Fin (regions occurrence).length :=
  regionIndex occurrence
    (host.val.wires (sourceWire occurrence wire)).scope
    (sourceWire_scope_mem occurrence wire)

private def wireTable
    (occurrence : Occurrence pattern host)
    (wire : Fin (wires occurrence).length) :
    CWire (regions occurrence).length (nodes occurrence).length :=
  let source := sourceWire occurrence wire
  let hostWire := host.val.wires source
  { sig := hostWire.sig
    scope := wireScope occurrence wire
    endpoints := hostWire.endpoints.filterMap (endpoint? occurrence) }

/-- Generated host complement with the retained anchor as its splice site. -/
def diagram
    {definitions : List (List Sig)}
    {pattern : CheckedOpenDiagram definitions}
    {host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host) :
    ConcreteDiagram definitions.length where
  regionCount := (regions occurrence).length
  nodeCount := (nodes occurrence).length
  wireCount := (wires occurrence).length
  root := regionIndex occurrence host.val.root (host_root_mem occurrence)
  regions := regionTable occurrence
  nodes := nodeTable occurrence
  wires := wireTable occurrence

theorem diagramRegion_rename
    (occurrence : Occurrence pattern host)
    (region : Fin (regions occurrence).length) :
    host.val.regions (sourceRegion occurrence region) =
      mapRegion (sourceRegion occurrence)
        ((diagram occurrence).regions region) := by
  cases regionData :
      host.val.regions (sourceRegion occurrence region) with
  | sheet =>
      simp [diagram, regionTable, regionData, mapRegion]
  | cut parent =>
      have parentRetained :
          parent ∈ regions occurrence :=
        retainedRegion_parent_mem occurrence
          (sourceRegion occurrence region) parent
          (List.get_mem (regions occurrence) region) regionData
      simp [diagram, regionTable, regionData, parentRetained, mapRegion,
        sourceRegion_regionIndex]

theorem diagramNode_rename
    (occurrence : Occurrence pattern host)
    (node : Fin (nodes occurrence).length) :
    host.val.nodes (sourceNode occurrence node) =
      mapNode (sourceRegion occurrence)
        ((diagram occurrence).nodes node) := by
  cases nodeData : host.val.nodes (sourceNode occurrence node) with
  | atom region args =>
      simp [diagram, nodeTable, nodeRegion, nodeData, mapNode,
        CNode.region, sourceRegion_regionIndex]
  | ref region definition args =>
      simp [diagram, nodeTable, nodeRegion, nodeData, mapNode,
        CNode.region, sourceRegion_regionIndex]
  | identity region sig arity =>
      simp [diagram, nodeTable, nodeRegion, nodeData, mapNode,
        CNode.region, sourceRegion_regionIndex]

theorem diagramWire_signature
    (occurrence : Occurrence pattern host)
    (wire : Fin (wires occurrence).length) :
    (host.val.wires (sourceWire occurrence wire)).sig =
      ((diagram occurrence).wires wire).sig :=
  rfl

theorem diagramWire_scope_rename
    (occurrence : Occurrence pattern host)
    (wire : Fin (wires occurrence).length) :
    (host.val.wires (sourceWire occurrence wire)).scope =
      sourceRegion occurrence ((diagram occurrence).wires wire).scope := by
  simp [diagram, wireTable, wireScope, sourceRegion_regionIndex]

theorem diagramEndpoint_mem_iff
    (occurrence : Occurrence pattern host)
    (wire : Fin (wires occurrence).length)
    (endpoint : CEndpoint (nodes occurrence).length) :
    endpoint ∈ ((diagram occurrence).wires wire).endpoints ↔
      sourceEndpoint occurrence endpoint ∈
        (host.val.wires (sourceWire occurrence wire)).endpoints := by
  constructor
  · intro member
    change
      endpoint ∈
        List.filterMap (endpoint? occurrence)
          (host.val.wires (sourceWire occurrence wire)).endpoints at member
    rcases List.mem_filterMap.mp member with
      ⟨candidate, incident, mapped⟩
    unfold endpoint? at mapped
    split at mapped
    · rename_i retained
      have equality :
          (⟨nodeIndex occurrence candidate.node retained,
              candidate.port⟩ :
            CEndpoint (nodes occurrence).length) = endpoint :=
        Option.some.inj mapped
      have indexEquality :
          nodeIndex occurrence candidate.node retained = endpoint.node :=
        congrArg CEndpoint.node equality
      have nodeEquality :
          candidate.node = sourceNode occurrence endpoint.node := by
        calc
          candidate.node =
              sourceNode occurrence
                (nodeIndex occurrence candidate.node retained) :=
            (sourceNode_nodeIndex occurrence
              candidate.node retained).symm
          _ = sourceNode occurrence endpoint.node :=
            congrArg (sourceNode occurrence) indexEquality
      have portEquality : candidate.port = endpoint.port :=
        congrArg CEndpoint.port equality
      simpa [sourceEndpoint, ← nodeEquality, ← portEquality] using incident
    · contradiction
  · intro incident
    have retained :
        (sourceEndpoint occurrence endpoint).node ∈ nodes occurrence := by
      change sourceNode occurrence endpoint.node ∈ nodes occurrence
      exact List.get_mem (nodes occurrence) endpoint.node
    have equality :
        (⟨nodeIndex occurrence
              (sourceEndpoint occurrence endpoint).node retained,
            (sourceEndpoint occurrence endpoint).port⟩ :
          CEndpoint (nodes occurrence).length) = endpoint := by
      cases endpoint
      simp [sourceEndpoint, nodeIndex_sourceNode]
    change
      endpoint ∈
        List.filterMap (endpoint? occurrence)
          (host.val.wires (sourceWire occurrence wire)).endpoints
    apply List.mem_filterMap.mpr
    refine ⟨sourceEndpoint occurrence endpoint, incident, ?_⟩
    unfold endpoint?
    simp only [retained, dite_true]
    exact congrArg some equality

/-- Dense identifier of the retained anchor region. -/
def site (occurrence : Occurrence pattern host) :
    (diagram occurrence).RegionId :=
  regionIndex occurrence (selection occurrence).region
    (anchor_mem occurrence)

end Removal

/-- Successful removal certifies only checker acceptance of the generated complement. -/
structure RemovalResult
    {definitions : List (List Sig)}
    {pattern : CheckedOpenDiagram definitions}
    {host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host) : Type where
  private mk ::
  private wellFormed : (Removal.diagram occurrence).WellFormed definitions

namespace RemovalResult

def complement
    {definitions : List (List Sig)}
    {pattern : CheckedOpenDiagram definitions}
    {host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (result : RemovalResult occurrence) :
    CheckedDiagram definitions :=
  ⟨Removal.diagram occurrence, result.wellFormed⟩

def site
    {definitions : List (List Sig)}
    {pattern : CheckedOpenDiagram definitions}
    {host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (_result : RemovalResult occurrence) :
    (Removal.diagram occurrence).RegionId :=
  Removal.site occurrence

@[simp] theorem complement_generated
    {definitions : List (List Sig)}
    {pattern : CheckedOpenDiagram definitions}
    {host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (result : RemovalResult occurrence) :
    result.complement.val = Removal.diagram occurrence :=
  rfl

@[simp] theorem site_generated
    {definitions : List (List Sig)}
    {pattern : CheckedOpenDiagram definitions}
    {host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (result : RemovalResult occurrence) :
    result.site = Removal.site occurrence :=
  rfl

theorem complement_wellFormed
    {definitions : List (List Sig)}
    {pattern : CheckedOpenDiagram definitions}
    {host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (result : RemovalResult occurrence) :
    result.complement.val.WellFormed definitions :=
  result.wellFormed

end RemovalResult

/-- Generate the partial complement and accept it only through the graph checker. -/
def remove
    {definitions : List (List Sig)}
    {pattern : CheckedOpenDiagram definitions}
    {host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host) :
    Except WFError (RemovalResult occurrence) := by
  match accepted :
      ConcreteDiagram.checkWellFormed definitions
        (Removal.diagram occurrence) with
  | .error error => exact .error error
  | .ok checked =>
      apply Except.ok
      apply RemovalResult.mk
      have same :=
        ConcreteDiagram.checkWellFormed_preserves_input accepted
      rw [← same]
      exact checked.property

end VisualProof
