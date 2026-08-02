import VisualProof.Diagram.Concrete.WireQuantifierBatchRemoval

namespace VisualProof

namespace ConcreteWireQuantifier

/--
One already-validated exact relation-sever occurrence.  The rule layer owns
copy matching and policy; this concrete owner consumes only its exact removal
extent, retained anchor, and ordered formal wires.
-/
structure RelationSeverSite
    (source : CheckedDiagram definitions) where
  region : source.val.RegionId
  removedRegions : List source.val.RegionId
  removedNodes : List source.val.NodeId
  removedWires : List source.val.WireId
  formals : List source.val.WireId
private def relationRemovedRegions
    {source : CheckedDiagram definitions}
    (sites : List (RelationSeverSite source)) :
    List source.val.RegionId :=
  sites.flatMap RelationSeverSite.removedRegions

private def relationRemovedNodes
    {source : CheckedDiagram definitions}
    (sites : List (RelationSeverSite source)) :
    List source.val.NodeId :=
  sites.flatMap RelationSeverSite.removedNodes

private def relationRemovedWires
    {source : CheckedDiagram definitions}
    (sites : List (RelationSeverSite source)) :
    List source.val.WireId :=
  sites.flatMap RelationSeverSite.removedWires

private def relationFormals
    {source : CheckedDiagram definitions}
    (sites : List (RelationSeverSite source)) :
    List source.val.WireId :=
  sites.flatMap RelationSeverSite.formals

private def relationSeverArgs
    {source : CheckedDiagram definitions}
    (sites : List (RelationSeverSite source)) :
    List Sig :=
  match sites with
  | [] => []
  | first :: _ =>
      first.formals.map fun wire => (source.val.wires wire).sig

private structure RelationSeverPlan
    (source : CheckedDiagram definitions)
    (scope : source.val.RegionId)
    (sites : List (RelationSeverSite source)) : Type where
  removal :
    Internal.BatchRemovalPlan source
      (relationRemovedRegions sites)
      (relationRemovedNodes sites)
      (relationRemovedWires sites)
  removedRegionsNodup : (relationRemovedRegions sites).Nodup
  removedNodesNodup : (relationRemovedNodes sites).Nodup
  removedWiresNodup : (relationRemovedWires sites).Nodup
  scopeRetained :
    scope ∈ Internal.retainedRegions source (relationRemovedRegions sites)
  siteRegionRetained :
    ∀ site : Fin sites.length,
      (sites.get site).region ∈
        Internal.retainedRegions source (relationRemovedRegions sites)
  formalRetained :
    ∀ site : Fin sites.length,
      ∀ position : Fin (sites.get site).formals.length,
        (sites.get site).formals.get position ∈
          Internal.retainedWires source (relationRemovedWires sites)
  signatureExact :
    ∀ site : Fin sites.length,
      (sites.get site).formals.map
          (fun wire => (source.val.wires wire).sig) =
        relationSeverArgs sites

private def checkRelationSeverPlan
    (source : CheckedDiagram definitions)
    (scope : source.val.RegionId)
    (sites : List (RelationSeverSite source)) :
    Except Error (RelationSeverPlan source scope sites) := by
  let removedRegions := relationRemovedRegions sites
  let removedNodes := relationRemovedNodes sites
  let removedWires := relationRemovedWires sites
  if nonempty : sites = [] then
    exact .error .emptyRelationSites
  else if disjoint :
      removedRegions.Nodup ∧
        removedNodes.Nodup ∧ removedWires.Nodup then
    if rootRemoved : source.val.root ∈ removedRegions then
      exact .error .removedRoot
    else if scopeRetained :
        scope ∈ Internal.retainedRegions source removedRegions then
      if sitesRetained :
          sites.all (fun site =>
            decide (
              site.region ∈ Internal.retainedRegions source removedRegions)) =
            true then
        if formalsRetained :
            sites.all (fun site =>
              site.formals.all (fun wire =>
                decide (
                  wire ∈ Internal.retainedWires source removedWires))) = true then
          if signaturesExact :
              sites.all (fun site =>
                decide (
                  site.formals.map
                      (fun wire => (source.val.wires wire).sig) =
                    relationSeverArgs sites)) = true then
            match removal :
                Internal.checkBatchRemovalPlan? source
                  removedRegions removedNodes removedWires with
            | none =>
                exact .error .invalidRemoval
            | some removalPlan =>
                exact .ok
                  { removal := by
                      simpa [removedRegions, removedNodes, removedWires]
                        using removalPlan
                    removedRegionsNodup := by
                      simpa [removedRegions] using disjoint.1
                    removedNodesNodup := by
                      simpa [removedNodes] using disjoint.2.1
                    removedWiresNodup := by
                      simpa [removedWires] using disjoint.2.2
                    scopeRetained := by
                      simpa [removedRegions] using scopeRetained
                    siteRegionRetained := by
                      intro site
                      exact of_decide_eq_true
                        ((List.all_eq_true.mp sitesRetained)
                          (sites.get site) (List.get_mem _ site))
                    formalRetained := by
                      intro site position
                      have siteAccepted :=
                        (List.all_eq_true.mp formalsRetained)
                          (sites.get site) (List.get_mem _ site)
                      exact of_decide_eq_true
                        ((List.all_eq_true.mp siteAccepted)
                          ((sites.get site).formals.get position)
                          (List.get_mem _ position))
                    signatureExact := by
                      intro site
                      exact of_decide_eq_true
                        ((List.all_eq_true.mp signaturesExact)
                          (sites.get site) (List.get_mem _ site)) }
          else
            exact .error .relationSignatureMismatch
        else
          match (relationFormals sites).find? fun wire =>
              decide (wire ∉ Internal.retainedWires source removedWires) with
          | some wire => exact .error (.removedFormal wire.val)
          | none => exact .error .invalidRemoval
      else
        exact .error .removedSite
    else
      exact .error .removedScope
  else
    exact .error .overlappingRemoval

private def relationSeverEndpoint?
    {source : CheckedDiagram definitions}
    (sites : List (RelationSeverSite source))
    (removedNodes : List source.val.NodeId)
    (endpoint : CEndpoint source.val.nodeCount) :
    Option
      (CEndpoint
        ((Internal.retainedNodes source removedNodes).length + sites.length)) :=
  (Internal.batchEndpoint? source removedNodes endpoint).map fun mapped =>
    { node := Fin.castAdd sites.length mapped.node
      port := mapped.port }

private def relationSeverAtom
    {source : CheckedDiagram definitions}
    (sites : List (RelationSeverSite source))
    (removedNodes : List source.val.NodeId)
    (site : Fin sites.length) :
    Fin ((Internal.retainedNodes source removedNodes).length + sites.length) :=
  Fin.natAdd (Internal.retainedNodes source removedNodes).length site

private def relationSeverFormalEndpoints
    {source : CheckedDiagram definitions}
    (sites : List (RelationSeverSite source))
    (removedNodes : List source.val.NodeId)
    (wire : source.val.WireId) :
    List
      (CEndpoint
        ((Internal.retainedNodes source removedNodes).length + sites.length)) :=
  (Data.Finite.allFin sites.length).flatMap fun site =>
    (List.range (sites.get site).formals.length).filterMap fun position =>
      match (sites.get site).formals[position]? with
      | none => none
      | some formal =>
          if formal = wire then
            some
              { node := relationSeverAtom sites removedNodes site
                port := .arg position }
          else
            none

private def relationSeverCandidate
    {definitions : List (List Sig)}
    (source : CheckedDiagram definitions)
    (scope : source.val.RegionId)
    (sites : List (RelationSeverSite source))
    (plan : RelationSeverPlan source scope sites) :
    ConcreteDiagram definitions.length where
  regionCount :=
    (Internal.retainedRegions source (relationRemovedRegions sites)).length
  nodeCount :=
    (Internal.retainedNodes source (relationRemovedNodes sites)).length +
      sites.length
  wireCount :=
    (Internal.retainedWires source (relationRemovedWires sites)).length + 1
  root :=
    Internal.retainedRegionIndex source (relationRemovedRegions sites)
      source.val.root plan.removal.rootRetained
  regions := Internal.batchRegionTable plan.removal
  nodes :=
    Fin.addCases
      (fun node => Internal.batchNodeTable plan.removal node)
      (fun site =>
        .atom
          (Internal.retainedRegionIndex source (relationRemovedRegions sites)
            (sites.get site).region (plan.siteRegionRetained site))
          (relationSeverArgs sites))
  wires :=
    Fin.addCases
      (fun wire =>
        let sourceWire :=
          Internal.sourceRetainedWire source (relationRemovedWires sites) wire
        let data := source.val.wires sourceWire
        { sig := data.sig
          scope :=
            Internal.retainedRegionIndex source (relationRemovedRegions sites)
              data.scope (plan.removal.wireScopeRetained wire)
          endpoints :=
            data.endpoints.filterMap
                (relationSeverEndpoint? sites
                  (relationRemovedNodes sites)) ++
              relationSeverFormalEndpoints sites
                (relationRemovedNodes sites) sourceWire })
      (fun _ =>
        { sig := .rel (relationSeverArgs sites)
          scope :=
            Internal.retainedRegionIndex source (relationRemovedRegions sites)
              scope plan.scopeRetained
          endpoints :=
            (Data.Finite.allFin sites.length).map fun site =>
              { node :=
                  relationSeverAtom sites
                    (relationRemovedNodes sites) site
                port := .head } })

/-- Checked output of one exact batch relation-content abstraction. -/
structure RelationSeverResult
    (source : CheckedDiagram definitions)
    (scope : source.val.RegionId)
    (sites : List (RelationSeverSite source)) : Type where
  private mk ::
  checked : CheckedDiagram definitions
  private plan : RelationSeverPlan source scope sites
  private generated :
    checked.val = relationSeverCandidate source scope sites plan

/--
Replace every supplied exact, disjoint content extent by an atom over one
fresh relation wire.  Copy identity, ambient coherence, scope policy, and
orientation remain rule-owned.
-/
def severRelation
    (source : CheckedDiagram definitions)
    (scope : source.val.RegionId)
    (sites : List (RelationSeverSite source)) :
    Except Error (RelationSeverResult source scope sites) := by
  match prepared : checkRelationSeverPlan source scope sites with
  | .error error =>
      exact .error error
  | .ok plan =>
      let candidate := relationSeverCandidate source scope sites plan
      match accepted :
          ConcreteDiagram.checkWellFormed definitions candidate with
      | .error error =>
          exact .error (.wellFormed error)
      | .ok checked =>
          exact .ok
            (RelationSeverResult.mk checked plan
              (ConcreteDiagram.checkWellFormed_preserves_input accepted))

namespace RelationSeverResult

def regionImage
    (result : RelationSeverResult source scope sites)
    (region : source.val.RegionId)
    (survives :
      region ∈ Internal.retainedRegions source (relationRemovedRegions sites)) :
    result.checked.val.RegionId :=
  Internal.checkedRegion result.generated
    (Internal.retainedRegionIndex source (relationRemovedRegions sites)
      region survives)

def nodeImage
    (result : RelationSeverResult source scope sites)
    (node : source.val.NodeId)
    (survives :
      node ∈ Internal.retainedNodes source (relationRemovedNodes sites)) :
    result.checked.val.NodeId :=
  Internal.checkedNode result.generated
    (Fin.castAdd sites.length
      (Internal.retainedNodeIndex source (relationRemovedNodes sites)
        node survives))

def wireImage
    (result : RelationSeverResult source scope sites)
    (wire : source.val.WireId)
    (survives :
      wire ∈ Internal.retainedWires source (relationRemovedWires sites)) :
    result.checked.val.WireId :=
  Internal.checkedWire result.generated
    (Fin.castAdd 1
      (Internal.retainedWireIndex source (relationRemovedWires sites)
        wire survives))

def atom
    (result : RelationSeverResult source scope sites)
    (site : Fin sites.length) :
    result.checked.val.NodeId :=
  Internal.checkedNode result.generated
    (relationSeverAtom sites (relationRemovedNodes sites) site)

def atoms
    (result : RelationSeverResult source scope sites) :
    List result.checked.val.NodeId :=
  (Data.Finite.allFin sites.length).map result.atom

def relationWire
    (result : RelationSeverResult source scope sites) :
    result.checked.val.WireId :=
  Internal.checkedWire result.generated
    (Fin.natAdd
      (Internal.retainedWires source (relationRemovedWires sites)).length
      (0 : Fin 1))

/-- Retained regions preserve the exact dense batch-removal index. -/
@[simp] theorem regionImage_val
    (result : RelationSeverResult source scope sites)
    (region : source.val.RegionId)
    (survives :
      region ∈ Internal.retainedRegions source (relationRemovedRegions sites)) :
    (result.regionImage region survives).val =
      (Internal.retainedRegionIndex source (relationRemovedRegions sites)
        region survives).val := by
  rfl

/-- Retained nodes occupy the original dense-removal prefix in exact order. -/
@[simp] theorem nodeImage_val
    (result : RelationSeverResult source scope sites)
    (node : source.val.NodeId)
    (survives :
      node ∈ Internal.retainedNodes source (relationRemovedNodes sites)) :
    (result.nodeImage node survives).val =
      (Internal.retainedNodeIndex source (relationRemovedNodes sites)
        node survives).val := by
  rfl

theorem nodeImage_lt_retainedCount
    (result : RelationSeverResult source scope sites)
    (node : source.val.NodeId)
    (survives :
      node ∈ Internal.retainedNodes source (relationRemovedNodes sites)) :
    (result.nodeImage node survives).val <
      (Internal.retainedNodes source (relationRemovedNodes sites)).length :=
  (Internal.retainedNodeIndex source (relationRemovedNodes sites)
    node survives).isLt

/-- Retained wires occupy the original dense-removal prefix in exact order. -/
@[simp] theorem wireImage_val
    (result : RelationSeverResult source scope sites)
    (wire : source.val.WireId)
    (survives :
      wire ∈ Internal.retainedWires source (relationRemovedWires sites)) :
    (result.wireImage wire survives).val =
      (Internal.retainedWireIndex source (relationRemovedWires sites)
        wire survives).val := by
  rfl

/-- Generated relation atoms follow the retained-node prefix in site order. -/
@[simp] theorem atom_val
    (result : RelationSeverResult source scope sites)
    (site : Fin sites.length) :
    (result.atom site).val =
      (Internal.retainedNodes source (relationRemovedNodes sites)).length +
        site.val := by
  rfl

/-- The generated relation wire is the unique final dense wire. -/
@[simp] theorem relationWire_val
    (result : RelationSeverResult source scope sites) :
    result.relationWire.val =
      (Internal.retainedWires source (relationRemovedWires sites)).length := by
  rfl

def retainedEndpoints
    (result : RelationSeverResult source scope sites)
    (wire : source.val.WireId) :
    List (CEndpoint result.checked.val.nodeCount) :=
  ((source.val.wires wire).endpoints.filterMap
      (relationSeverEndpoint? sites (relationRemovedNodes sites))).map
    (Internal.checkedEndpoint result.generated)

def formalEndpoints
    (result : RelationSeverResult source scope sites)
    (wire : source.val.WireId) :
    List (CEndpoint result.checked.val.nodeCount) :=
  (relationSeverFormalEndpoints sites
      (relationRemovedNodes sites) wire).map
    (Internal.checkedEndpoint result.generated)

theorem checked_generated
    (result : RelationSeverResult source scope sites) :
    result.checked.val =
      relationSeverCandidate source scope sites result.plan :=
  result.generated

@[simp] theorem regionCount
    (result : RelationSeverResult source scope sites) :
    result.checked.val.regionCount =
      (Internal.retainedRegions source (relationRemovedRegions sites)).length := by
  simpa [relationSeverCandidate] using
    congrArg ConcreteDiagram.regionCount result.generated

@[simp] theorem nodeCount
    (result : RelationSeverResult source scope sites) :
    result.checked.val.nodeCount =
      (Internal.retainedNodes source (relationRemovedNodes sites)).length +
        sites.length := by
  simpa [relationSeverCandidate] using
    congrArg ConcreteDiagram.nodeCount result.generated

@[simp] theorem wireCount
    (result : RelationSeverResult source scope sites) :
    result.checked.val.wireCount =
      (Internal.retainedWires source (relationRemovedWires sites)).length + 1 := by
  simpa [relationSeverCandidate] using
    congrArg ConcreteDiagram.wireCount result.generated

theorem checkedRegionCount_eq_retainedRegions
    (result : RelationSeverResult source scope sites) :
    result.checked.val.regionCount =
      (Internal.retainedRegions source
        (sites.flatMap RelationSeverSite.removedRegions)).length :=
  result.regionCount

theorem checkedNodeCount_eq_retainedNodes_add_sites
    (result : RelationSeverResult source scope sites) :
    result.checked.val.nodeCount =
      (Internal.retainedNodes source
        (sites.flatMap RelationSeverSite.removedNodes)).length +
          sites.length :=
  result.nodeCount

theorem checkedWireCount_eq_retainedWires_add_one
    (result : RelationSeverResult source scope sites) :
    result.checked.val.wireCount =
      (Internal.retainedWires source
        (sites.flatMap RelationSeverSite.removedWires)).length + 1 :=
  result.wireCount

theorem removedRegions_nodup
    (result : RelationSeverResult source scope sites) :
    (sites.flatMap RelationSeverSite.removedRegions).Nodup :=
  result.plan.removedRegionsNodup

theorem removedNodes_nodup
    (result : RelationSeverResult source scope sites) :
    (sites.flatMap RelationSeverSite.removedNodes).Nodup :=
  result.plan.removedNodesNodup

theorem removedWires_nodup
    (result : RelationSeverResult source scope sites) :
    (sites.flatMap RelationSeverSite.removedWires).Nodup :=
  result.plan.removedWiresNodup

/-- The parent of a retained source region is retained by the same batch. -/
theorem regionParent_survives
    (result : RelationSeverResult source scope sites)
    (region : source.val.RegionId)
    (survives :
      region ∈ Internal.retainedRegions source (relationRemovedRegions sites))
    (parent : source.val.RegionId)
    (data : source.val.regions region = .cut parent) :
    parent ∈
      Internal.retainedRegions source (relationRemovedRegions sites) := by
  have retained := result.plan.removal.parentRetained
    (Internal.retainedRegionIndex source (relationRemovedRegions sites)
      region survives)
  change
    match source.val.regions
        ((Internal.retainedRegions source
          (relationRemovedRegions sites)).get
            (Internal.retainedRegionIndex source
              (relationRemovedRegions sites) region survives)) with
    | .sheet => True
    | .cut parent =>
        parent ∈ Internal.retainedRegions source
          (relationRemovedRegions sites) at retained
  unfold Internal.retainedRegionIndex at retained
  rw [DenseList.get_index, data] at retained
  exact retained

/-- Retained sheet data is copied exactly through the sever's dense map. -/
theorem regionImage_sheet
    (result : RelationSeverResult source scope sites)
    (region : source.val.RegionId)
    (survives :
      region ∈ Internal.retainedRegions source (relationRemovedRegions sites))
    (data : source.val.regions region = .sheet) :
    result.checked.val.regions (result.regionImage region survives) =
      .sheet := by
  unfold regionImage
  apply Internal.checkedRegion_data_transport_sheet
  exact Internal.batchRegionTable_retained_sheet result.plan.removal
    region survives data

/-- Retained cut data and its parent are copied through the sever's dense map. -/
theorem regionImage_cut
    (result : RelationSeverResult source scope sites)
    (region : source.val.RegionId)
    (survives :
      region ∈ Internal.retainedRegions source (relationRemovedRegions sites))
    (parent : source.val.RegionId)
    (data : source.val.regions region = .cut parent) :
    result.checked.val.regions (result.regionImage region survives) =
      .cut (result.regionImage parent
        (result.regionParent_survives region survives parent data)) := by
  unfold regionImage
  apply Internal.checkedRegion_data_transport_cut
  exact Internal.batchRegionTable_retained_cut result.plan.removal
    region survives parent data
      (result.regionParent_survives region survives parent data)

theorem retainedRegions_length_add_removedRegions_length
    (result : RelationSeverResult source scope sites) :
    (Internal.retainedRegions source
        (sites.flatMap RelationSeverSite.removedRegions)).length +
      (sites.flatMap RelationSeverSite.removedRegions).length =
        source.val.regionCount := by
  simpa [Internal.retainedRegions, ConcreteDiagram.regionsList] using
    Data.Finite.filter_not_mem_length_add_removed_length
      (sites.flatMap RelationSeverSite.removedRegions)
      result.removedRegions_nodup

theorem retainedNodes_length_add_removedNodes_length
    (result : RelationSeverResult source scope sites) :
    (Internal.retainedNodes source
        (sites.flatMap RelationSeverSite.removedNodes)).length +
      (sites.flatMap RelationSeverSite.removedNodes).length =
        source.val.nodeCount := by
  simpa [Internal.retainedNodes, ConcreteDiagram.nodesList] using
    Data.Finite.filter_not_mem_length_add_removed_length
      (sites.flatMap RelationSeverSite.removedNodes)
      result.removedNodes_nodup

theorem retainedWires_length_add_removedWires_length
    (result : RelationSeverResult source scope sites) :
    (Internal.retainedWires source
        (sites.flatMap RelationSeverSite.removedWires)).length +
      (sites.flatMap RelationSeverSite.removedWires).length =
        source.val.wireCount := by
  simpa [Internal.retainedWires, ConcreteDiagram.wiresList] using
    Data.Finite.filter_not_mem_length_add_removed_length
      (sites.flatMap RelationSeverSite.removedWires)
      result.removedWires_nodup

/-- Public characterization of the batch-retained source regions. -/
theorem retainedRegion_iff
    (result : RelationSeverResult source scope sites)
    (region : source.val.RegionId) :
    region ∈ Internal.retainedRegions source (relationRemovedRegions sites) ↔
      region ∉ sites.flatMap RelationSeverSite.removedRegions := by
  simp [Internal.retainedRegions, relationRemovedRegions,
    ConcreteDiagram.regionsList, Data.Finite.mem_allFin]

/-- Public characterization of the batch-retained source nodes. -/
theorem retainedNode_iff
    (result : RelationSeverResult source scope sites)
    (node : source.val.NodeId) :
    node ∈ Internal.retainedNodes source (relationRemovedNodes sites) ↔
      node ∉ sites.flatMap RelationSeverSite.removedNodes := by
  simp [Internal.retainedNodes, relationRemovedNodes,
    ConcreteDiagram.nodesList, Data.Finite.mem_allFin]

/-- Public characterization of the batch-retained source wires. -/
theorem retainedWire_iff
    (result : RelationSeverResult source scope sites)
    (wire : source.val.WireId) :
    wire ∈ Internal.retainedWires source (relationRemovedWires sites) ↔
      wire ∉ sites.flatMap RelationSeverSite.removedWires := by
  simp [Internal.retainedWires, relationRemovedWires,
    ConcreteDiagram.wiresList, Data.Finite.mem_allFin]

theorem site_formal_signatures
    (result : RelationSeverResult source scope sites)
    (site : Fin sites.length) :
    (sites.get site).formals.map
        (fun wire => (source.val.wires wire).sig) =
      relationSeverArgs sites :=
  result.plan.signatureExact site

@[simp] theorem relationWire_signature
    (result : RelationSeverResult source scope sites) :
    (result.checked.val.wires result.relationWire).sig =
      .rel (relationSeverArgs sites) := by
  unfold relationWire
  rw [Internal.checkedWire_signature_transport]
  simp only [relationSeverCandidate, Fin.addCases_right]

@[simp] theorem relationWire_scope
    (result : RelationSeverResult source scope sites) :
    (result.checked.val.wires result.relationWire).scope =
      result.regionImage scope result.plan.scopeRetained := by
  unfold relationWire regionImage
  rw [Internal.checkedWire_scope_transport]
  simp only [relationSeverCandidate, Fin.addCases_right]

theorem atom_generated
    (result : RelationSeverResult source scope sites)
    (site : Fin sites.length) :
    result.checked.val.nodes (result.atom site) =
      .atom
        (result.regionImage (sites.get site).region
          (result.plan.siteRegionRetained site))
        (relationSeverArgs sites) := by
  unfold atom regionImage
  rw [Internal.checkedNode_data_transport]
  simp only [relationSeverAtom, relationSeverCandidate,
    Fin.addCases_right, Internal.checkedNodeData]

theorem relationWire_endpoints
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {scope : source.val.RegionId}
    {sites : List (RelationSeverSite source)}
    (result : RelationSeverResult source scope sites) :
    (result.checked.val.wires result.relationWire).endpoints =
      (Data.Finite.allFin sites.length).map
        (fun (site : Fin sites.length) =>
          ({ node := result.atom site
             port := .head } :
            CEndpoint result.checked.val.nodeCount)) := by
  unfold relationWire atom relationSeverAtom
  rw [Internal.checkedWire_endpoints_transport]
  simp only [relationSeverCandidate, Fin.addCases_right]
  simp [List.map_map, Internal.checkedEndpoint, relationSeverAtom]

/--
The generated applications occupy the exact dense suffix and therefore occur
in site order when a relation join scans source-node storage.  This is the
batch sever/join alignment theorem; no identifier search is involved.
-/
theorem relationApplications_storage_order
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {scope : source.val.RegionId}
    {sites : List (RelationSeverSite source)}
    (result : RelationSeverResult source scope sites) :
    result.checked.val.nodesList.filter (fun node =>
        decide
          ((⟨node, .head⟩ : CEndpoint result.checked.val.nodeCount) ∈
            (result.checked.val.wires result.relationWire).endpoints)) =
      result.atoms := by
  let retainedCount :=
    (Internal.retainedNodes source (relationRemovedNodes sites)).length
  have selectedExact :
      ∀ node : result.checked.val.NodeId,
        decide
            ((⟨node, .head⟩ : CEndpoint result.checked.val.nodeCount) ∈
              (result.checked.val.wires result.relationWire).endpoints) =
          decide (retainedCount ≤ node.val) := by
    intro node
    apply decide_eq_decide.mpr
    rw [result.relationWire_endpoints]
    constructor
    · intro member
      obtain ⟨site, _, endpointExact⟩ := List.mem_map.mp member
      have nodeExact : result.atom site = node := by
        simpa using congrArg CEndpoint.node endpointExact
      rw [← nodeExact, result.atom_val]
      simp [retainedCount]
    · intro lower
      have upper : node.val < retainedCount + sites.length := by
        rw [← result.nodeCount]
        exact node.isLt
      let site : Fin sites.length :=
        ⟨node.val - retainedCount, by omega⟩
      apply List.mem_map.mpr
      refine ⟨site, Data.Finite.mem_allFin site, ?_⟩
      have nodeExact : result.atom site = node := by
        apply Fin.ext
        rw [result.atom_val]
        simp [site]
        omega
      simpa using nodeExact
  rw [ConcreteDiagram.nodesList]
  rw [Data.Finite.filter_allFin_suffix_of_eq
    result.checked.val.nodeCount retainedCount sites.length result.nodeCount _
    selectedExact]
  unfold atoms retainedCount
  apply List.map_congr_left
  intro site _
  apply Fin.ext
  rw [result.atom_val]
  rfl

@[simp] theorem wireImage_signature
    (result : RelationSeverResult source scope sites)
    (wire : source.val.WireId)
    (survives :
      wire ∈ Internal.retainedWires source (relationRemovedWires sites)) :
    (result.checked.val.wires (result.wireImage wire survives)).sig =
      (source.val.wires wire).sig := by
  unfold wireImage
  rw [Internal.checkedWire_signature_transport]
  simp only [relationSeverCandidate, Fin.addCases_left]
  unfold Internal.sourceRetainedWire Internal.retainedWireIndex
  rw [DenseList.get_index]

theorem wireScope_survives
    (result : RelationSeverResult source scope sites)
    (wire : source.val.WireId)
    (survives :
      wire ∈ Internal.retainedWires source (relationRemovedWires sites)) :
    (source.val.wires wire).scope ∈
      Internal.retainedRegions source (relationRemovedRegions sites) := by
  have retained :=
    result.plan.removal.wireScopeRetained
      (Internal.retainedWireIndex source (relationRemovedWires sites)
        wire survives)
  unfold Internal.retainedWireIndex at retained
  change
    (source.val.wires
      ((Internal.retainedWires source (relationRemovedWires sites)).get
        (DenseList.index
          (Internal.retainedWires source (relationRemovedWires sites))
          wire survives))).scope ∈
      Internal.retainedRegions source (relationRemovedRegions sites) at retained
  rw [DenseList.get_index] at retained
  exact retained

@[simp] theorem wireImage_scope
    (result : RelationSeverResult source scope sites)
    (wire : source.val.WireId)
    (survives :
      wire ∈ Internal.retainedWires source (relationRemovedWires sites)) :
    (result.checked.val.wires (result.wireImage wire survives)).scope =
      result.regionImage (source.val.wires wire).scope
        (result.wireScope_survives wire survives) := by
  unfold wireImage regionImage
  rw [Internal.checkedWire_scope_transport]
  simp only [relationSeverCandidate, Fin.addCases_left]
  simp only [Internal.sourceRetainedWire, Internal.retainedWireIndex,
    DenseList.get_index]

theorem wireImage_endpoints
    (result : RelationSeverResult source scope sites)
    (wire : source.val.WireId)
    (survives :
      wire ∈ Internal.retainedWires source (relationRemovedWires sites)) :
    (result.checked.val.wires (result.wireImage wire survives)).endpoints =
      result.retainedEndpoints wire ++ result.formalEndpoints wire := by
  unfold wireImage retainedEndpoints formalEndpoints
  rw [Internal.checkedWire_endpoints_transport]
  simp only [relationSeverCandidate, Fin.addCases_left]
  unfold Internal.sourceRetainedWire Internal.retainedWireIndex
  rw [DenseList.get_index, List.map_append]

/-- Every ordered site formal survives the batch abstraction. -/
theorem siteFormal_survives
    (result : RelationSeverResult source scope sites)
    (site : Fin sites.length)
    (position : Fin (sites.get site).formals.length) :
    (sites.get site).formals.get position ∈
      Internal.retainedWires source (relationRemovedWires sites) :=
  result.plan.formalRetained site position

/-- Ordered retained-wire images of one sever site's formal vector. -/
def siteFormalImages
    (result : RelationSeverResult source scope sites)
    (site : Fin sites.length) :
    List result.checked.val.WireId :=
  List.ofFn fun position : Fin (sites.get site).formals.length =>
    result.wireImage ((sites.get site).formals.get position)
      (result.siteFormal_survives site position)

@[simp] theorem siteFormalImages_length
    (result : RelationSeverResult source scope sites)
    (site : Fin sites.length) :
    (result.siteFormalImages site).length =
      (sites.get site).formals.length := by
  simp [siteFormalImages]

@[simp] theorem siteFormalImages_get
    (result : RelationSeverResult source scope sites)
    (site : Fin sites.length)
    (position : Fin (result.siteFormalImages site).length) :
    (result.siteFormalImages site).get position =
      result.wireImage
        ((sites.get site).formals.get
          (Fin.cast (result.siteFormalImages_length site) position))
        (result.siteFormal_survives site
          (Fin.cast (result.siteFormalImages_length site) position)) := by
  simp [siteFormalImages]

/-- The generated atom argument is incident to the exact retained image of
its ordered site formal. -/
theorem atomArgument_incident
    (result : RelationSeverResult source scope sites)
    (site : Fin sites.length)
    (position : Fin (sites.get site).formals.length) :
    ({ node := result.atom site, port := .arg position.val } :
        CEndpoint result.checked.val.nodeCount) ∈
      (result.checked.val.wires
        (result.wireImage ((sites.get site).formals.get position)
          (result.siteFormal_survives site position))).endpoints := by
  rw [result.wireImage_endpoints]
  apply List.mem_append_right
  unfold formalEndpoints
  rw [List.mem_map]
  let raw :
      CEndpoint
        ((Internal.retainedNodes source (relationRemovedNodes sites)).length +
          sites.length) :=
    { node := relationSeverAtom sites (relationRemovedNodes sites) site
      port := .arg position.val }
  refine ⟨raw, ?_, ?_⟩
  · unfold relationSeverFormalEndpoints
    apply List.mem_flatMap.mpr
    refine ⟨site, Data.Finite.mem_allFin site, ?_⟩
    change raw ∈ _
    apply List.mem_filterMap.mpr
    refine ⟨position.val, by simp [position.isLt], ?_⟩
    simp [List.getElem?_eq_getElem, position.isLt, raw]
  · rfl

end RelationSeverResult

end ConcreteWireQuantifier

end VisualProof
