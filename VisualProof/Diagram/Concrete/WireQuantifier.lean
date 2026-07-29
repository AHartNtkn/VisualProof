import VisualProof.Diagram.Concrete.Subgraph.Splice

namespace VisualProof

namespace ConcreteWireQuantifier

/-- Concrete construction failures owned below the rule-policy boundary. -/
inductive Error
  | expectedIota (wire : Nat)
  | expectedRelation (wire : Nat)
  | sameWire
  | invalidEndpointPartition
  | emptyRelationSites
  | overlappingRemoval
  | invalidRemoval
  | removedRoot
  | removedScope
  | removedSite
  | removedFormal (wire : Nat)
  | relationSignatureMismatch
  | boundaryArityMismatch
  | boundarySignatureMismatch (position : Nat)
  | dyingWireParameter
  | nonAppliedEndpoint (node : Nat) (port : CPort)
  | invalidApplication (node : Nat)
  | invalidAttachment
  | wellFormed (error : WFError)
  deriving Repr, DecidableEq

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

private def retainedRegions
    (source : CheckedDiagram definitions)
    (removed : List source.val.RegionId) :
    List source.val.RegionId :=
  source.val.regionsList.filter fun region =>
    decide (region ∉ removed)

private def retainedNodes
    (source : CheckedDiagram definitions)
    (removed : List source.val.NodeId) :
    List source.val.NodeId :=
  source.val.nodesList.filter fun node =>
    decide (node ∉ removed)

private def retainedWires
    (source : CheckedDiagram definitions)
    (removed : List source.val.WireId) :
    List source.val.WireId :=
  source.val.wiresList.filter fun wire =>
    decide (wire ∉ removed)

/--
The complete structural evidence needed to densely remove a batch without a
repair fallback.  Only the executable checker below can construct this plan.
-/
private structure BatchRemovalPlan
    (source : CheckedDiagram definitions)
    (removedRegions : List source.val.RegionId)
    (removedNodes : List source.val.NodeId)
    (removedWires : List source.val.WireId) : Type where
  rootRetained :
    source.val.root ∈ retainedRegions source removedRegions
  parentRetained :
    ∀ target : Fin (retainedRegions source removedRegions).length,
      match source.val.regions
          ((retainedRegions source removedRegions).get target) with
      | .sheet => True
      | .cut parent =>
          parent ∈ retainedRegions source removedRegions
  nodeRegionRetained :
    ∀ target : Fin (retainedNodes source removedNodes).length,
      (source.val.nodes
          ((retainedNodes source removedNodes).get target)).region ∈
        retainedRegions source removedRegions
  wireScopeRetained :
    ∀ target : Fin (retainedWires source removedWires).length,
      (source.val.wires
          ((retainedWires source removedWires).get target)).scope ∈
        retainedRegions source removedRegions

private def checkBatchRemovalPlan?
    (source : CheckedDiagram definitions)
    (removedRegions : List source.val.RegionId)
    (removedNodes : List source.val.NodeId)
    (removedWires : List source.val.WireId) :
    Option
      (BatchRemovalPlan source removedRegions removedNodes removedWires) := by
  if rootRetained :
      source.val.root ∈ retainedRegions source removedRegions then
    if parentRetained :
        (retainedRegions source removedRegions).all (fun region =>
          match source.val.regions region with
          | .sheet => true
          | .cut parent =>
              decide (parent ∈ retainedRegions source removedRegions)) =
            true then
      if nodeRegionRetained :
          (retainedNodes source removedNodes).all (fun node =>
            decide (
              (source.val.nodes node).region ∈
                retainedRegions source removedRegions)) = true then
        if wireScopeRetained :
            (retainedWires source removedWires).all (fun wire =>
              decide (
                (source.val.wires wire).scope ∈
                  retainedRegions source removedRegions)) = true then
          exact some
            { rootRetained := rootRetained
              parentRetained := by
                intro target
                have accepted :=
                  (List.all_eq_true.mp parentRetained)
                    ((retainedRegions source removedRegions).get target)
                    (List.get_mem _ target)
                cases regionData :
                    source.val.regions
                      ((retainedRegions source removedRegions).get target) with
                | sheet => trivial
                | cut parent =>
                    rw [regionData] at accepted
                    exact of_decide_eq_true accepted
              nodeRegionRetained := by
                intro target
                exact of_decide_eq_true
                  ((List.all_eq_true.mp nodeRegionRetained)
                    ((retainedNodes source removedNodes).get target)
                    (List.get_mem _ target))
              wireScopeRetained := by
                intro target
                exact of_decide_eq_true
                  ((List.all_eq_true.mp wireScopeRetained)
                    ((retainedWires source removedWires).get target)
                    (List.get_mem _ target)) }
        else
          exact none
      else
        exact none
    else
      exact none
  else
    exact none

private def retainedRegionIndex
    (source : CheckedDiagram definitions)
    (removed : List source.val.RegionId)
    (region : source.val.RegionId)
    (member : region ∈ retainedRegions source removed) :
    Fin (retainedRegions source removed).length :=
  DenseList.index (retainedRegions source removed) region member

private def retainedNodeIndex
    (source : CheckedDiagram definitions)
    (removed : List source.val.NodeId)
    (node : source.val.NodeId)
    (member : node ∈ retainedNodes source removed) :
    Fin (retainedNodes source removed).length :=
  DenseList.index (retainedNodes source removed) node member

private def retainedWireIndex
    (source : CheckedDiagram definitions)
    (removed : List source.val.WireId)
    (wire : source.val.WireId)
    (member : wire ∈ retainedWires source removed) :
    Fin (retainedWires source removed).length :=
  DenseList.index (retainedWires source removed) wire member

private def sourceRetainedRegion
    (source : CheckedDiagram definitions)
    (removed : List source.val.RegionId)
    (region : Fin (retainedRegions source removed).length) :
    source.val.RegionId :=
  (retainedRegions source removed).get region

private def sourceRetainedNode
    (source : CheckedDiagram definitions)
    (removed : List source.val.NodeId)
    (node : Fin (retainedNodes source removed).length) :
    source.val.NodeId :=
  (retainedNodes source removed).get node

private def sourceRetainedWire
    (source : CheckedDiagram definitions)
    (removed : List source.val.WireId)
    (wire : Fin (retainedWires source removed).length) :
    source.val.WireId :=
  (retainedWires source removed).get wire

private theorem batchParentRetained
    {source : CheckedDiagram definitions}
    {removedRegions : List source.val.RegionId}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan :
      BatchRemovalPlan source removedRegions removedNodes removedWires)
    (region : Fin (retainedRegions source removedRegions).length)
    (parent : source.val.RegionId)
    (regionData :
      source.val.regions
          (sourceRetainedRegion source removedRegions region) =
        .cut parent) :
    parent ∈ retainedRegions source removedRegions := by
  have retained := plan.parentRetained region
  have same :
      source.val.regions
          ((retainedRegions source removedRegions).get region) =
        .cut parent := by
    simpa [sourceRetainedRegion] using regionData
  rw [same] at retained
  exact retained

private def batchRegionTable
    {removedRegions : List source.val.RegionId}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan :
      BatchRemovalPlan source removedRegions removedNodes removedWires)
    (region : Fin (retainedRegions source removedRegions).length) :
    CRegion (retainedRegions source removedRegions).length :=
  match regionData : source.val.regions
      (sourceRetainedRegion source removedRegions region) with
  | .sheet => .sheet
  | .cut parent =>
      .cut
        (retainedRegionIndex source removedRegions parent
          (batchParentRetained plan region parent regionData))

private def batchNodeTable
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {removedRegions : List source.val.RegionId}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan :
      BatchRemovalPlan source removedRegions removedNodes removedWires)
    (node : Fin (retainedNodes source removedNodes).length) :
    CNode (retainedRegions source removedRegions).length definitions.length :=
  let sourceNode := sourceRetainedNode source removedNodes node
  let region :=
    retainedRegionIndex source removedRegions
      (source.val.nodes sourceNode).region
      (plan.nodeRegionRetained node)
  match source.val.nodes sourceNode with
  | .atom _ args => .atom region args
  | .ref _ definition args => .ref region definition args
  | .identity _ sig arity => .identity region sig arity

private def batchEndpoint?
    (source : CheckedDiagram definitions)
    (removedNodes : List source.val.NodeId)
    (endpoint : CEndpoint source.val.nodeCount) :
    Option (CEndpoint (retainedNodes source removedNodes).length) :=
  if retained : endpoint.node ∈ retainedNodes source removedNodes then
    some
      { node :=
          retainedNodeIndex source removedNodes endpoint.node retained
        port := endpoint.port }
  else
    none

private def batchWireTable
    {removedRegions : List source.val.RegionId}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan :
      BatchRemovalPlan source removedRegions removedNodes removedWires)
    (wire : Fin (retainedWires source removedWires).length) :
    CWire
      (retainedRegions source removedRegions).length
      (retainedNodes source removedNodes).length :=
  let sourceWire := sourceRetainedWire source removedWires wire
  let data := source.val.wires sourceWire
  { sig := data.sig
    scope :=
      retainedRegionIndex source removedRegions data.scope
        (plan.wireScopeRetained wire)
    endpoints := data.endpoints.filterMap
      (batchEndpoint? source removedNodes) }

private def batchRemovalCandidate
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {removedRegions : List source.val.RegionId}
    {removedNodes : List source.val.NodeId}
    {removedWires : List source.val.WireId}
    (plan :
      BatchRemovalPlan source removedRegions removedNodes removedWires) :
    ConcreteDiagram definitions.length where
  regionCount := (retainedRegions source removedRegions).length
  nodeCount := (retainedNodes source removedNodes).length
  wireCount := (retainedWires source removedWires).length
  root :=
    retainedRegionIndex source removedRegions source.val.root
      plan.rootRetained
  regions := batchRegionTable plan
  nodes := batchNodeTable plan
  wires := batchWireTable plan

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
    BatchRemovalPlan source
      (relationRemovedRegions sites)
      (relationRemovedNodes sites)
      (relationRemovedWires sites)
  scopeRetained :
    scope ∈ retainedRegions source (relationRemovedRegions sites)
  siteRegionRetained :
    ∀ site : Fin sites.length,
      (sites.get site).region ∈
        retainedRegions source (relationRemovedRegions sites)
  formalRetained :
    ∀ site : Fin sites.length,
      ∀ position : Fin (sites.get site).formals.length,
        (sites.get site).formals.get position ∈
          retainedWires source (relationRemovedWires sites)
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
        scope ∈ retainedRegions source removedRegions then
      if sitesRetained :
          sites.all (fun site =>
            decide (
              site.region ∈ retainedRegions source removedRegions)) =
            true then
        if formalsRetained :
            sites.all (fun site =>
              site.formals.all (fun wire =>
                decide (
                  wire ∈ retainedWires source removedWires))) = true then
          if signaturesExact :
              sites.all (fun site =>
                decide (
                  site.formals.map
                      (fun wire => (source.val.wires wire).sig) =
                    relationSeverArgs sites)) = true then
            match removal :
                checkBatchRemovalPlan? source
                  removedRegions removedNodes removedWires with
            | none =>
                exact .error .invalidRemoval
            | some removalPlan =>
                exact .ok
                  { removal := by
                      simpa [removedRegions, removedNodes, removedWires]
                        using removalPlan
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
              decide (wire ∉ retainedWires source removedWires) with
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
        ((retainedNodes source removedNodes).length + sites.length)) :=
  (batchEndpoint? source removedNodes endpoint).map fun mapped =>
    { node := Fin.castAdd sites.length mapped.node
      port := mapped.port }

private def relationSeverAtom
    {source : CheckedDiagram definitions}
    (sites : List (RelationSeverSite source))
    (removedNodes : List source.val.NodeId)
    (site : Fin sites.length) :
    Fin ((retainedNodes source removedNodes).length + sites.length) :=
  Fin.natAdd (retainedNodes source removedNodes).length site

private def relationSeverFormalEndpoints
    {source : CheckedDiagram definitions}
    (sites : List (RelationSeverSite source))
    (removedNodes : List source.val.NodeId)
    (wire : source.val.WireId) :
    List
      (CEndpoint
        ((retainedNodes source removedNodes).length + sites.length)) :=
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
    (retainedRegions source (relationRemovedRegions sites)).length
  nodeCount :=
    (retainedNodes source (relationRemovedNodes sites)).length +
      sites.length
  wireCount :=
    (retainedWires source (relationRemovedWires sites)).length + 1
  root :=
    retainedRegionIndex source (relationRemovedRegions sites)
      source.val.root plan.removal.rootRetained
  regions := batchRegionTable plan.removal
  nodes :=
    Fin.addCases
      (fun node => batchNodeTable plan.removal node)
      (fun site =>
        .atom
          (retainedRegionIndex source (relationRemovedRegions sites)
            (sites.get site).region (plan.siteRegionRetained site))
          (relationSeverArgs sites))
  wires :=
    Fin.addCases
      (fun wire =>
        let sourceWire :=
          sourceRetainedWire source (relationRemovedWires sites) wire
        let data := source.val.wires sourceWire
        { sig := data.sig
          scope :=
            retainedRegionIndex source (relationRemovedRegions sites)
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
            retainedRegionIndex source (relationRemovedRegions sites)
              scope plan.scopeRetained
          endpoints :=
            (Data.Finite.allFin sites.length).map fun site =>
              { node :=
                  relationSeverAtom sites
                    (relationRemovedNodes sites) site
                port := .head } })

private def checkedRegion
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (region : candidate.RegionId) :
    checked.val.RegionId :=
  Fin.cast
    (congrArg ConcreteDiagram.regionCount generated).symm region

private def checkedNode
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (node : candidate.NodeId) :
    checked.val.NodeId :=
  Fin.cast
    (congrArg ConcreteDiagram.nodeCount generated).symm node

private def checkedWire
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (wire : candidate.WireId) :
    checked.val.WireId :=
  Fin.cast
    (congrArg ConcreteDiagram.wireCount generated).symm wire

private theorem checkedWire_signature_transport
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (wire : candidate.WireId) :
    (checked.val.wires (checkedWire generated wire)).sig =
      (candidate.wires wire).sig := by
  subst candidate
  rfl

private def checkedEndpoint
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (endpoint : CEndpoint candidate.nodeCount) :
    CEndpoint checked.val.nodeCount :=
  { node := checkedNode generated endpoint.node
    port := endpoint.port }

private theorem checkedWire_scope_transport
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (wire : candidate.WireId) :
    (checked.val.wires (checkedWire generated wire)).scope =
      checkedRegion generated (candidate.wires wire).scope := by
  subst candidate
  rfl

private theorem checkedWire_endpoints_transport
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (wire : candidate.WireId) :
    (checked.val.wires (checkedWire generated wire)).endpoints =
      (candidate.wires wire).endpoints.map
        (checkedEndpoint generated) := by
  cases generated
  unfold checkedWire checkedEndpoint checkedNode
  simp

private def checkedNodeData
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate) :
    CNode candidate.regionCount definitions.length →
      CNode checked.val.regionCount definitions.length
  | .atom region args =>
      .atom (checkedRegion generated region) args
  | .ref region definition args =>
      .ref (checkedRegion generated region) definition args
  | .identity region sig arity =>
      .identity (checkedRegion generated region) sig arity

private def checkedRegionData
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate) :
    CRegion candidate.regionCount → CRegion checked.val.regionCount
  | .sheet => .sheet
  | .cut parent => .cut (checkedRegion generated parent)

private theorem checkedRoot_transport
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate) :
    checked.val.root = checkedRegion generated candidate.root := by
  cases generated
  rfl

private theorem checkedRegion_data_transport
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (region : candidate.RegionId) :
    checked.val.regions (checkedRegion generated region) =
      checkedRegionData generated (candidate.regions region) := by
  cases generated
  cases data : checked.val.regions region <;>
    simp [checkedRegion, checkedRegionData, data]

private theorem checkedNode_data_transport
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate)
    (node : candidate.NodeId) :
    checked.val.nodes (checkedNode generated node) =
      checkedNodeData generated (candidate.nodes node) := by
  cases generated
  cases data : checked.val.nodes node <;>
    simp [checkedNode, checkedNodeData, checkedRegion, data]

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
      region ∈ retainedRegions source (relationRemovedRegions sites)) :
    result.checked.val.RegionId :=
  checkedRegion result.generated
    (retainedRegionIndex source (relationRemovedRegions sites)
      region survives)

def nodeImage
    (result : RelationSeverResult source scope sites)
    (node : source.val.NodeId)
    (survives :
      node ∈ retainedNodes source (relationRemovedNodes sites)) :
    result.checked.val.NodeId :=
  checkedNode result.generated
    (Fin.castAdd sites.length
      (retainedNodeIndex source (relationRemovedNodes sites)
        node survives))

def wireImage
    (result : RelationSeverResult source scope sites)
    (wire : source.val.WireId)
    (survives :
      wire ∈ retainedWires source (relationRemovedWires sites)) :
    result.checked.val.WireId :=
  checkedWire result.generated
    (Fin.castAdd 1
      (retainedWireIndex source (relationRemovedWires sites)
        wire survives))

def atom
    (result : RelationSeverResult source scope sites)
    (site : Fin sites.length) :
    result.checked.val.NodeId :=
  checkedNode result.generated
    (relationSeverAtom sites (relationRemovedNodes sites) site)

def atoms
    (result : RelationSeverResult source scope sites) :
    List result.checked.val.NodeId :=
  (Data.Finite.allFin sites.length).map result.atom

def relationWire
    (result : RelationSeverResult source scope sites) :
    result.checked.val.WireId :=
  checkedWire result.generated
    (Fin.natAdd
      (retainedWires source (relationRemovedWires sites)).length
      (0 : Fin 1))

def retainedEndpoints
    (result : RelationSeverResult source scope sites)
    (wire : source.val.WireId) :
    List (CEndpoint result.checked.val.nodeCount) :=
  ((source.val.wires wire).endpoints.filterMap
      (relationSeverEndpoint? sites (relationRemovedNodes sites))).map
    (checkedEndpoint result.generated)

def formalEndpoints
    (result : RelationSeverResult source scope sites)
    (wire : source.val.WireId) :
    List (CEndpoint result.checked.val.nodeCount) :=
  (relationSeverFormalEndpoints sites
      (relationRemovedNodes sites) wire).map
    (checkedEndpoint result.generated)

theorem checked_generated
    (result : RelationSeverResult source scope sites) :
    result.checked.val =
      relationSeverCandidate source scope sites result.plan :=
  result.generated

@[simp] theorem regionCount
    (result : RelationSeverResult source scope sites) :
    result.checked.val.regionCount =
      (retainedRegions source (relationRemovedRegions sites)).length := by
  simpa [relationSeverCandidate] using
    congrArg ConcreteDiagram.regionCount result.generated

@[simp] theorem nodeCount
    (result : RelationSeverResult source scope sites) :
    result.checked.val.nodeCount =
      (retainedNodes source (relationRemovedNodes sites)).length +
        sites.length := by
  simpa [relationSeverCandidate] using
    congrArg ConcreteDiagram.nodeCount result.generated

@[simp] theorem wireCount
    (result : RelationSeverResult source scope sites) :
    result.checked.val.wireCount =
      (retainedWires source (relationRemovedWires sites)).length + 1 := by
  simpa [relationSeverCandidate] using
    congrArg ConcreteDiagram.wireCount result.generated

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
  rw [checkedWire_signature_transport]
  simp only [relationSeverCandidate, Fin.addCases_right]

@[simp] theorem relationWire_scope
    (result : RelationSeverResult source scope sites) :
    (result.checked.val.wires result.relationWire).scope =
      result.regionImage scope result.plan.scopeRetained := by
  unfold relationWire regionImage
  rw [checkedWire_scope_transport]
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
  rw [checkedNode_data_transport]
  simp only [relationSeverAtom, relationSeverCandidate,
    Fin.addCases_right, checkedNodeData]

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
  rw [checkedWire_endpoints_transport]
  simp only [relationSeverCandidate, Fin.addCases_right]
  simp [List.map_map, checkedEndpoint, relationSeverAtom]

@[simp] theorem wireImage_signature
    (result : RelationSeverResult source scope sites)
    (wire : source.val.WireId)
    (survives :
      wire ∈ retainedWires source (relationRemovedWires sites)) :
    (result.checked.val.wires (result.wireImage wire survives)).sig =
      (source.val.wires wire).sig := by
  unfold wireImage
  rw [checkedWire_signature_transport]
  simp only [relationSeverCandidate, Fin.addCases_left]
  unfold sourceRetainedWire retainedWireIndex
  rw [DenseList.get_index]

theorem wireScope_survives
    (result : RelationSeverResult source scope sites)
    (wire : source.val.WireId)
    (survives :
      wire ∈ retainedWires source (relationRemovedWires sites)) :
    (source.val.wires wire).scope ∈
      retainedRegions source (relationRemovedRegions sites) := by
  have retained :=
    result.plan.removal.wireScopeRetained
      (retainedWireIndex source (relationRemovedWires sites)
        wire survives)
  unfold retainedWireIndex at retained
  change
    (source.val.wires
      ((retainedWires source (relationRemovedWires sites)).get
        (DenseList.index
          (retainedWires source (relationRemovedWires sites))
          wire survives))).scope ∈
      retainedRegions source (relationRemovedRegions sites) at retained
  rw [DenseList.get_index] at retained
  exact retained

@[simp] theorem wireImage_scope
    (result : RelationSeverResult source scope sites)
    (wire : source.val.WireId)
    (survives :
      wire ∈ retainedWires source (relationRemovedWires sites)) :
    (result.checked.val.wires (result.wireImage wire survives)).scope =
      result.regionImage (source.val.wires wire).scope
        (result.wireScope_survives wire survives) := by
  unfold wireImage regionImage
  rw [checkedWire_scope_transport]
  simp only [relationSeverCandidate, Fin.addCases_left]
  simp only [sourceRetainedWire, retainedWireIndex,
    DenseList.get_index]

theorem wireImage_endpoints
    (result : RelationSeverResult source scope sites)
    (wire : source.val.WireId)
    (survives :
      wire ∈ retainedWires source (relationRemovedWires sites)) :
    (result.checked.val.wires (result.wireImage wire survives)).endpoints =
      result.retainedEndpoints wire ++ result.formalEndpoints wire := by
  unfold wireImage retainedEndpoints formalEndpoints
  rw [checkedWire_endpoints_transport]
  simp only [relationSeverCandidate, Fin.addCases_left]
  unfold sourceRetainedWire retainedWireIndex
  rw [DenseList.get_index, List.map_append]

end RelationSeverResult

private structure RelationJoinApplication
    (source : CheckedDiagram definitions) where
  node : source.val.NodeId
  region : source.val.RegionId
  arguments : List source.val.WireId

def relationArgumentWires?
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId) :
    List Sig → Nat → Option (List source.val.WireId)
  | [], _ => some []
  | expected :: rest, position => do
      let wire ← source.val.endpointOwner? ⟨node, .arg position⟩
      if (source.val.wires wire).sig = expected then
        let tail ← relationArgumentWires? source node rest (position + 1)
        pure (wire :: tail)
      else
        none

private def relationEndpointIsApplied
    (source : CheckedDiagram definitions)
    (args : List Sig)
    (endpoint : CEndpoint source.val.nodeCount) : Bool :=
  match endpoint.port, source.val.nodes endpoint.node with
  | .head, .atom _ nodeArgs => decide (nodeArgs = args)
  | _, _ => false

private def relationApplicationNodes
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :
    List source.val.NodeId :=
  source.val.nodesList.filter fun node =>
    decide (
      (⟨node, .head⟩ : CEndpoint source.val.nodeCount) ∈
        (source.val.wires wire).endpoints)

private def relationJoinApplicationAt?
    (source : CheckedDiagram definitions)
    (args : List Sig)
    (node : source.val.NodeId) :
    Option (RelationJoinApplication source) := do
  match source.val.nodes node with
  | .atom region nodeArgs =>
      if nodeArgs = args then
        let arguments ← relationArgumentWires? source node args 0
        pure { node := node, region := region, arguments := arguments }
      else
        none
  | _ => none

private def relationJoinApplications?
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (args : List Sig) :
    Option (List (RelationJoinApplication source)) :=
  (relationApplicationNodes source wire).mapM
    (relationJoinApplicationAt? source args)

private def openBoundarySigs
    (content : CheckedOpenDiagram definitions) :
    List Sig :=
  content.val.boundary.map fun wire =>
    (content.val.diagram.wires wire).sig

private def parameterSigs
    (source : CheckedDiagram definitions)
    (parameters : List source.val.WireId) :
    List Sig :=
  parameters.map fun wire => (source.val.wires wire).sig

private structure RelationJoinPlan
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId) : Type where
  args : List Sig
  relationSignature : (source.val.wires wire).sig = .rel args
  endpointsApplied :
    (source.val.wires wire).endpoints.all
        (relationEndpointIsApplied source args) = true
  applications : List (RelationJoinApplication source)
  boundaryExact :
    openBoundarySigs content = args ++ parameterSigs source parameters
  parametersSurvive :
    ∀ position : Fin parameters.length,
      parameters.get position ≠ wire

private def firstBoundaryMismatch
    (actual expected : List Sig) : Nat :=
  ((List.range (max actual.length expected.length)).find? fun position =>
    actual[position]? != expected[position]?).getD 0

private def checkRelationJoinPlan
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId) :
    Except Error (RelationJoinPlan source wire content parameters) := by
  match relationData : (source.val.wires wire).sig with
  | .iota =>
      exact .error (.expectedRelation wire.val)
  | .rel args =>
      if parametersSurvive :
          parameters.all fun parameter => decide (parameter ≠ wire) then
        let expected := args ++ parameterSigs source parameters
        if arity : (openBoundarySigs content).length = expected.length then
          if boundaryExact : openBoundarySigs content = expected then
            if endpointsApplied :
                (source.val.wires wire).endpoints.all
                    (relationEndpointIsApplied source args) = true then
              match applicationsAccepted :
                  relationJoinApplications? source wire args with
              | none =>
                  exact .error (.invalidApplication 0)
              | some applications =>
                  exact .ok
                    { args := args
                      relationSignature := relationData
                      endpointsApplied := endpointsApplied
                      applications := applications
                      boundaryExact := boundaryExact
                      parametersSurvive := by
                        intro position
                        exact of_decide_eq_true
                          ((List.all_eq_true.mp parametersSurvive)
                            (parameters.get position)
                            (List.get_mem _ position)) }
            else
              match (source.val.wires wire).endpoints.find? fun endpoint =>
                  !relationEndpointIsApplied source args endpoint with
              | some endpoint =>
                  exact .error
                    (.nonAppliedEndpoint endpoint.node.val endpoint.port)
              | none =>
                  exact .error .invalidRemoval
          else
            exact .error
              (.boundarySignatureMismatch
                (firstBoundaryMismatch
                  (openBoundarySigs content) expected))
        else
          exact .error .boundaryArityMismatch
      else
        exact .error .dyingWireParameter

structure RelationJoinStep
    (source : CheckedDiagram definitions)
    (dying : source.val.WireId)
    (content : CheckedOpenDiagram definitions) : Type where
  private mk ::
  application : source.val.NodeId
  sourceRegion : source.val.RegionId
  sourceArguments : List source.val.WireId
  sourceParameters : List source.val.WireId
  sourceAttachments : List source.val.WireId
  sourceAttachmentsExact :
    sourceAttachments = sourceArguments ++ sourceParameters
  sourceAttachmentArity :
    sourceAttachments.length = content.val.boundary.length
  sourceAttachmentsSurvive :
    ∀ position : Fin sourceAttachments.length,
      sourceAttachments.get position ≠ dying
  relationArgs : List Sig
  prior : CheckedDiagram definitions
  priorApplication : prior.val.NodeId
  priorRegionImage : source.val.RegionId → prior.val.RegionId
  priorWireImage : source.val.WireId → prior.val.WireId
  priorWireScopeExact :
    ∀ sourceWire,
      (prior.val.wires (priorWireImage sourceWire)).scope =
        priorRegionImage (source.val.wires sourceWire).scope
  priorNodeExact :
    prior.val.nodes priorApplication =
      .atom (priorRegionImage sourceRegion) relationArgs
  priorDyingOwner :
    prior.val.endpointOwner? ⟨priorApplication, .head⟩ =
      some (priorWireImage dying)
  priorArguments : List prior.val.WireId
  priorArgumentsAccepted :
    relationArgumentWires? prior priorApplication relationArgs 0 =
      some priorArguments
  priorArgumentsExact :
    priorArguments = sourceArguments.map priorWireImage
  private removal :
    BatchRemovalPlan prior [] [priorApplication] []
  base : CheckedDiagram definitions
  private baseGenerated :
    base.val =
      ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        prior priorApplication
  baseRegionImage : source.val.RegionId → base.val.RegionId
  baseRegionImageExact :
    ∀ region,
      baseRegionImage region =
        checkedRegion baseGenerated
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
            prior priorApplication (priorRegionImage region))
  baseWireImage : source.val.WireId → base.val.WireId
  baseWireImageExact :
    ∀ sourceWire,
      baseWireImage sourceWire =
        checkedWire baseGenerated
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeWire
            prior priorApplication (priorWireImage sourceWire))
  baseWireScopeExact :
    ∀ sourceWire,
      (base.val.wires (baseWireImage sourceWire)).scope =
        baseRegionImage (source.val.wires sourceWire).scope
  site : base.val.RegionId
  siteExact : site = baseRegionImage sourceRegion
  attachment : ConcreteSpliceAttachment base site content
  targetExact :
    ∀ position : Fin content.val.boundary.length,
      attachment.target position =
        baseWireImage
          (sourceAttachments.get
            (Fin.cast sourceAttachmentArity.symm position))
  checked : CheckedDiagram definitions
  private attachmentAccepted :
    checkConcreteSpliceAttachment base site content attachment.target =
      some attachment
  private generated : checked.val = attachment.diagram
  checkedRegionImage : source.val.RegionId → checked.val.RegionId
  checkedWireImage : source.val.WireId → checked.val.WireId
  checkedWireScopeExact :
    ∀ sourceWire,
      (checked.val.wires (checkedWireImage sourceWire)).scope =
        checkedRegionImage (source.val.wires sourceWire).scope

namespace RelationJoinStep

theorem attachment_accepted
    (step : RelationJoinStep source dying content) :
    checkConcreteSpliceAttachment step.base step.site content
        step.attachment.target =
      some step.attachment :=
  step.attachmentAccepted

theorem checked_generated
    (step : RelationJoinStep source dying content) :
    step.checked.val = step.attachment.diagram :=
  step.generated

theorem base_generated
    (step : RelationJoinStep source dying content) :
    step.base.val =
      ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
        step.prior step.priorApplication :=
  step.baseGenerated

@[simp] theorem checked_dying_scope
    (step : RelationJoinStep source dying content) :
    (step.checked.val.wires (step.checkedWireImage dying)).scope =
      step.checkedRegionImage (source.val.wires dying).scope :=
  step.checkedWireScopeExact dying

end RelationJoinStep

inductive RelationJoinSemanticTrace
    (source : CheckedDiagram definitions) (dying : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId) (args : List Sig) :
    (steps : List (RelationJoinStep source dying content)) →
    (final : CheckedDiagram definitions) → final.val.WireId →
    final.val.RegionId → Prop
  | nil :
      RelationJoinSemanticTrace source dying content parameters args []
        source dying (source.val.wires dying).scope
  | snoc {steps current currentDying currentScope}
      (trace :
        RelationJoinSemanticTrace source dying content parameters args steps
          current currentDying currentScope)
      (step : RelationJoinStep source dying content)
      (_ : step.prior = current)
      (_ : HEq (step.priorWireImage dying) currentDying)
      (_ : HEq
        (step.priorRegionImage (source.val.wires dying).scope) currentScope)
      (_ : step.relationArgs = args)
      (_ : step.sourceParameters = parameters) :
      RelationJoinSemanticTrace source dying content parameters args
        (steps ++ [step]) step.checked (step.checkedWireImage dying)
        (step.checkedRegionImage (source.val.wires dying).scope)

private theorem checkedWire_injective
    {definitions : List (List Sig)}
    {checked : CheckedDiagram definitions}
    {candidate : ConcreteDiagram definitions.length}
    (generated : checked.val = candidate) :
    Function.Injective (checkedWire generated) := by
  intro left right same
  apply Fin.ext
  simpa [checkedWire] using congrArg Fin.val same

private theorem retainedWireIndex_injective
    (source : CheckedDiagram definitions)
    (removed : List source.val.WireId)
    {left right : source.val.WireId}
    (leftMember : left ∈ retainedWires source removed)
    (rightMember : right ∈ retainedWires source removed)
    (same :
      retainedWireIndex source removed left leftMember =
        retainedWireIndex source removed right rightMember) :
    left = right := by
  have values :=
    congrArg (retainedWires source removed).get same
  unfold retainedWireIndex at values
  rw [DenseList.get_index, DenseList.get_index] at values
  exact values

private structure RelationJoinState
    (source : CheckedDiagram definitions)
    (dying : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId)
    (args : List Sig) : Type where
  checked : CheckedDiagram definitions
  regionImage : source.val.RegionId → checked.val.RegionId
  wireImage : source.val.WireId → checked.val.WireId
  wireImage_injective : Function.Injective wireImage
  wireScopeExact :
    ∀ sourceWire,
      (checked.val.wires (wireImage sourceWire)).scope =
        regionImage (source.val.wires sourceWire).scope
  nodeImage : source.val.NodeId → Option checked.val.NodeId
  processed : List source.val.NodeId
  steps : List (RelationJoinStep source dying content)
  traceExact :
    steps.map RelationJoinStep.application = processed
  semanticTrace :
    RelationJoinSemanticTrace source dying content parameters args steps checked
      (wireImage dying) (regionImage (source.val.wires dying).scope)

private structure RelationJoinStepResult
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    {args : List Sig}
    (state : RelationJoinState source dying content parameters args)
    (application : RelationJoinApplication source) : Type where
  next : RelationJoinState source dying content parameters args
  processedExact :
    next.processed = state.processed ++ [application.node]

private theorem relationJoinRegionRetained
    (source : CheckedDiagram definitions)
    (region : source.val.RegionId) :
    region ∈ retainedRegions source [] := by
  simp [retainedRegions, ConcreteDiagram.regionsList,
    Data.Finite.mem_allFin]

private theorem relationJoinWireRetained
    (source : CheckedDiagram definitions)
    (dying candidate : source.val.WireId)
    (different : candidate ≠ dying) :
    candidate ∈ retainedWires source [] := by
  simp [retainedWires, ConcreteDiagram.wiresList,
    Data.Finite.mem_allFin]

private structure RelationJoinInitialResult
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    (plan : RelationJoinPlan source wire content parameters) : Type where
  state : RelationJoinState source wire content parameters plan.args
  checkedExact : state.checked = source
  processedEmpty : state.processed = []

private def relationJoinInitialState
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId)
    (plan : RelationJoinPlan source wire content parameters) :
    RelationJoinInitialResult plan := by
  let state : RelationJoinState source wire content parameters plan.args :=
    { checked := source
      regionImage := id
      wireImage := id
      wireImage_injective := Function.injective_id
      wireScopeExact := fun _ => rfl
      nodeImage := fun node => some node
      processed := []
      steps := []
      traceExact := rfl
      semanticTrace := .nil }
  exact
    { state := state
      checkedExact := rfl
      processedEmpty := rfl }

private def relationJoinAttachments
    {source : CheckedDiagram definitions}
    (application : RelationJoinApplication source)
    (parameters : List source.val.WireId) :
    List source.val.WireId :=
  application.arguments ++ parameters

private def spliceRelationApplication
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId)
    (args : List Sig)
    (state : RelationJoinState source wire content parameters args)
    (application : RelationJoinApplication source) :
    Except Error (RelationJoinStepResult state application) := by
  match priorApplicationAccepted :
      state.nodeImage application.node with
  | none =>
      exact .error (.invalidApplication application.node.val)
  | some priorApplication =>
      if priorNodeExact :
          state.checked.val.nodes priorApplication =
            .atom (state.regionImage application.region) args then
        if priorDyingOwner :
            state.checked.val.endpointOwner?
                ⟨priorApplication, .head⟩ =
              some (state.wireImage wire) then
          match priorArgumentsAccepted :
              relationArgumentWires? state.checked priorApplication args 0 with
          | none =>
              exact .error (.invalidApplication application.node.val)
          | some priorArguments =>
              if priorArgumentsExact :
                  priorArguments =
                    application.arguments.map state.wireImage then
                match removalAccepted :
                    checkBatchRemovalPlan? state.checked []
                      [priorApplication] [] with
                | none =>
                    exact .error .invalidRemoval
                | some removal =>
                    let baseCandidate :=
                      ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
                        state.checked priorApplication
                    match baseAccepted :
                        ConcreteDiagram.checkWellFormed definitions
                          baseCandidate with
                    | .error error =>
                        exact .error (.wellFormed error)
                    | .ok base =>
                        have baseGenerated :=
                          ConcreteDiagram.checkWellFormed_preserves_input
                            baseAccepted
                        let baseRegionImage :
                            source.val.RegionId → base.val.RegionId :=
                          fun region =>
                            checkedRegion baseGenerated
                              (ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
                                state.checked priorApplication
                                (state.regionImage region))
                        let baseWireImage :
                            source.val.WireId → base.val.WireId :=
                          fun sourceWire =>
                            checkedWire baseGenerated
                              (ConcreteDiagram.IdentityNormalizationCore.eraseNodeWire
                                state.checked priorApplication
                                (state.wireImage sourceWire))
                        let baseNodeImage :
                            source.val.NodeId →
                              Option base.val.NodeId :=
                          fun sourceNode =>
                            match state.nodeImage sourceNode with
                            | none => none
                            | some priorNode =>
                                if retained :
                                    priorNode ∈
                                      ConcreteDiagram.IdentityNormalizationCore.retainedNodes
                                        state.checked.val [priorApplication] then
                                  some
                                    (checkedNode baseGenerated
                                      (ConcreteDiagram.IdentityNormalizationCore.eraseNodeIndex
                                        state.checked priorApplication
                                        priorNode retained))
                                else
                                  none
                        let sources :=
                          relationJoinAttachments application parameters
                        if exactArity :
                            sources.length =
                              content.val.boundary.length then
                          if allSurvive :
                              sources.all fun sourceWire =>
                                decide (sourceWire ≠ wire) then
                            let target :
                                Fin content.val.boundary.length →
                                  base.val.WireId :=
                              fun position =>
                                let sourcePosition : Fin sources.length :=
                                  Fin.cast exactArity.symm position
                                let sourceWire :=
                                  sources.get sourcePosition
                                baseWireImage sourceWire
                            let site :=
                              baseRegionImage application.region
                            match attachmentAccepted :
                                checkConcreteSpliceAttachment base site
                                  content target with
                            | none =>
                                exact .error .invalidAttachment
                            | some attachment =>
                                match checked :
                                    ConcreteDiagram.checkWellFormed
                                      definitions attachment.diagram with
                                | .error error =>
                                    exact .error (.wellFormed error)
                                | .ok next =>
                                    have generated :=
                                      ConcreteDiagram.checkWellFormed_preserves_input
                                        checked
                                    have exactTarget :
                                        attachment.target = target :=
                                      checkConcreteSpliceAttachment_target
                                        base site content target attachment
                                          attachmentAccepted
                                    have canonicalAccepted :
                                        checkConcreteSpliceAttachment base site
                                            content attachment.target =
                                          some attachment := by
                                      rw [exactTarget]
                                      exact attachmentAccepted
                                    have baseWireScopeExact :
                                        ∀ sourceWire,
                                          (base.val.wires
                                              (baseWireImage sourceWire)).scope =
                                            baseRegionImage
                                              (source.val.wires
                                                sourceWire).scope := by
                                      intro sourceWire
                                      unfold baseWireImage baseRegionImage
                                      rw [checkedWire_scope_transport]
                                      apply congrArg
                                        (checkedRegion baseGenerated)
                                      simp only [baseCandidate,
                                        ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate]
                                      have sourceExact :
                                          state.checked.val.wiresList.get
                                              (ConcreteDiagram.IdentityNormalizationCore.eraseNodeWire
                                                state.checked priorApplication
                                                (state.wireImage sourceWire)) =
                                            state.wireImage sourceWire := by
                                        apply Fin.ext
                                        simp [ConcreteDiagram.IdentityNormalizationCore.eraseNodeWire,
                                          ConcreteDiagram.wiresList,
                                          Data.Finite.allFin_eq_finRange]
                                      rw [sourceExact,
                                        state.wireScopeExact sourceWire]
                                      apply Fin.ext
                                      rfl
                                    let step :
                                        RelationJoinStep source wire content :=
                                      { application := application.node
                                        sourceRegion := application.region
                                        sourceArguments :=
                                          application.arguments
                                        sourceParameters := parameters
                                        sourceAttachments := sources
                                        sourceAttachmentsExact := rfl
                                        sourceAttachmentArity := exactArity
                                        sourceAttachmentsSurvive :=
                                          fun position =>
                                            of_decide_eq_true
                                              ((List.all_eq_true.mp
                                                  allSurvive)
                                                (sources.get position)
                                                (List.get_mem _ position))
                                        relationArgs := args
                                        prior := state.checked
                                        priorApplication :=
                                          priorApplication
                                        priorRegionImage :=
                                          state.regionImage
                                        priorWireImage := state.wireImage
                                        priorWireScopeExact :=
                                          state.wireScopeExact
                                        priorNodeExact := priorNodeExact
                                        priorDyingOwner := priorDyingOwner
                                        priorArguments := priorArguments
                                        priorArgumentsAccepted :=
                                          priorArgumentsAccepted
                                        priorArgumentsExact :=
                                          priorArgumentsExact
                                        removal := removal
                                        base := base
                                        baseGenerated := baseGenerated
                                        baseRegionImage := baseRegionImage
                                        baseRegionImageExact := fun _ => rfl
                                        baseWireImage := baseWireImage
                                        baseWireImageExact := fun _ => rfl
                                        baseWireScopeExact :=
                                          baseWireScopeExact
                                        site := site
                                        siteExact := rfl
                                        attachment := attachment
                                        targetExact := by
                                          intro position
                                          rw [exactTarget]
                                        checked := next
                                        attachmentAccepted :=
                                          canonicalAccepted
                                        generated := generated
                                        checkedRegionImage := fun region =>
                                          checkedRegion generated
                                            (attachment.hostRegion
                                              (baseRegionImage region))
                                        checkedWireImage := fun sourceWire =>
                                          checkedWire generated
                                            (attachment.hostWire
                                              (baseWireImage sourceWire))
                                        checkedWireScopeExact := by
                                          intro sourceWire
                                          rw [checkedWire_scope_transport,
                                            attachment.diagram_wire_hostWire_scope]
                                          exact
                                            congrArg (checkedRegion generated)
                                              (congrArg attachment.hostRegion
                                                (baseWireScopeExact
                                                  sourceWire)) }
                                    let nextState :
                                        RelationJoinState source wire content
                                          parameters args :=
                                      { checked := next
                                        regionImage :=
                                          step.checkedRegionImage
                                        wireImage := step.checkedWireImage
                                        wireImage_injective := by
                                          intro left right same
                                          apply state.wireImage_injective
                                          apply
                                            ConcreteDiagram.IdentityNormalizationCore.eraseNodeWire_injective
                                              state.checked priorApplication
                                          apply
                                            checkedWire_injective
                                              baseGenerated
                                          apply
                                            attachment.hostWire_injective
                                          apply
                                            checkedWire_injective generated
                                          exact same
                                        wireScopeExact :=
                                          step.checkedWireScopeExact
                                        nodeImage := fun sourceNode =>
                                          (baseNodeImage sourceNode).map
                                            fun baseNode =>
                                              checkedNode generated
                                                (attachment.hostNode
                                                  baseNode)
                                        processed :=
                                          state.processed ++
                                            [application.node]
                                        steps := state.steps ++ [step]
                                        traceExact := by
                                          simp [step, state.traceExact]
                                        semanticTrace :=
                                          .snoc state.semanticTrace step
                                            rfl (by simp [step]) (by simp [step])
                                            rfl rfl }
                                    exact .ok
                                      { next := nextState
                                        processedExact := rfl }
                          else
                            exact .error .dyingWireParameter
                        else
                          exact .error .boundaryArityMismatch
              else
                exact .error (.invalidApplication application.node.val)
        else
          exact .error (.invalidApplication application.node.val)
      else
        exact .error (.invalidApplication application.node.val)

private def spliceRelationApplications
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId) :
    (args : List Sig) →
    RelationJoinState source wire content parameters args →
      List (RelationJoinApplication source) →
        Except Error
          (RelationJoinState source wire content parameters args)
  | _, state, [] => .ok state
  | args, state, application :: rest => do
      let step ←
        spliceRelationApplication source wire content parameters args
          state application
      spliceRelationApplications source wire content parameters args
        step.next rest

private theorem spliceRelationApplications_processed
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId)
    (args : List Sig)
    (state final : RelationJoinState source wire content parameters args)
    (applications : List (RelationJoinApplication source))
    (accepted :
      spliceRelationApplications source wire content parameters args
          state applications =
        .ok final) :
    final.processed =
      state.processed ++
        applications.map RelationJoinApplication.node := by
  induction applications generalizing state with
  | nil =>
      simp only [spliceRelationApplications, Except.ok.injEq] at accepted
      subst final
      simp
  | cons application rest induction =>
      unfold spliceRelationApplications at accepted
      cases stepAccepted :
          spliceRelationApplication source wire content parameters args
            state application with
      | error error =>
          rw [stepAccepted] at accepted
          contradiction
      | ok step =>
          rw [stepAccepted] at accepted
          rw [induction step.next accepted, step.processedExact]
          simp [List.append_assoc]

private structure RelationJoinFinalRemoval
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    {args : List Sig}
    (state : RelationJoinState source wire content parameters args) : Type where
  checked : CheckedDiagram definitions
  plan :
    BatchRemovalPlan state.checked [] [] [state.wireImage wire]
  generated :
    checked.val = batchRemovalCandidate plan
  regionImage : source.val.RegionId → checked.val.RegionId
  wireImage :
    ∀ sourceWire : source.val.WireId,
      sourceWire ≠ wire → checked.val.WireId

private def removeRelationJoinWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    {args : List Sig}
    (state : RelationJoinState source wire content parameters args) :
    Except Error (RelationJoinFinalRemoval state) := by
  let dying := state.wireImage wire
  match prepared :
      checkBatchRemovalPlan? state.checked [] [] [dying] with
  | none =>
      exact .error .invalidRemoval
  | some plan =>
      let candidate := batchRemovalCandidate plan
      match accepted :
          ConcreteDiagram.checkWellFormed definitions candidate with
      | .error error =>
          exact .error (.wellFormed error)
      | .ok checked =>
          have generated :=
            ConcreteDiagram.checkWellFormed_preserves_input accepted
          exact .ok
            { checked := checked
              plan := plan
              generated := generated
              regionImage := fun region =>
                checkedRegion generated
                  (retainedRegionIndex state.checked []
                    (state.regionImage region) (by
                      simp [retainedRegions,
                        ConcreteDiagram.regionsList,
                        Data.Finite.mem_allFin]))
              wireImage := fun sourceWire different =>
                checkedWire generated
                  (retainedWireIndex state.checked [dying]
                    (state.wireImage sourceWire) (by
                      have mappedDifferent :
                          state.wireImage sourceWire ≠ dying := by
                        intro same
                        exact different (state.wireImage_injective same)
                      simp [retainedWires,
                        ConcreteDiagram.wiresList,
                        Data.Finite.mem_allFin, mappedDifferent])) }

/-- Checked output of grounding every applied endpoint of one relation wire. -/
structure RelationJoinResult
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId) : Type where
  private mk ::
  checked : CheckedDiagram definitions
  applications : List source.val.NodeId
  wireImage :
    ∀ sourceWire : source.val.WireId,
      sourceWire ≠ wire → checked.val.WireId
  private plan : RelationJoinPlan source wire content parameters
  private initial : RelationJoinInitialResult plan
  private finalState :
    RelationJoinState source wire content parameters plan.args
  private batchAccepted :
    spliceRelationApplications source wire content parameters plan.args
        initial.state plan.applications =
      .ok finalState
  private finalRemoval : RelationJoinFinalRemoval finalState
  private normalization :
    ConcreteDiagram.IdentityNormalization finalRemoval.checked
  private normalizationExact :
    normalization =
      ConcreteDiagram.normalizeIdentities finalRemoval.checked
  private checkedExact : checked = normalization.target
  private applicationsExact :
    applications = finalState.processed

namespace RelationJoinResult

def args
    (result : RelationJoinResult source wire content parameters) :
    List Sig :=
  result.plan.args

def boundarySignatures
    (_result : RelationJoinResult source wire content parameters) :
    List Sig :=
  openBoundarySigs content

def parameterSignatures
    (_result : RelationJoinResult source wire content parameters) :
    List Sig :=
  parameterSigs source parameters

def initialChecked
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source wire content parameters) :
    CheckedDiagram definitions :=
  result.initial.state.checked

section FinalDeletion

variable {definitions : List (List Sig)} {source : CheckedDiagram definitions}
variable {wire : source.val.WireId}
variable {content : CheckedOpenDiagram definitions}
variable {parameters : List source.val.WireId}

def boundFinal
    (result : RelationJoinResult source wire content parameters) :
    CheckedDiagram definitions :=
  result.finalState.checked

def boundRegionImage
    (result : RelationJoinResult source wire content parameters) :
    source.val.RegionId → result.boundFinal.val.RegionId :=
  result.finalState.regionImage

def boundDying
    (result : RelationJoinResult source wire content parameters) :
    result.boundFinal.val.WireId :=
  result.finalState.wireImage wire

def plainFinal
    (result : RelationJoinResult source wire content parameters) :
    CheckedDiagram definitions :=
  result.finalRemoval.checked

theorem final_deletion_exact
    (result : RelationJoinResult source wire content parameters) :
    result.plainFinal.val =
      ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
        result.boundFinal result.boundDying := by
  unfold plainFinal; rw [result.finalRemoval.generated]
  unfold boundFinal boundDying batchRemovalCandidate
    ConcreteDiagram.IdentityNormalizationCore.eraseWireCandidate
    batchRegionTable batchNodeTable batchWireTable batchEndpoint?
  unfold retainedRegionIndex retainedNodeIndex
    sourceRetainedRegion sourceRetainedNode sourceRetainedWire
    DenseList.index
  unfold retainedRegions retainedNodes retainedWires
    ConcreteDiagram.IdentityNormalizationCore.retainedWires
  congr 1
  funext target
  split
  · rename_i equation
    simp only [equation]
  · rename_i parent equation
    simp only [equation]

@[simp] theorem bound_dying_scope
    (result : RelationJoinResult source wire content parameters) :
    (result.boundFinal.val.wires result.boundDying).scope =
      result.boundRegionImage (source.val.wires wire).scope :=
  result.finalState.wireScopeExact wire

theorem semantic_trace
    (result : RelationJoinResult source wire content parameters) :
    RelationJoinSemanticTrace source wire content parameters result.args
      result.finalState.steps result.boundFinal result.boundDying
        (result.boundRegionImage (source.val.wires wire).scope) :=
  result.finalState.semanticTrace

end FinalDeletion

theorem relation_signature
    (result : RelationJoinResult source wire content parameters) :
    (source.val.wires wire).sig = .rel result.args :=
  result.plan.relationSignature

theorem boundary_exact
    (result : RelationJoinResult source wire content parameters) :
    result.boundarySignatures =
      result.args ++ result.parameterSignatures :=
  result.plan.boundaryExact

theorem parameters_survive
    (result : RelationJoinResult source wire content parameters)
    (position : Fin parameters.length) :
    parameters.get position ≠ wire :=
  result.plan.parametersSurvive position

theorem initial_exact
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source wire content parameters) :
    result.initialChecked = source :=
  result.initial.checkedExact

theorem applications_complete
    (result : RelationJoinResult source wire content parameters) :
    result.applications =
      result.plan.applications.map RelationJoinApplication.node := by
  calc
    result.applications = result.finalState.processed :=
      result.applicationsExact
    _ =
        result.initial.state.processed ++
          result.plan.applications.map RelationJoinApplication.node :=
      spliceRelationApplications_processed source wire content parameters
        result.plan.args result.initial.state result.finalState
        result.plan.applications result.batchAccepted
    _ = result.plan.applications.map RelationJoinApplication.node := by
      rw [result.initial.processedEmpty]
      simp

theorem endpoint_applied
    (result : RelationJoinResult source wire content parameters)
    (endpoint : CEndpoint source.val.nodeCount)
    (member : endpoint ∈ (source.val.wires wire).endpoints) :
    endpoint.port = .head ∧
      ∃ region,
        source.val.nodes endpoint.node = .atom region result.args := by
  have accepted :=
    (List.all_eq_true.mp result.plan.endpointsApplied) endpoint member
  unfold relationEndpointIsApplied at accepted
  cases portData : endpoint.port <;>
    cases nodeData : source.val.nodes endpoint.node <;>
    simp [portData, nodeData] at accepted
  rename_i region nodeArgs
  exact
    ⟨rfl, region, by
      simpa [args, accepted] using nodeData⟩

theorem trace_complete
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    {parameters : List source.val.WireId}
    (result : RelationJoinResult source wire content parameters) :
    ∃ steps : List (RelationJoinStep source wire content),
      ∃ normalization :
          ConcreteDiagram.IdentityNormalization result.plainFinal,
        RelationJoinSemanticTrace source wire content parameters result.args
            steps result.boundFinal result.boundDying
              (result.boundRegionImage (source.val.wires wire).scope) ∧
          steps.map RelationJoinStep.application =
            result.applications ∧
          normalization =
            ConcreteDiagram.normalizeIdentities result.plainFinal ∧
          normalization.target = result.checked := by
  refine
    ⟨result.finalState.steps, result.normalization,
      result.finalState.semanticTrace, ?_, result.normalizationExact,
      result.checkedExact.symm⟩
  exact
    result.finalState.traceExact.trans result.applicationsExact.symm

end RelationJoinResult

/--
Ground one relation wire by deleting all of its applied-head atoms, splicing
the supplied checked-open content at every application in source node order,
and deleting the exhausted relation wire.  Identity normalization runs once
after the complete ordered batch.
-/
def joinRelation
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (content : CheckedOpenDiagram definitions)
    (parameters : List source.val.WireId) :
    Except Error (RelationJoinResult source wire content parameters) := by
  match prepared :
      checkRelationJoinPlan source wire content parameters with
  | .error error =>
      exact .error error
  | .ok plan =>
      let initial :=
        relationJoinInitialState source wire content parameters plan
      match batchAccepted :
          spliceRelationApplications source wire content parameters plan.args
            initial.state plan.applications with
      | .error error =>
          exact .error error
      | .ok finalState =>
          match removed : removeRelationJoinWire finalState with
          | .error error =>
              exact .error error
          | .ok finalRemoval =>
              let normalization :=
                ConcreteDiagram.normalizeIdentities finalRemoval.checked
              exact .ok
                (RelationJoinResult.mk normalization.target
                  finalState.processed
                  (fun sourceWire different =>
                    normalization.wireImage
                      (finalRemoval.wireImage sourceWire different))
                  plan initial finalState batchAccepted finalRemoval
                  normalization rfl rfl rfl)

private def iotaSeverCandidate
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (keep : List (CEndpoint source.val.nodeCount)) :
    ConcreteDiagram definitions.length where
  regionCount := source.val.regionCount
  nodeCount := source.val.nodeCount
  wireCount := source.val.wireCount + 1
  root := source.val.root
  regions := source.val.regions
  nodes := source.val.nodes
  wires :=
    Fin.addCases
      (fun candidate =>
        let data := source.val.wires candidate
        if candidate = wire then
          { data with
            endpoints := data.endpoints.filter fun endpoint =>
              decide (endpoint ∈ keep) }
        else
          data)
      (fun _ =>
        let data := source.val.wires wire
        { data with
          endpoints := data.endpoints.filter fun endpoint =>
            decide (endpoint ∉ keep) })

private def iotaJoinWires
    (source : CheckedDiagram definitions)
    (inner : source.val.WireId) :
    List source.val.WireId :=
  source.val.wiresList.filter fun candidate =>
    decide (candidate ≠ inner)

private theorem filter_ne_length_of_nodup_mem
    [DecidableEq α] {removed : α} {values : List α}
    (nodup : values.Nodup) (member : removed ∈ values) :
    (values.filter fun value => decide (value ≠ removed)).length =
      values.length - 1 := by
  induction values with
  | nil => simp at member
  | cons head tail induction =>
      rw [List.nodup_cons] at nodup
      rcases nodup with ⟨headFresh, tailNodup⟩
      by_cases same : head = removed
      · subst head
        have retained :
            tail.filter (fun value => decide (value ≠ removed)) = tail :=
          List.filter_eq_self.mpr fun value valueMember => by
            apply decide_eq_true
            intro equality
            subst value
            exact headFresh valueMember
        rw [List.filter_cons_of_neg (by simp), retained]
        simp
      · have tailMember : removed ∈ tail := by
          rcases List.mem_cons.mp member with equality | tailMember
          · exact False.elim (same equality.symm)
          · exact tailMember
        rw [List.filter_cons_of_pos (by simp [same])]
        simp only [List.length_cons]
        have tailLength := induction tailNodup tailMember
        have tailPositive : 0 < tail.length :=
          List.length_pos_iff.mpr (by
            intro empty
            subst tail
            simp at tailMember)
        omega

private def iotaJoinCandidate
    (source : CheckedDiagram definitions)
    (outer inner : source.val.WireId) :
    ConcreteDiagram definitions.length where
  regionCount := source.val.regionCount
  nodeCount := source.val.nodeCount
  wireCount := (iotaJoinWires source inner).length
  root := source.val.root
  regions := source.val.regions
  nodes := source.val.nodes
  wires := fun target =>
    let sourceWire := (iotaJoinWires source inner).get target
    let data := source.val.wires sourceWire
    if sourceWire = outer then
      { data with
        endpoints :=
          data.endpoints ++ (source.val.wires inner).endpoints }
    else
      data

/-- Checked output of one individual-wire endpoint partition. -/
structure IotaSeverResult
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (keep : List (CEndpoint source.val.nodeCount)) : Type where
  private mk ::
  checked : CheckedDiagram definitions
  private sourceSignature : (source.val.wires wire).sig = .iota
  private generated :
    checked.val = iotaSeverCandidate source wire keep
  private rejoined : CheckedDiagram definitions
  private rejoinedGenerated :
    rejoined.val =
      iotaJoinCandidate checked
        (checkedWire generated (Fin.castAdd 1 wire))
        (checkedWire generated
          (Fin.natAdd source.val.wireCount (0 : Fin 1)))

namespace IotaSeverResult

def regionImage
    (result : IotaSeverResult source wire keep)
    (region : source.val.RegionId) :
    result.checked.val.RegionId :=
  checkedRegion result.generated region

def nodeImage
    (result : IotaSeverResult source wire keep)
    (node : source.val.NodeId) :
    result.checked.val.NodeId :=
  checkedNode result.generated node

def wireImage
    (result : IotaSeverResult source wire keep)
    (sourceWire : source.val.WireId) :
    result.checked.val.WireId :=
  checkedWire result.generated (Fin.castAdd 1 sourceWire)

def freshWire
    (result : IotaSeverResult source wire keep) :
    result.checked.val.WireId :=
  checkedWire result.generated
    (Fin.natAdd source.val.wireCount (0 : Fin 1))

def endpointImage
    (result : IotaSeverResult source wire keep)
    (endpoint : CEndpoint source.val.nodeCount) :
    CEndpoint result.checked.val.nodeCount :=
  checkedEndpoint result.generated endpoint

def renameRegion
    (result : IotaSeverResult source wire keep) :
    CRegion source.val.regionCount →
      CRegion result.checked.val.regionCount
  | .sheet => .sheet
  | .cut parent => .cut (result.regionImage parent)

def renameNode
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {keep : List (CEndpoint source.val.nodeCount)}
    (result : IotaSeverResult source wire keep) :
    CNode source.val.regionCount definitions.length →
      CNode result.checked.val.regionCount definitions.length
  | .atom region args => .atom (result.regionImage region) args
  | .ref region definition args =>
      .ref (result.regionImage region) definition args
  | .identity region sig arity =>
      .identity (result.regionImage region) sig arity

theorem checked_generated
    (result : IotaSeverResult source wire keep) :
    result.checked.val = iotaSeverCandidate source wire keep :=
  result.generated

@[simp] theorem regionCount
    (result : IotaSeverResult source wire keep) :
    result.checked.val.regionCount = source.val.regionCount :=
  by
    simpa [iotaSeverCandidate] using
      congrArg ConcreteDiagram.regionCount result.generated

@[simp] theorem nodeCount
    (result : IotaSeverResult source wire keep) :
    result.checked.val.nodeCount = source.val.nodeCount :=
  by
    simpa [iotaSeverCandidate] using
      congrArg ConcreteDiagram.nodeCount result.generated

@[simp] theorem wireCount
    (result : IotaSeverResult source wire keep) :
    result.checked.val.wireCount = source.val.wireCount + 1 :=
  by
    simpa [iotaSeverCandidate] using
      congrArg ConcreteDiagram.wireCount result.generated

@[simp] theorem root_generated
    (result : IotaSeverResult source wire keep) :
    result.checked.val.root = result.regionImage source.val.root := by
  unfold regionImage
  rw [checkedRoot_transport]
  rfl

@[simp] theorem region_generated
    (result : IotaSeverResult source wire keep)
    (region : source.val.RegionId) :
    result.checked.val.regions (result.regionImage region) =
      result.renameRegion (source.val.regions region) := by
  unfold regionImage renameRegion
  rw [checkedRegion_data_transport]
  simp only [iotaSeverCandidate]
  cases source.val.regions region <;> rfl

theorem climb_regionImage
    (result : IotaSeverResult source wire keep)
    (steps : Nat) (region : source.val.RegionId) :
    result.checked.val.climb steps (result.regionImage region) =
      (source.val.climb steps region).map result.regionImage := by
  induction steps generalizing region with
  | zero => rfl
  | succ steps induction =>
      simp only [ConcreteDiagram.climb]
      rw [result.region_generated]
      cases data : source.val.regions region with
      | sheet => rfl
      | cut parent =>
          simp only [IotaSeverResult.renameRegion]
          exact induction parent

@[simp] theorem node_generated
    (result : IotaSeverResult source wire keep)
    (node : source.val.NodeId) :
    result.checked.val.nodes (result.nodeImage node) =
      result.renameNode (source.val.nodes node) := by
  unfold nodeImage renameNode
  rw [checkedNode_data_transport]
  simp only [iotaSeverCandidate]
  cases source.val.nodes node <;> rfl

@[simp] theorem wireImage_signature
    (result : IotaSeverResult source wire keep)
    (sourceWire : source.val.WireId) :
    (result.checked.val.wires (result.wireImage sourceWire)).sig =
      (source.val.wires sourceWire).sig := by
  unfold wireImage
  rw [checkedWire_signature_transport]
  simp [iotaSeverCandidate]
  split <;> rfl

@[simp] theorem freshWire_signature
    (result : IotaSeverResult source wire keep) :
    (result.checked.val.wires result.freshWire).sig = .iota := by
  unfold freshWire
  rw [checkedWire_signature_transport]
  simpa [iotaSeverCandidate] using result.sourceSignature

@[simp] theorem wireImage_scope
    (result : IotaSeverResult source wire keep)
    (sourceWire : source.val.WireId) :
    (result.checked.val.wires (result.wireImage sourceWire)).scope =
      result.regionImage (source.val.wires sourceWire).scope := by
  unfold wireImage regionImage
  rw [checkedWire_scope_transport]
  simp [iotaSeverCandidate]
  split <;> rfl

@[simp] theorem freshWire_scope
    (result : IotaSeverResult source wire keep) :
    (result.checked.val.wires result.freshWire).scope =
      result.regionImage (source.val.wires wire).scope := by
  unfold freshWire regionImage
  rw [checkedWire_scope_transport]
  simp only [iotaSeverCandidate, Fin.addCases_right]

theorem wireImage_endpoints
    (result : IotaSeverResult source wire keep)
    (sourceWire : source.val.WireId) :
    (result.checked.val.wires (result.wireImage sourceWire)).endpoints =
      (if sourceWire = wire then
        (source.val.wires sourceWire).endpoints.filter fun endpoint =>
          decide (endpoint ∈ keep)
      else
        (source.val.wires sourceWire).endpoints).map result.endpointImage := by
  unfold wireImage endpointImage
  rw [checkedWire_endpoints_transport]
  simp only [iotaSeverCandidate, Fin.addCases_left]
  split <;> rfl

theorem freshWire_endpoints
    (result : IotaSeverResult source wire keep) :
    (result.checked.val.wires result.freshWire).endpoints =
      ((source.val.wires wire).endpoints.filter fun endpoint =>
        decide (endpoint ∉ keep)).map result.endpointImage := by
  unfold freshWire endpointImage
  rw [checkedWire_endpoints_transport]
  simp only [iotaSeverCandidate, Fin.addCases_right]

end IotaSeverResult

/--
Split one individual wire into two co-scoped wires according to an exact
endpoint partition. Polarity and orientation are intentionally rule-owned.
-/
def severIota
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (keep : List (CEndpoint source.val.nodeCount)) :
    Except Error (IotaSeverResult source wire keep) := by
  if signature : (source.val.wires wire).sig = .iota then
    if partition :
        ∀ endpoint, endpoint ∈ keep →
          endpoint ∈ (source.val.wires wire).endpoints then
      let candidate := iotaSeverCandidate source wire keep
      match accepted :
          ConcreteDiagram.checkWellFormed definitions candidate with
      | .error error =>
          exact .error (.wellFormed error)
      | .ok checked =>
          let generated :=
            ConcreteDiagram.checkWellFormed_preserves_input accepted
          let retained :=
            checkedWire generated (Fin.castAdd 1 wire)
          let fresh :=
            checkedWire generated
              (Fin.natAdd source.val.wireCount (0 : Fin 1))
          let rejoinCandidate :=
            iotaJoinCandidate checked retained fresh
          match rejoinAccepted :
              ConcreteDiagram.checkWellFormed definitions rejoinCandidate with
          | .error error =>
              exact .error (.wellFormed error)
          | .ok rejoined =>
              exact .ok
                (IotaSeverResult.mk checked signature generated rejoined
                  (ConcreteDiagram.checkWellFormed_preserves_input
                    rejoinAccepted))
    else
      exact .error .invalidEndpointPartition
  else
    exact .error (.expectedIota wire.val)

/-- Checked output of one comparable-scope individual-wire merge. -/
structure IotaJoinResult
    (source : CheckedDiagram definitions)
    (outer inner : source.val.WireId) : Type where
  private mk ::
  checked : CheckedDiagram definitions
  private different : outer ≠ inner
  private outerSignature : (source.val.wires outer).sig = .iota
  private innerSignature : (source.val.wires inner).sig = .iota
  private generated :
    checked.val = iotaJoinCandidate source outer inner

namespace IotaJoinResult

def regionImage
    (result : IotaJoinResult source outer inner)
    (region : source.val.RegionId) :
    result.checked.val.RegionId :=
  checkedRegion result.generated region

def nodeImage
    (result : IotaJoinResult source outer inner)
    (node : source.val.NodeId) :
    result.checked.val.NodeId :=
  checkedNode result.generated node

def wireImage
    (result : IotaJoinResult source outer inner)
    (sourceWire : source.val.WireId)
    (survives : sourceWire ≠ inner) :
    result.checked.val.WireId :=
  checkedWire result.generated
    (DenseList.index (iotaJoinWires source inner) sourceWire (by
      simp [iotaJoinWires, ConcreteDiagram.wiresList,
        Data.Finite.mem_allFin, survives]))

def outerWire
    (result : IotaJoinResult source outer inner) :
    result.checked.val.WireId :=
  result.wireImage outer result.different

def endpointImage
    (result : IotaJoinResult source outer inner)
    (endpoint : CEndpoint source.val.nodeCount) :
    CEndpoint result.checked.val.nodeCount :=
  checkedEndpoint result.generated endpoint

def renameRegion
    (result : IotaJoinResult source outer inner) :
    CRegion source.val.regionCount →
      CRegion result.checked.val.regionCount
  | .sheet => .sheet
  | .cut parent => .cut (result.regionImage parent)

def renameNode
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {outer inner : source.val.WireId}
    (result : IotaJoinResult source outer inner) :
    CNode source.val.regionCount definitions.length →
      CNode result.checked.val.regionCount definitions.length
  | .atom region args => .atom (result.regionImage region) args
  | .ref region definition args =>
      .ref (result.regionImage region) definition args
  | .identity region sig arity =>
      .identity (result.regionImage region) sig arity

theorem checked_generated
    (result : IotaJoinResult source outer inner) :
    result.checked.val = iotaJoinCandidate source outer inner :=
  result.generated

theorem outer_ne_inner
    (result : IotaJoinResult source outer inner) :
    outer ≠ inner :=
  result.different

@[simp] theorem source_outer_signature
    (result : IotaJoinResult source outer inner) :
    (source.val.wires outer).sig = .iota :=
  result.outerSignature

@[simp] theorem source_inner_signature
    (result : IotaJoinResult source outer inner) :
    (source.val.wires inner).sig = .iota :=
  result.innerSignature

@[simp] theorem regionCount
    (result : IotaJoinResult source outer inner) :
    result.checked.val.regionCount = source.val.regionCount := by
  simpa [iotaJoinCandidate] using
    congrArg ConcreteDiagram.regionCount result.generated

@[simp] theorem nodeCount
    (result : IotaJoinResult source outer inner) :
    result.checked.val.nodeCount = source.val.nodeCount := by
  simpa [iotaJoinCandidate] using
    congrArg ConcreteDiagram.nodeCount result.generated

@[simp] theorem wireCount
    (result : IotaJoinResult source outer inner) :
    result.checked.val.wireCount = (iotaJoinWires source inner).length := by
  simpa [iotaJoinCandidate] using
    congrArg ConcreteDiagram.wireCount result.generated

@[simp] theorem root_generated
    (result : IotaJoinResult source outer inner) :
    result.checked.val.root = result.regionImage source.val.root := by
  unfold regionImage
  rw [checkedRoot_transport]
  rfl

@[simp] theorem region_generated
    (result : IotaJoinResult source outer inner)
    (region : source.val.RegionId) :
    result.checked.val.regions (result.regionImage region) =
      result.renameRegion (source.val.regions region) := by
  unfold regionImage renameRegion
  rw [checkedRegion_data_transport]
  simp only [iotaJoinCandidate]
  cases source.val.regions region <;> rfl

@[simp] theorem node_generated
    (result : IotaJoinResult source outer inner)
    (node : source.val.NodeId) :
    result.checked.val.nodes (result.nodeImage node) =
      result.renameNode (source.val.nodes node) := by
  unfold nodeImage renameNode
  rw [checkedNode_data_transport]
  simp only [iotaJoinCandidate]
  cases source.val.nodes node <;> rfl

@[simp] theorem wireImage_signature
    (result : IotaJoinResult source outer inner)
    (sourceWire : source.val.WireId)
    (survives : sourceWire ≠ inner) :
    (result.checked.val.wires
        (result.wireImage sourceWire survives)).sig =
      (source.val.wires sourceWire).sig := by
  unfold wireImage
  rw [checkedWire_signature_transport]
  simp only [iotaJoinCandidate]
  rw [DenseList.get_index]
  split <;> rfl

@[simp] theorem wireImage_scope
    (result : IotaJoinResult source outer inner)
    (sourceWire : source.val.WireId)
    (survives : sourceWire ≠ inner) :
    (result.checked.val.wires
        (result.wireImage sourceWire survives)).scope =
      result.regionImage (source.val.wires sourceWire).scope := by
  unfold wireImage regionImage
  rw [checkedWire_scope_transport]
  simp only [iotaJoinCandidate]
  rw [DenseList.get_index]
  split <;> rfl

theorem wireImage_endpoints
    (result : IotaJoinResult source outer inner)
    (sourceWire : source.val.WireId)
    (survives : sourceWire ≠ inner) :
    (result.checked.val.wires
        (result.wireImage sourceWire survives)).endpoints =
      (if sourceWire = outer then
        (source.val.wires outer).endpoints ++
          (source.val.wires inner).endpoints
      else
        (source.val.wires sourceWire).endpoints).map
          result.endpointImage := by
  unfold wireImage endpointImage
  rw [checkedWire_endpoints_transport]
  simp only [iotaJoinCandidate]
  rw [DenseList.get_index]
  split
  · rename_i same
    subst sourceWire
    rfl
  · rfl

end IotaJoinResult

namespace IotaSeverResult

/--
The checker-owned inverse join of an accepted iota sever. Its checked target
is the canonical stable-partition rejoin retained by the sever receipt.
-/
def inverseJoin
    (result : IotaSeverResult source wire keep) :
    IotaJoinResult result.checked (result.wireImage wire)
      result.freshWire :=
  IotaJoinResult.mk result.rejoined (by
    intro same
    have values := congrArg Fin.val same
    unfold wireImage freshWire checkedWire at values
    simp only [Fin.coe_cast, Fin.val_castAdd, Fin.val_natAdd] at values
    omega)
    (by
      rw [result.wireImage_signature]
      exact result.sourceSignature)
    result.freshWire_signature
    (by
      simpa [wireImage, freshWire] using result.rejoinedGenerated)

@[simp] theorem inverseJoin_checked
    (result : IotaSeverResult source wire keep) :
    result.inverseJoin.checked = result.rejoined :=
  rfl

@[simp] theorem inverseJoin_regionCount
    (result : IotaSeverResult source wire keep) :
    result.inverseJoin.checked.val.regionCount = source.val.regionCount := by
  rw [result.inverseJoin.regionCount, result.regionCount]

@[simp] theorem inverseJoin_nodeCount
    (result : IotaSeverResult source wire keep) :
    result.inverseJoin.checked.val.nodeCount = source.val.nodeCount := by
  rw [result.inverseJoin.nodeCount, result.nodeCount]

@[simp] theorem inverseJoin_wireCount
    (result : IotaSeverResult source wire keep) :
    result.inverseJoin.checked.val.wireCount = source.val.wireCount := by
  rw [result.inverseJoin.wireCount]
  unfold iotaJoinWires
  unfold ConcreteDiagram.wiresList
  rw [filter_ne_length_of_nodup_mem
    (Data.Finite.allFin_nodup result.checked.val.wireCount)
    (Data.Finite.mem_allFin result.freshWire)]
  simp only [ConcreteDiagram.wiresList, Data.Finite.allFin_eq_finRange,
    List.length_finRange]
  rw [result.wireCount]
  omega

private def inverseRegion
    (result : IotaSeverResult source wire keep)
    (region : source.val.RegionId) :
    result.inverseJoin.checked.val.RegionId :=
  Fin.cast result.inverseJoin_regionCount.symm region

private def inverseNode
    (result : IotaSeverResult source wire keep)
    (node : source.val.NodeId) :
    result.inverseJoin.checked.val.NodeId :=
  Fin.cast result.inverseJoin_nodeCount.symm node

@[simp] private theorem inverse_regionImage
    (result : IotaSeverResult source wire keep)
    (region : source.val.RegionId) :
    result.inverseJoin.regionImage (result.regionImage region) =
      result.inverseRegion region := by
  apply Fin.ext
  rfl

@[simp] private theorem inverse_nodeImage
    (result : IotaSeverResult source wire keep)
    (node : source.val.NodeId) :
    result.inverseJoin.nodeImage (result.nodeImage node) =
      result.inverseNode node := by
  apply Fin.ext
  rfl

private theorem retained_ne_fresh
    (result : IotaSeverResult source wire keep)
    (sourceWire : source.val.WireId) :
    result.wireImage sourceWire ≠ result.freshWire := by
  intro same
  have values := congrArg Fin.val same
  unfold wireImage freshWire checkedWire at values
  simp only [Fin.coe_cast, Fin.val_castAdd, Fin.val_natAdd] at values
  omega

private def rejoinSourceWire
    (result : IotaSeverResult source wire keep)
    (target : result.inverseJoin.checked.val.WireId) :
    result.checked.val.WireId :=
  (iotaJoinWires result.checked result.freshWire).get
    (Fin.cast result.inverseJoin.wireCount target)

private theorem rejoinSourceWire_survives
    (result : IotaSeverResult source wire keep)
    (target : result.inverseJoin.checked.val.WireId) :
    result.rejoinSourceWire target ≠ result.freshWire := by
  have member :
      result.rejoinSourceWire target ∈
        iotaJoinWires result.checked result.freshWire :=
    List.get_mem _ _
  exact of_decide_eq_true (List.mem_filter.mp member).2

@[simp] private theorem inverseJoin_wireImage_sourceWire
    (result : IotaSeverResult source wire keep)
    (target : result.inverseJoin.checked.val.WireId) :
    result.inverseJoin.wireImage (result.rejoinSourceWire target)
        (result.rejoinSourceWire_survives target) =
      target := by
  unfold IotaJoinResult.wireImage rejoinSourceWire
  apply Fin.ext
  change
    (DenseList.index
      (iotaJoinWires result.checked result.freshWire)
      ((iotaJoinWires result.checked result.freshWire).get
        (Fin.cast result.inverseJoin.wireCount target)) _).val =
      target.val
  rw [DenseList.index_get
    (iotaJoinWires result.checked result.freshWire)
    ((Data.Finite.allFin_nodup result.checked.val.wireCount).filter _)
    (Fin.cast result.inverseJoin.wireCount target)]
  rfl

@[simp] private theorem rejoinSourceWire_wireImage
    (result : IotaSeverResult source wire keep)
    (splitWire : result.checked.val.WireId)
    (survives : splitWire ≠ result.freshWire) :
    result.rejoinSourceWire
        (result.inverseJoin.wireImage splitWire survives) =
      splitWire := by
  have member :
      splitWire ∈ iotaJoinWires result.checked result.freshWire := by
    simp [iotaJoinWires, ConcreteDiagram.wiresList,
      Data.Finite.mem_allFin, survives]
  unfold rejoinSourceWire IotaJoinResult.wireImage
  apply Fin.ext
  change
    ((iotaJoinWires result.checked result.freshWire).get
      (DenseList.index
        (iotaJoinWires result.checked result.freshWire)
        splitWire member)).val =
      splitWire.val
  rw [DenseList.get_index]

private def sourceWireOfRetained
    (result : IotaSeverResult source wire keep)
    (splitWire : result.checked.val.WireId)
    (survives : splitWire ≠ result.freshWire) :
    source.val.WireId :=
  ⟨splitWire.val, by
    have bound := splitWire.isLt
    have freshValue : result.freshWire.val = source.val.wireCount := by
      unfold freshWire checkedWire
      simp only [Fin.coe_cast, Fin.val_natAdd]
      omega
    have notLast : splitWire.val ≠ source.val.wireCount := by
      intro same
      apply survives
      apply Fin.ext
      exact same.trans freshValue.symm
    have count := result.wireCount
    omega⟩

@[simp] private theorem wireImage_sourceWireOfRetained
    (result : IotaSeverResult source wire keep)
    (splitWire : result.checked.val.WireId)
    (survives : splitWire ≠ result.freshWire) :
    result.wireImage (result.sourceWireOfRetained splitWire survives) =
      splitWire := by
  apply Fin.ext
  rfl

@[simp] private theorem sourceWireOfRetained_wireImage
    (result : IotaSeverResult source wire keep)
    (sourceWire : source.val.WireId) :
    result.sourceWireOfRetained (result.wireImage sourceWire)
        (retained_ne_fresh result sourceWire) =
      sourceWire := by
  apply Fin.ext
  rfl

private def inverseWire
    (result : IotaSeverResult source wire keep)
    (sourceWire : source.val.WireId) :
    result.inverseJoin.checked.val.WireId :=
  result.inverseJoin.wireImage (result.wireImage sourceWire)
    (retained_ne_fresh result sourceWire)

private def originalWire
    (result : IotaSeverResult source wire keep)
    (target : result.inverseJoin.checked.val.WireId) :
    source.val.WireId :=
  result.sourceWireOfRetained (result.rejoinSourceWire target)
    (result.rejoinSourceWire_survives target)

private def regionEquiv
    (result : IotaSeverResult source wire keep) :
    Data.Finite.FiniteEquiv source.val.RegionId
      result.inverseJoin.checked.val.RegionId where
  toFun := result.inverseRegion
  invFun := Fin.cast result.inverseJoin_regionCount
  left_inv := by
    intro region
    apply Fin.ext
    rfl
  right_inv := by
    intro region
    apply Fin.ext
    rfl

private def nodeEquiv
    (result : IotaSeverResult source wire keep) :
    Data.Finite.FiniteEquiv source.val.NodeId
      result.inverseJoin.checked.val.NodeId where
  toFun := result.inverseNode
  invFun := Fin.cast result.inverseJoin_nodeCount
  left_inv := by
    intro node
    apply Fin.ext
    rfl
  right_inv := by
    intro node
    apply Fin.ext
    rfl

private def wireEquiv
    (result : IotaSeverResult source wire keep) :
    Data.Finite.FiniteEquiv source.val.WireId
      result.inverseJoin.checked.val.WireId where
  toFun := result.inverseWire
  invFun := result.originalWire
  left_inv := by
    intro sourceWire
    unfold originalWire inverseWire
    calc
      result.sourceWireOfRetained
            (result.rejoinSourceWire
              (result.inverseJoin.wireImage
                (result.wireImage sourceWire) _)) _ =
          result.sourceWireOfRetained (result.wireImage sourceWire) _ := by
        congr 1
        exact result.rejoinSourceWire_wireImage
          (result.wireImage sourceWire) _
      _ = sourceWire :=
        result.sourceWireOfRetained_wireImage sourceWire
  right_inv := by
    intro target
    unfold inverseWire originalWire
    calc
      result.inverseJoin.wireImage
            (result.wireImage
              (result.sourceWireOfRetained
                (result.rejoinSourceWire target) _)) _ =
          result.inverseJoin.wireImage
            (result.rejoinSourceWire target) _ := by
        congr 1
      _ = target := result.inverseJoin_wireImage_sourceWire target

private def inverseEndpoint
    (result : IotaSeverResult source wire keep)
    (endpoint : CEndpoint source.val.nodeCount) :
    CEndpoint result.inverseJoin.checked.val.nodeCount :=
  ⟨result.inverseNode endpoint.node, endpoint.port⟩

private theorem inverseEndpoint_injective
    (result : IotaSeverResult source wire keep) :
    Function.Injective result.inverseEndpoint := by
  intro left right same
  cases left with
  | mk leftNode leftPort =>
      cases right with
      | mk rightNode rightPort =>
          have nodeSame : leftNode = rightNode := by
            apply Fin.ext
            exact congrArg (fun endpoint => endpoint.node.val) same
          have portSame : leftPort = rightPort :=
            congrArg (fun endpoint => endpoint.port) same
          subst rightNode
          subst rightPort
          rfl

@[simp] private theorem inverse_endpointImage
    (result : IotaSeverResult source wire keep)
    (endpoint : CEndpoint source.val.nodeCount) :
    result.inverseJoin.endpointImage (result.endpointImage endpoint) =
      result.inverseEndpoint endpoint := by
  cases endpoint
  congr

private theorem mem_map_injective
    {map : α → β} (injective : Function.Injective map)
    (value : α) (values : List α) :
    map value ∈ values.map map ↔ value ∈ values := by
  constructor
  · intro member
    obtain ⟨candidate, candidateMember, same⟩ :=
      List.mem_map.mp member
    exact (injective same).symm ▸ candidateMember
  · exact fun member => List.mem_map.mpr ⟨value, member, rfl⟩

private theorem inverse_region_table
    (result : IotaSeverResult source wire keep)
    (region : source.val.RegionId) :
    result.inverseJoin.checked.val.regions (result.inverseRegion region) =
      (source.val.regions region).rename result.regionEquiv := by
  rw [← inverse_regionImage, result.inverseJoin.region_generated,
    result.region_generated]
  cases source.val.regions region <;> rfl

private theorem inverse_node_table
    (result : IotaSeverResult source wire keep)
    (node : source.val.NodeId) :
    result.inverseJoin.checked.val.nodes (result.inverseNode node) =
      (source.val.nodes node).rename result.regionEquiv := by
  rw [← inverse_nodeImage, result.inverseJoin.node_generated,
    result.node_generated]
  cases source.val.nodes node <;> rfl

private theorem inverseEndpoint_corresponds
    (result : IotaSeverResult source wire keep)
    (endpoint : CEndpoint source.val.nodeCount)
    (required :
      endpoint.port ∈ source.val.requiredPorts endpoint.node) :
    PortCorresponds source.val result.inverseJoin.checked.val
      result.nodeEquiv endpoint (result.inverseEndpoint endpoint) := by
  unfold PortCorresponds
  constructor
  · rfl
  · simp only [inverseEndpoint]
    rw [result.inverse_node_table]
    cases data : source.val.nodes endpoint.node <;>
      simp [data, CNode.rename]
    rcases (by
      simpa [ConcreteDiagram.requiredPorts, data, eq_comm] using required) with
      ⟨index, _, port⟩
    exact ⟨index, port⟩

private theorem inverseEndpoint_mem
    (result : IotaSeverResult source wire keep)
    (sourceWire : source.val.WireId)
    (endpoint : CEndpoint source.val.nodeCount) :
    result.inverseEndpoint endpoint ∈
        (result.inverseJoin.checked.val.wires
          (result.inverseWire sourceWire)).endpoints ↔
      endpoint ∈ (source.val.wires sourceWire).endpoints := by
  unfold inverseWire
  rw [result.inverseJoin.wireImage_endpoints]
  by_cases same : sourceWire = wire
  · subst sourceWire
    rw [if_pos rfl, result.wireImage_endpoints, if_pos rfl,
      result.freshWire_endpoints, List.map_append,
      List.map_map, List.map_map]
    change
      result.inverseEndpoint endpoint ∈
          ((source.val.wires wire).endpoints.filter fun candidate =>
              decide (candidate ∈ keep)).map result.inverseEndpoint ++
            ((source.val.wires wire).endpoints.filter fun candidate =>
              decide (candidate ∉ keep)).map result.inverseEndpoint ↔
        endpoint ∈ (source.val.wires wire).endpoints
    rw [List.mem_append,
      mem_map_injective result.inverseEndpoint_injective endpoint
        ((source.val.wires wire).endpoints.filter fun candidate =>
          decide (candidate ∈ keep)),
      mem_map_injective result.inverseEndpoint_injective endpoint
        ((source.val.wires wire).endpoints.filter fun candidate =>
          decide (candidate ∉ keep))]
    by_cases kept : endpoint ∈ keep <;> simp [kept]
  · have splitDifferent :
        result.wireImage sourceWire ≠ result.wireImage wire := by
      intro equal
      apply same
      apply Fin.ext
      simpa [IotaSeverResult.wireImage, checkedWire] using
        congrArg Fin.val equal
    rw [if_neg splitDifferent, result.wireImage_endpoints,
      if_neg same, List.map_map]
    change
      result.inverseEndpoint endpoint ∈
          (source.val.wires sourceWire).endpoints.map
            result.inverseEndpoint ↔
        endpoint ∈ (source.val.wires sourceWire).endpoints
    exact
      mem_map_injective result.inverseEndpoint_injective endpoint
        (source.val.wires sourceWire).endpoints

/--
The canonical inverse join differs from the sever source only by endpoint
list order, which raw concrete isomorphism intentionally treats as
nonsemantic.
-/
def inverseIso
    {definitions : List (List Sig)}
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {keep : List (CEndpoint source.val.nodeCount)}
    (result : IotaSeverResult source wire keep) :
    ConcreteIso source.val result.inverseJoin.checked.val where
  regions := result.regionEquiv
  nodes := result.nodeEquiv
  wires := result.wireEquiv
  root := by
    change
      result.inverseRegion source.val.root =
        result.inverseJoin.checked.val.root
    rw [← inverse_regionImage, ← result.root_generated,
      ← result.inverseJoin.root_generated]
  region_table := result.inverse_region_table
  node_table := result.inverse_node_table
  wire_signature := by
    intro sourceWire
    change
      (result.inverseJoin.checked.val.wires
        (result.inverseWire sourceWire)).sig =
        (source.val.wires sourceWire).sig
    unfold inverseWire
    rw [result.inverseJoin.wireImage_signature,
      result.wireImage_signature]
  wire_scope := by
    intro sourceWire
    change
      (result.inverseJoin.checked.val.wires
          (result.inverseWire sourceWire)).scope =
        result.inverseRegion (source.val.wires sourceWire).scope
    unfold inverseWire
    rw [result.inverseJoin.wireImage_scope,
      result.wireImage_scope, inverse_regionImage]
  endpoint_forward := by
    intro sourceWire endpoint incident
    refine
      ⟨result.inverseEndpoint endpoint,
        (result.inverseEndpoint_mem sourceWire endpoint).mpr incident, ?_⟩
    exact
      result.inverseEndpoint_corresponds endpoint
        (ConcreteDiagram.incident_port_required definitions source.val
          source.property sourceWire endpoint incident)
  endpoint_backward := by
    intro sourceWire candidate incident
    let endpoint : CEndpoint source.val.nodeCount :=
      ⟨Fin.cast result.inverseJoin_nodeCount candidate.node, candidate.port⟩
    have endpointImage : result.inverseEndpoint endpoint = candidate := by
      cases candidate
      congr
    have mappedIncident :
        result.inverseEndpoint endpoint ∈
          (result.inverseJoin.checked.val.wires
            (result.inverseWire sourceWire)).endpoints :=
      endpointImage ▸ incident
    have sourceIncident :
        endpoint ∈ (source.val.wires sourceWire).endpoints :=
      (result.inverseEndpoint_mem sourceWire endpoint).mp mappedIncident
    refine ⟨endpoint, sourceIncident, ?_⟩
    have corresponds :=
      result.inverseEndpoint_corresponds endpoint
        (ConcreteDiagram.incident_port_required definitions source.val
          source.property sourceWire endpoint sourceIncident)
    exact endpointImage ▸ corresponds

end IotaSeverResult

/--
Merge the inner individual wire into the retained outer wire and delete the
inner identifier. Scope comparability is intentionally rule-owned.
-/
def joinIota
    (source : CheckedDiagram definitions)
    (outer inner : source.val.WireId) :
    Except Error (IotaJoinResult source outer inner) := by
  if same : outer = inner then
    exact .error .sameWire
  else if outerSignature : (source.val.wires outer).sig = .iota then
    if innerSignature : (source.val.wires inner).sig = .iota then
      let candidate := iotaJoinCandidate source outer inner
      match accepted :
          ConcreteDiagram.checkWellFormed definitions candidate with
      | .error error =>
          exact .error (.wellFormed error)
      | .ok checked =>
          exact .ok
            (IotaJoinResult.mk checked same outerSignature innerSignature
              (ConcreteDiagram.checkWellFormed_preserves_input accepted))
    else
      exact .error (.expectedIota inner.val)
  else
    exact .error (.expectedIota outer.val)

end ConcreteWireQuantifier

end VisualProof
