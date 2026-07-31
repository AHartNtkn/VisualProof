import VisualProof.Diagram.Concrete.WirePrimitive.Arguments

namespace VisualProof

namespace ConcreteWirePrimitive

open ConcreteWireQuantifier
open WirePrimitive

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

private inductive LeafShape
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

private def LeafShape.ports :
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
  (Data.Finite.allFin result.sites.sites.length).map fun site =>
    Internal.checkedNode result.generated (leafNode result.plan site)

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
  Internal.checkedRegion result.generated
    (leafRegion source (source.val.wires wire).scope)

theorem siteCount
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : LeafResult source wire) :
    result.sites.sites.length =
      (source.val.wires wire).endpoints.length :=
  result.sites.length

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

private def checkedSelection
    (source : CheckedDiagram definitions)
    (nodes : List source.val.NodeId)
    (scope : source.val.RegionId) :
    Except LeafError Unit := do
  if nodes.isEmpty then
    throw .emptySelection
  if !nodes.Nodup then
    throw .duplicateSelection
  if !(nodes.all fun node =>
      source.val.Encloses scope (source.val.nodes node).region) then
    throw .scopeDoesNotEnclose
  pure ()

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
      checkedSelection source selected scope
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
      checkedSelection source selected scope
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
      checkedSelection source selected scope
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
                  scope := scope
                  targetArguments := arguments
                  arguments := collectedAt collected }
              buildAbstract source spec
      | _ => throw .wrongNodeKind

end ConcreteWirePrimitive

end VisualProof
