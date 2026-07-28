import VisualProof.Diagram.Concrete.ElaborationInvariance
import VisualProof.Diagram.Concrete.IdentityNormalization
import VisualProof.Diagram.Concrete.Subgraph.Extract

namespace VisualProof

universe u

namespace Var

/-- Equality of intrinsically typed variables is structurally decidable. -/
def decEq : (left right : Var ctx sig) → Decidable (left = right)
  | .here, .here => isTrue rfl
  | .here, .there _ => isFalse fun equality => by cases equality
  | .there _, .here => isFalse fun equality => by cases equality
  | .there left, .there right =>
      match decEq left right with
      | isTrue equality => isTrue (by cases equality; rfl)
      | isFalse different => isFalse fun equality => by
          cases equality
          exact different rfl

instance : DecidableEq (Var ctx sig) := decEq

end Var

namespace Vars

/--
One source class and one target variable occupy the same ordered boundary
position. This is structural evidence about the supplied attachment tuple.
-/
inductive Paired :
    {args : List Sig} → Vars source args → Vars target args →
      {sig : Sig} → Var source sig → Var target sig → Prop
  | head :
      Paired (.cons source sourceTail) (.cons target targetTail) source target
  | tail :
      Paired sourceTail targetTail source target →
        Paired (.cons otherSource sourceTail) (.cons otherTarget targetTail)
          source target

/-- Equal ordered boundary tuples give equal values at paired positions. -/
theorem value_eq_of_paired
    {sources : Vars source args} {targets : Vars target args}
    {sourceVar : Var source sig} {targetVar : Var target sig}
    (paired : Paired sources targets sourceVar targetVar)
    (left : Env pre source) (right : Env pre target)
    (valuesEqual : Vars.denote left sources = Vars.denote right targets) :
    left sig sourceVar = right sig targetVar := by
  induction paired with
  | head => exact congrArg Prod.fst valuesEqual
  | tail _ induction =>
      exact induction (congrArg Prod.snd valuesEqual)

end Vars

/--
An ordered boundary attachment. `positions` names every external position;
`classMap` chooses one representative target wire for each aliased source
class. Intrinsic typing is the signature check and makes capture impossible.
-/
structure SpliceAttachment (fragment : OpenDiagram defs args)
    (target : List Sig) where
  positions : Vars target args
  classMap : WireRenaming fragment.classes target
  representative_position :
    ∀ {sig} (fiber : Var fragment.classes sig),
      Vars.Paired fragment.boundary positions fiber (classMap fiber)

namespace SpliceAttachment

private def buildIdentities (classMap : WireRenaming source target) :
    {args : List Sig} →
      Vars source args → Vars target args → ItemSeq defs target
  | [], .nil, .nil => .nil
  | _ :: _, .cons source sourceTail, .cons destination destinationTail =>
      if classMap source = destination then
        buildIdentities classMap sourceTail destinationTail
      else
        .cons (Item.binaryIdentity _ (classMap source) destination)
          (buildIdentities classMap sourceTail destinationTail)

private theorem buildIdentities_denote
    (classMap : WireRenaming source target)
    (sources : Vars source args) (targets : Vars target args)
    (pre : PreModel.{u}) (definitionEnv : DefinitionEnv pre defs)
    (env : Env pre target) :
    denoteItemSeq pre definitionEnv env
        (buildIdentities classMap sources targets) ↔
      Vars.denote (Env.comp env classMap) sources =
        Vars.denote env targets := by
  induction sources with
  | nil =>
      cases targets
      simp [buildIdentities, Vars.denote]
  | cons source sourceTail induction =>
      cases targets with
      | cons destination destinationTail =>
          by_cases equality : classMap source = destination
          · simp only [buildIdentities, equality, ↓reduceIte,
              Vars.denote_cons, Env.comp]
            simpa only [PreModel.Args, Prod.mk.injEq, true_and] using
              induction destinationTail
          · simp only [buildIdentities, equality, ↓reduceIte,
              denoteItemSeq_cons, Item.binaryIdentity,
              denoteItem_identity, List.map_cons, List.map_nil,
              AllEqual.pair, Vars.denote_cons, Env.comp]
            simp only [PreModel.Args, Prod.mk.injEq]
            exact and_congr Iff.rfl (induction destinationTail)

/--
Materialize only mismatches between an ordered attachment and its class
representative. Repeated source positions attached to distinct target wires
therefore create an identity; exact aliases create no node. Task 6 alone owns
normalization of the resulting identities.
-/
def identities (attachment : SpliceAttachment fragment target) :
    ItemSeq defs target :=
  buildIdentities attachment.classMap fragment.boundary attachment.positions

private theorem identities_denote
    (attachment : SpliceAttachment fragment target)
    (pre : PreModel.{u}) (definitionEnv : DefinitionEnv pre defs)
    (env : Env pre target) :
    denoteItemSeq pre definitionEnv env attachment.identities ↔
      Vars.denote (Env.comp env attachment.classMap) fragment.boundary =
        Vars.denote env attachment.positions := by
  exact buildIdentities_denote attachment.classMap fragment.boundary
    attachment.positions pre definitionEnv env

end SpliceAttachment

/--
Capture-avoiding intrinsic splice. The body is renamed into the visible hole
context and explicit boundary identities are conjoined there.
-/
def intrinsicSplice (fragment : OpenDiagram defs args)
    (attachment : SpliceAttachment fragment target) :
    Region defs target :=
  Region.surround attachment.identities
    (fragment.body.renameWires attachment.classMap) .nil

/-- Place a capture-avoiding splice through a genuine one-hole context. -/
def intrinsicSpliceIn (context : DiagramContext defs target outer)
    (fragment : OpenDiagram defs args)
    (attachment : SpliceAttachment fragment target) :
    Region defs outer :=
  context.fill (intrinsicSplice fragment attachment)

/--
Splice denotes exactly the open fragment at the ordered supplied values.
The reverse direction uses boundary surjectivity to identify the existential
class environment with the representative environment; it is not definitional.
-/
theorem denote_intrinsicSplice
    (pre : PreModel.{u}) (definitionEnv : DefinitionEnv pre defs)
    (env : Env pre target) (fragment : OpenDiagram defs args)
    (attachment : SpliceAttachment fragment target) :
    denoteRegion pre definitionEnv env (intrinsicSplice fragment attachment) ↔
      denoteOpen pre definitionEnv fragment
        (Vars.denote env attachment.positions) := by
  rw [intrinsicSplice, Region.denote_surround,
    SpliceAttachment.identities_denote,
    denoteRegion_renameWires]
  simp only [denoteItemSeq_nil, and_true]
  constructor
  · rintro ⟨boundaryEqual, body⟩
    exact ⟨Env.comp env attachment.classMap, boundaryEqual, body⟩
  · rintro ⟨classEnv, boundaryEqual, body⟩
    have environmentsEqual :
        classEnv = Env.comp env attachment.classMap := by
      funext sig fiber
      exact Vars.value_eq_of_paired
        (attachment.representative_position fiber) classEnv env boundaryEqual
    subst classEnv
    exact ⟨boundaryEqual, body⟩

/--
Equivalent open fragments remain equivalent after splice at every context
depth; polarity is discharged by `context_equiv`.
-/
theorem denote_intrinsicSplice_in_context
    (context : DiagramContext defs target outer)
    (pre : PreModel.{u}) (definitionEnv : DefinitionEnv pre defs)
    (left : OpenDiagram defs leftArgs)
    (leftAttachment : SpliceAttachment left target)
    (right : OpenDiagram defs rightArgs)
    (rightAttachment : SpliceAttachment right target)
    (equivalent : ∀ env : Env pre target,
      denoteOpen pre definitionEnv left
          (Vars.denote env leftAttachment.positions) ↔
        denoteOpen pre definitionEnv right
          (Vars.denote env rightAttachment.positions))
    (env : Env pre outer) :
    denoteRegion pre definitionEnv env
        (intrinsicSpliceIn context left leftAttachment) ↔
      denoteRegion pre definitionEnv env
        (intrinsicSpliceIn context right rightAttachment) := by
  apply context_equiv context pre definitionEnv
  intro holeEnv
  rw [denote_intrinsicSplice, denote_intrinsicSplice]
  exact equivalent holeEnv

/-- One concrete binary identity requested by a distinct attachment pair. -/
structure ConcreteIdentityRequest
    (diagram : ConcreteDiagram definitionCount) where
  sig : Sig
  representative : diagram.WireId
  target : diagram.WireId
  deriving DecidableEq

def concreteRepresentativePosition
    (fragment : CheckedOpenDiagram definitions)
    (wire : fragment.val.diagram.WireId)
    (member : wire ∈ fragment.val.boundary) :
    Fin fragment.val.boundary.length :=
  DenseList.index fragment.val.boundary wire member

def concreteRepresentativeTarget
    (site : RemovalResult occurrence)
    (fragment : CheckedOpenDiagram definitions)
    (target :
      Fin fragment.val.boundary.length →
        site.complement.val.WireId)
    (wire : fragment.val.diagram.WireId)
    (member : wire ∈ fragment.val.boundary) :
    site.complement.val.WireId :=
  target (concreteRepresentativePosition fragment wire member)

/-- Canonical deduplicated identity requests computed from positional targets. -/
def computedIdentityRequests
    (site : RemovalResult occurrence)
    (fragment : CheckedOpenDiagram definitions)
    (target :
      Fin fragment.val.boundary.length →
        site.complement.val.WireId) :
    List (ConcreteIdentityRequest site.complement.val) :=
  ((Data.Finite.allFin fragment.val.boundary.length).filterMap fun position =>
    let source := fragment.val.boundary.get position
    let representative := concreteRepresentativeTarget site fragment target
      source (List.get_mem fragment.val.boundary position)
    let destination := target position
    if representative = destination then
      none
    else
      some
        { sig := (fragment.val.diagram.wires source).sig
          representative := representative
          target := destination }).eraseDups

/--
Concrete attachments are indexed by genuine generated boundary positions.
Typing and enclosure are explicit, validated data; no target search occurs.
-/
structure ConcreteSpliceAttachment
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (site : RemovalResult occurrence)
    (fragment : CheckedOpenDiagram definitions) where
  target :
    Fin fragment.val.boundary.length →
      site.complement.val.WireId
  signature :
    ∀ position,
      (site.complement.val.wires (target position)).sig =
        (fragment.val.diagram.wires
          (fragment.val.boundary.get position)).sig
  scope :
    ∀ position,
      site.complement.val.Encloses
        (site.complement.val.wires (target position)).scope
        site.site
  identityRequests : List (ConcreteIdentityRequest site.complement.val)
  identityRequests_nodup : identityRequests.Nodup
  identityRequests_exact :
    identityRequests = computedIdentityRequests site fragment target

/-- Executably validate explicit target positions into a typed attachment. -/
def checkConcreteSpliceAttachment
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (site : RemovalResult occurrence)
    (fragment : CheckedOpenDiagram definitions)
    (target :
      Fin fragment.val.boundary.length →
        site.complement.val.WireId) :
    Option (ConcreteSpliceAttachment site fragment) :=
  if signature :
      ∀ position,
        (site.complement.val.wires (target position)).sig =
          (fragment.val.diagram.wires
            (fragment.val.boundary.get position)).sig then
    if scope :
        ∀ position,
          site.complement.val.Encloses
            (site.complement.val.wires (target position)).scope
            site.site then
      let identities := computedIdentityRequests site fragment target
      some
        { target := target
          signature := signature
          scope := scope
          identityRequests := identities
          identityRequests_nodup := Data.Finite.eraseDups_nodup _
          identityRequests_exact := rfl }
    else
      none
  else
    none

theorem checkConcreteSpliceAttachment_target
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    (site : RemovalResult occurrence)
    (fragment : CheckedOpenDiagram definitions)
    (target :
      Fin fragment.val.boundary.length →
        site.complement.val.WireId)
    (attachment : ConcreteSpliceAttachment site fragment)
    (accepted :
      checkConcreteSpliceAttachment site fragment target =
        some attachment) :
    attachment.target = target := by
  simp only [checkConcreteSpliceAttachment] at accepted
  split at accepted
  · split at accepted
    · have same := Option.some.inj accepted
      cases same
      rfl
    · contradiction
  · contradiction

namespace ConcreteSpliceAttachment

/-- The first actual boundary position of a source class. -/
def representativePosition
    (attachment : ConcreteSpliceAttachment site fragment)
    (wire : fragment.val.diagram.WireId)
    (member : wire ∈ fragment.val.boundary) :
    Fin fragment.val.boundary.length :=
  DenseList.index fragment.val.boundary wire member

/-- Every source class chooses a representative from its supplied positions. -/
def representativeTarget
    (attachment : ConcreteSpliceAttachment site fragment)
    (wire : fragment.val.diagram.WireId)
    (member : wire ∈ fragment.val.boundary) :
    site.complement.val.WireId :=
  attachment.target (attachment.representativePosition wire member)

theorem identityRequests_mem_iff
    (attachment : ConcreteSpliceAttachment site fragment)
    (request : ConcreteIdentityRequest site.complement.val) :
    request ∈ attachment.identityRequests ↔
      request ∈ computedIdentityRequests site fragment attachment.target := by
  rw [attachment.identityRequests_exact]

def fragmentRegions
    (attachment : ConcreteSpliceAttachment site fragment) :
    List fragment.val.diagram.RegionId :=
  fragment.val.diagram.regionsList.filter fun region =>
    decide (region ≠ fragment.val.diagram.root)

def fragmentInternalWires
    (attachment : ConcreteSpliceAttachment site fragment) :
    List fragment.val.diagram.WireId :=
  fragment.val.diagram.wiresList.filter fun wire =>
    decide (wire ∉ fragment.val.boundary)

abbrev regionCount
    (attachment : ConcreteSpliceAttachment site fragment) : Nat :=
  site.complement.val.regionCount + attachment.fragmentRegions.length

abbrev nodeCount
    (attachment : ConcreteSpliceAttachment site fragment) : Nat :=
  site.complement.val.nodeCount +
    (fragment.val.diagram.nodeCount + attachment.identityRequests.length)

abbrev wireCount
    (attachment : ConcreteSpliceAttachment site fragment) : Nat :=
  site.complement.val.wireCount + attachment.fragmentInternalWires.length

def hostRegion
    (attachment : ConcreteSpliceAttachment site fragment)
    (region : site.complement.val.RegionId) :
    Fin attachment.regionCount :=
  Fin.castAdd attachment.fragmentRegions.length region

def freshRegion
    (attachment : ConcreteSpliceAttachment site fragment)
    (region : Fin attachment.fragmentRegions.length) :
    Fin attachment.regionCount :=
  Fin.natAdd site.complement.val.regionCount region

theorem hostRegion_ne_freshRegion
    (attachment : ConcreteSpliceAttachment site fragment)
    (hostId : site.complement.val.RegionId)
    (freshId : Fin attachment.fragmentRegions.length) :
    attachment.hostRegion hostId ≠ attachment.freshRegion freshId := by
  intro equality
  have values := congrArg Fin.val equality
  simp [hostRegion, freshRegion] at values
  have bound := hostId.isLt
  omega

/-- The fragment root is identified with the site; all other regions are fresh. -/
def fragmentRegion
    (attachment : ConcreteSpliceAttachment site fragment)
    (region : fragment.val.diagram.RegionId) :
    Fin attachment.regionCount :=
  if root : region = fragment.val.diagram.root then
    attachment.hostRegion site.site
  else
    attachment.freshRegion
      (DenseList.index attachment.fragmentRegions region (by
        simp [fragmentRegions, ConcreteDiagram.regionsList,
          Data.Finite.mem_allFin, root]))

def hostNode
    (attachment : ConcreteSpliceAttachment site fragment)
    (node : site.complement.val.NodeId) :
    Fin attachment.nodeCount :=
  Fin.castAdd
    (fragment.val.diagram.nodeCount + attachment.identityRequests.length)
    node

def fragmentNode
    (attachment : ConcreteSpliceAttachment site fragment)
    (node : fragment.val.diagram.NodeId) :
    Fin attachment.nodeCount :=
  ⟨site.complement.val.nodeCount + node.val, by
    have bound := node.isLt
    simp only [nodeCount]
    omega⟩

def identityNode
    (attachment : ConcreteSpliceAttachment site fragment)
    (node : Fin attachment.identityRequests.length) :
    Fin attachment.nodeCount :=
  ⟨site.complement.val.nodeCount + fragment.val.diagram.nodeCount + node.val, by
    have bound := node.isLt
    simp only [nodeCount]
    omega⟩

theorem hostNode_ne_fragmentNode
    (attachment : ConcreteSpliceAttachment site fragment)
    (hostId : site.complement.val.NodeId)
    (fragmentId : fragment.val.diagram.NodeId) :
    attachment.hostNode hostId ≠ attachment.fragmentNode fragmentId := by
  intro equality
  have values := congrArg Fin.val equality
  simp [hostNode, fragmentNode] at values
  have bound := hostId.isLt
  omega

theorem hostNode_ne_identityNode
    (attachment : ConcreteSpliceAttachment site fragment)
    (hostId : site.complement.val.NodeId)
    (identityId : Fin attachment.identityRequests.length) :
    attachment.hostNode hostId ≠ attachment.identityNode identityId := by
  intro equality
  have values := congrArg Fin.val equality
  simp [hostNode, identityNode] at values
  have bound := hostId.isLt
  omega

theorem fragmentNode_ne_identityNode
    (attachment : ConcreteSpliceAttachment site fragment)
    (fragmentId : fragment.val.diagram.NodeId)
    (identityId : Fin attachment.identityRequests.length) :
    attachment.fragmentNode fragmentId ≠
      attachment.identityNode identityId := by
  intro equality
  have values := congrArg Fin.val equality
  simp [fragmentNode, identityNode] at values
  have bound := fragmentId.isLt
  omega

def hostWire
    (attachment : ConcreteSpliceAttachment site fragment)
    (wire : site.complement.val.WireId) :
    Fin attachment.wireCount :=
  Fin.castAdd attachment.fragmentInternalWires.length wire

def freshWire
    (attachment : ConcreteSpliceAttachment site fragment)
    (wire : Fin attachment.fragmentInternalWires.length) :
    Fin attachment.wireCount :=
  Fin.natAdd site.complement.val.wireCount wire

theorem hostWire_injective
    (attachment : ConcreteSpliceAttachment site fragment) :
    Function.Injective attachment.hostWire := by
  intro left right same
  apply Fin.ext
  simpa [hostWire] using congrArg Fin.val same

theorem hostWire_ne_freshWire
    (attachment : ConcreteSpliceAttachment site fragment)
    (hostId : site.complement.val.WireId)
    (freshId : Fin attachment.fragmentInternalWires.length) :
    attachment.hostWire hostId ≠ attachment.freshWire freshId := by
  intro equality
  have values := congrArg Fin.val equality
  simp [hostWire, freshWire] at values
  have bound := hostId.isLt
  omega

/--
Boundary classes reconnect to their representative actual target. Every
nonboundary fragment wire receives a disjoint fresh identifier.
-/
def fragmentWire
    (attachment : ConcreteSpliceAttachment site fragment)
    (wire : fragment.val.diagram.WireId) :
    Fin attachment.wireCount :=
  if boundary : wire ∈ fragment.val.boundary then
    attachment.hostWire (attachment.representativeTarget wire boundary)
  else
    attachment.freshWire
      (DenseList.index attachment.fragmentInternalWires wire (by
        simp [fragmentInternalWires, ConcreteDiagram.wiresList,
          Data.Finite.mem_allFin, boundary]))

/-- Rename one retained host endpoint into the enlarged node carrier. -/
def hostEndpoint
    (attachment : ConcreteSpliceAttachment site fragment)
    (endpoint : CEndpoint site.complement.val.nodeCount) :
    CEndpoint attachment.nodeCount :=
  ⟨attachment.hostNode endpoint.node, endpoint.port⟩

/-- Rename one copied fragment endpoint into its disjoint fresh node carrier. -/
def fragmentEndpoint
    (attachment : ConcreteSpliceAttachment site fragment)
    (endpoint : CEndpoint fragment.val.diagram.nodeCount) :
    CEndpoint attachment.nodeCount :=
  ⟨attachment.fragmentNode endpoint.node, endpoint.port⟩

def regionTable
    (attachment : ConcreteSpliceAttachment site fragment) :
    Fin attachment.regionCount → CRegion attachment.regionCount :=
  Fin.addCases
    (fun region =>
      match site.complement.val.regions region with
      | .sheet => .sheet
      | .cut parent => .cut (attachment.hostRegion parent))
    (fun fresh =>
      let source := attachment.fragmentRegions.get fresh
      match fragment.val.diagram.regions source with
      | .sheet => .sheet
      | .cut parent => .cut (attachment.fragmentRegion parent))

def renameHostNode
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {site : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment site fragment)
    (node : site.complement.val.NodeId) :
    CNode attachment.regionCount definitions.length :=
  match site.complement.val.nodes node with
  | .atom region args => .atom (attachment.hostRegion region) args
  | .ref region definition args =>
      .ref (attachment.hostRegion region) definition args
  | .identity region sig arity =>
      .identity (attachment.hostRegion region) sig arity

def renameFragmentNode
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {site : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment site fragment)
    (node : fragment.val.diagram.NodeId) :
    CNode attachment.regionCount definitions.length :=
  match fragment.val.diagram.nodes node with
  | .atom region args => .atom (attachment.fragmentRegion region) args
  | .ref region definition args =>
      .ref (attachment.fragmentRegion region) definition args
  | .identity region sig arity =>
      .identity (attachment.fragmentRegion region) sig arity

def nodeTable
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {site : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment site fragment) :
    Fin attachment.nodeCount →
      CNode attachment.regionCount definitions.length :=
  Fin.addCases
    (fun node => renameHostNode attachment node)
    (Fin.addCases
      (fun node => renameFragmentNode attachment node)
      (fun identity =>
        let request := attachment.identityRequests.get identity
        .identity (attachment.hostRegion site.site) request.sig 2))

/-- Every copied fragment incidence, keyed by its mapped destination wire. -/
def fragmentEndpointOccurrences
    (attachment : ConcreteSpliceAttachment site fragment) :
    List (Fin attachment.wireCount × CEndpoint attachment.nodeCount) :=
  fragment.val.diagram.endpointOccurrences.map fun occurrence =>
    (attachment.fragmentWire occurrence.1,
      attachment.fragmentEndpoint occurrence.2)

/-- The two concrete ports of every requested attachment identity. -/
def identityEndpointOccurrences
    (attachment : ConcreteSpliceAttachment site fragment) :
    List (Fin attachment.wireCount × CEndpoint attachment.nodeCount) :=
  (Data.Finite.allFin attachment.identityRequests.length).flatMap fun index =>
    let request := attachment.identityRequests.get index
    let node := attachment.identityNode index
    [(attachment.hostWire request.representative,
        ⟨node, .identity 0⟩),
      (attachment.hostWire request.target,
        ⟨node, .identity 1⟩)]

def generatedEndpoints
    (attachment : ConcreteSpliceAttachment site fragment)
    (wire : Fin attachment.wireCount) :
    List (CEndpoint attachment.nodeCount) :=
  (attachment.fragmentEndpointOccurrences ++
      attachment.identityEndpointOccurrences).filterMap fun occurrence =>
    if occurrence.1 = wire then some occurrence.2 else none

theorem fragmentEndpoint_mem_generated
    (attachment : ConcreteSpliceAttachment site fragment)
    (_empty : attachment.identityRequests = [])
    (source : fragment.val.diagram.WireId)
    (endpoint : CEndpoint fragment.val.diagram.nodeCount)
    (incident :
      endpoint ∈ (fragment.val.diagram.wires source).endpoints) :
    attachment.fragmentEndpoint endpoint ∈
      attachment.generatedEndpoints (attachment.fragmentWire source) := by
  apply List.mem_filterMap.mpr
  refine
    ⟨(attachment.fragmentWire source,
        attachment.fragmentEndpoint endpoint), ?_, ?_⟩
  · apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨(source, endpoint), ?_, rfl⟩
    simp [ConcreteDiagram.endpointOccurrences,
      ConcreteDiagram.wiresList, Data.Finite.mem_allFin, incident]
  · simp

theorem generatedEndpoint_origin
    (attachment : ConcreteSpliceAttachment site fragment)
    (empty : attachment.identityRequests = [])
    (wire : Fin attachment.wireCount)
    (endpoint : CEndpoint attachment.nodeCount)
    (member : endpoint ∈ attachment.generatedEndpoints wire) :
    ∃ source : fragment.val.diagram.WireId,
      ∃ sourceEndpoint : CEndpoint fragment.val.diagram.nodeCount,
        sourceEndpoint ∈
            (fragment.val.diagram.wires source).endpoints ∧
          attachment.fragmentWire source = wire ∧
          attachment.fragmentEndpoint sourceEndpoint = endpoint := by
  unfold generatedEndpoints at member
  rcases List.mem_filterMap.mp member with
    ⟨mappedOccurrence, occurrenceMember, filtered⟩
  have identityLength : attachment.identityRequests.length = 0 := by
    simpa using congrArg List.length empty
  have identityOccurrencesEmpty :
      attachment.identityEndpointOccurrences = [] := by
    unfold identityEndpointOccurrences
    simp [identityLength]
  have fragmentMember :
      mappedOccurrence ∈ attachment.fragmentEndpointOccurrences := by
    simpa [identityOccurrencesEmpty] using occurrenceMember
  unfold fragmentEndpointOccurrences at fragmentMember
  rcases List.mem_map.mp fragmentMember with
    ⟨sourceOccurrence, sourceMember, mappedEquality⟩
  rcases sourceOccurrence with ⟨source, sourceEndpoint⟩
  have incident :
      sourceEndpoint ∈
        (fragment.val.diagram.wires source).endpoints := by
    simpa [ConcreteDiagram.endpointOccurrences,
      ConcreteDiagram.wiresList, Data.Finite.mem_allFin] using sourceMember
  subst mappedOccurrence
  change
    (if attachment.fragmentWire source = wire then
        some (attachment.fragmentEndpoint sourceEndpoint)
      else none) = some endpoint at filtered
  split at filtered
  · rename_i mappedWire
    exact
      ⟨source, sourceEndpoint, incident, mappedWire,
        Option.some.inj filtered⟩
  · contradiction

def wireTable
    (attachment : ConcreteSpliceAttachment site fragment) :
    Fin attachment.wireCount →
      CWire attachment.regionCount attachment.nodeCount :=
  Fin.addCases
    (fun wire =>
      let source := site.complement.val.wires wire
      { sig := source.sig
        scope := attachment.hostRegion source.scope
        endpoints :=
          source.endpoints.map attachment.hostEndpoint ++
            attachment.generatedEndpoints (attachment.hostWire wire) })
    (fun fresh =>
      let sourceId := attachment.fragmentInternalWires.get fresh
      let source := fragment.val.diagram.wires sourceId
      { sig := source.sig
        scope := attachment.fragmentRegion source.scope
        endpoints :=
          attachment.generatedEndpoints
            (Fin.natAdd site.complement.val.wireCount fresh) })

/--
The concrete splice candidate copies every complement and fragment table,
reconnects boundary classes to actual targets, and materializes requested
identities. No normalization is performed.
-/
def diagram
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {site : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment site fragment) :
    ConcreteDiagram definitions.length where
  regionCount := attachment.regionCount
  nodeCount := attachment.nodeCount
  wireCount := attachment.wireCount
  root := attachment.hostRegion site.complement.val.root
  regions := regionTable attachment
  nodes := nodeTable attachment
  wires := wireTable attachment

@[simp] theorem diagram_wire_hostWire
    (attachment : ConcreteSpliceAttachment site fragment)
    (wire : site.complement.val.WireId) :
    (attachment.diagram.wires (attachment.hostWire wire)).sig =
      (site.complement.val.wires wire).sig := by
  unfold diagram wireTable hostWire
  simp only [Fin.addCases_left]

@[simp] theorem diagram_wire_hostWire_scope
    (attachment : ConcreteSpliceAttachment site fragment)
    (wire : site.complement.val.WireId) :
    (attachment.diagram.wires (attachment.hostWire wire)).scope =
      attachment.hostRegion (site.complement.val.wires wire).scope := by
  unfold diagram wireTable hostWire
  simp only [Fin.addCases_left]

@[simp] theorem diagram_wire_freshWire_scope
    (attachment : ConcreteSpliceAttachment site fragment)
    (fresh : Fin attachment.fragmentInternalWires.length) :
    (attachment.diagram.wires (attachment.freshWire fresh)).scope =
      attachment.fragmentRegion
        (fragment.val.diagram.wires
          (attachment.fragmentInternalWires.get fresh)).scope := by
  unfold diagram wireTable freshWire
  simp only [Fin.addCases_right]

@[simp] theorem diagram_node_hostNode
    (attachment : ConcreteSpliceAttachment site fragment)
    (node : site.complement.val.NodeId) :
    attachment.diagram.nodes (attachment.hostNode node) =
      renameHostNode attachment node := by
  unfold diagram nodeTable hostNode
  simp only [Fin.addCases_left]

@[simp] theorem diagram_node_fragmentNode
    (attachment : ConcreteSpliceAttachment site fragment)
    (node : fragment.val.diagram.NodeId) :
    attachment.diagram.nodes (attachment.fragmentNode node) =
      renameFragmentNode attachment node := by
  have allocated :
      attachment.fragmentNode node =
        Fin.natAdd site.complement.val.nodeCount
          (Fin.castAdd attachment.identityRequests.length node) :=
    Fin.ext (by simp [fragmentNode])
  unfold diagram
  rw [allocated]
  unfold nodeTable
  simp only [Fin.addCases_right, Fin.addCases_left]

@[simp] theorem diagram_node_hostNode_region
    (attachment : ConcreteSpliceAttachment site fragment)
    (node : site.complement.val.NodeId) :
  (attachment.diagram.nodes (attachment.hostNode node)).region =
      attachment.hostRegion (site.complement.val.nodes node).region := by
  rw [diagram_node_hostNode]
  cases data : site.complement.val.nodes node <;>
    simp [renameHostNode, CNode.region, data]

@[simp] theorem diagram_node_fragmentNode_region
    (attachment : ConcreteSpliceAttachment site fragment)
    (node : fragment.val.diagram.NodeId) :
  (attachment.diagram.nodes (attachment.fragmentNode node)).region =
      attachment.fragmentRegion (fragment.val.diagram.nodes node).region := by
  rw [diagram_node_fragmentNode]
  cases data : fragment.val.diagram.nodes node <;>
    simp [renameFragmentNode, CNode.region, data]

@[simp] theorem diagram_node_identityNode
    (attachment : ConcreteSpliceAttachment site fragment)
    (identity : Fin attachment.identityRequests.length) :
    attachment.diagram.nodes (attachment.identityNode identity) =
      .identity (attachment.hostRegion site.site)
        (attachment.identityRequests.get identity).sig 2 := by
  have allocated :
      attachment.identityNode identity =
        Fin.natAdd site.complement.val.nodeCount
          (Fin.natAdd fragment.val.diagram.nodeCount identity) :=
    Fin.ext (by simp [identityNode]; omega)
  unfold diagram
  rw [allocated]
  unfold nodeTable
  simp only [Fin.addCases_right]

@[simp] theorem diagram_region_hostRegion
    (attachment : ConcreteSpliceAttachment site fragment)
    (region : site.complement.val.RegionId) :
    attachment.diagram.regions (attachment.hostRegion region) =
      mapRegion attachment.hostRegion
        (site.complement.val.regions region) := by
  unfold diagram regionTable hostRegion
  simp only [Fin.addCases_left]
  cases data : site.complement.val.regions region <;>
    simp [mapRegion, data]

@[simp] theorem diagram_region_freshRegion
    (attachment : ConcreteSpliceAttachment site fragment)
    (fresh : Fin attachment.fragmentRegions.length) :
    attachment.diagram.regions (attachment.freshRegion fresh) =
      mapRegion attachment.fragmentRegion
        (fragment.val.diagram.regions
          (attachment.fragmentRegions.get fresh)) := by
  unfold diagram regionTable freshRegion
  simp only [Fin.addCases_right]
  cases data :
      fragment.val.diagram.regions
        (attachment.fragmentRegions.get fresh) <;>
    simp [mapRegion, data]

end ConcreteSpliceAttachment

/-- Original boundary targets, generated from the exact crossing positions. -/
def reconstructionAttachment?
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host)
    (compiled : ExtractionCompilation occurrence)
    (removed : RemovalResult occurrence) :
    Option (ConcreteSpliceAttachment removed compiled.checked) :=
  checkConcreteSpliceAttachment removed compiled.checked
    fun position =>
    Removal.wireIndex occurrence
      (occurrence.wireMap (occurrence.boundarySourceAt position))
      (Removal.boundarySource_retained occurrence position)


/--
The normalized checked endpoint and total source-wire transport produced by a
successful concrete splice.  Only `splice` can construct this receipt.
-/
structure ConcreteSpliceResult
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {site : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment site fragment) : Type where
  private mk ::
  checked : CheckedDiagram definitions
  wireImage : attachment.diagram.WireId → checked.val.WireId
  wireImage_signature :
    ∀ wire,
      (checked.val.wires (wireImage wire)).sig =
        (attachment.diagram.wires wire).sig

namespace ConcreteSpliceResult

/-- The normalized image of one supplied boundary position. -/
def boundaryTarget
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {site : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment site fragment}
    (result : ConcreteSpliceResult attachment)
    (position : Fin fragment.val.boundary.length) :
    result.checked.val.WireId :=
  result.wireImage (attachment.hostWire (attachment.target position))

theorem boundaryTarget_signature
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {site : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment site fragment}
    (result : ConcreteSpliceResult attachment)
    (position : Fin fragment.val.boundary.length) :
    (result.checked.val.wires (result.boundaryTarget position)).sig =
      (fragment.val.diagram.wires
        (fragment.val.boundary.get position)).sig :=
  (result.wireImage_signature
      (attachment.hostWire (attachment.target position))).trans
    ((attachment.diagram_wire_hostWire
      (attachment.target position)).trans
        (attachment.signature position))

theorem boundaryTarget_eq_of_alias
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {site : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment site fragment}
    (result : ConcreteSpliceResult attachment)
    (left right : Fin fragment.val.boundary.length)
    (alias : attachment.target left = attachment.target right) :
    result.boundaryTarget left = result.boundaryTarget right := by
  simp [boundaryTarget, alias]

end ConcreteSpliceResult

/--
Validate the generated candidate, normalize its checked form, and return the
only public receipt for that pipeline.
-/
def splice
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {site : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment site fragment) :
    Except WFError (ConcreteSpliceResult attachment) := by
  match accepted :
      ConcreteDiagram.checkWellFormed definitions attachment.diagram with
  | .error error => exact .error error
  | .ok checked =>
      have same :=
        ConcreteDiagram.checkWellFormed_preserves_input accepted
      let generated : CheckedDiagram definitions :=
        ⟨attachment.diagram, by
          rw [← same]
          exact checked.property⟩
      let normalized :=
        ConcreteDiagram.normalizeIdentities generated
      exact .ok
        (ConcreteSpliceResult.mk normalized.target
          normalized.wireImage normalized.wire_signature)

/--
Raw generated-candidate well-formedness is recoverable only by presenting the
exact successful `splice` receipt.  Proof modules use this to reason about the
private pre-normalization stage.
-/
theorem splice_success_wellFormed
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {site : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment site fragment}
    {result : ConcreteSpliceResult attachment}
    (accepted : splice attachment = .ok result) :
    attachment.diagram.WellFormed definitions := by
  unfold splice at accepted
  split at accepted
  · contradiction
  · rename_i generated checked
    have same :=
      ConcreteDiagram.checkWellFormed_preserves_input checked
    rw [← same]
    exact generated.property

/-- A successful receipt's public checked target is exactly the eager normal form. -/
theorem splice_success_checked
    {definitions : List (List Sig)}
    {pattern host : CheckedDiagram definitions}
    {occurrence : Occurrence pattern host}
    {site : RemovalResult occurrence}
    {fragment : CheckedOpenDiagram definitions}
    {attachment : ConcreteSpliceAttachment site fragment}
    {result : ConcreteSpliceResult attachment}
    (accepted : splice attachment = .ok result) :
    result.checked =
      (ConcreteDiagram.normalizeIdentities
        (⟨attachment.diagram,
          splice_success_wellFormed accepted⟩ :
          CheckedDiagram definitions)).target := by
  unfold splice at accepted
  split at accepted
  · contradiction
  · rename_i checked checkedAccepted
    simp only [Except.ok.injEq] at accepted
    subst result
    rfl

end VisualProof
