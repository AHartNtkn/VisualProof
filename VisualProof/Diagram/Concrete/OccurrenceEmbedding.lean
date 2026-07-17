import VisualProof.Diagram.Concrete.Subgraph.Extract
import VisualProof.Lambda.Certificate

namespace VisualProof.Diagram

open VisualProof.Data.Finite
open ConcreteElaboration

/--
A checked finite occurrence problem.  The binder spine is explicit data: graph
shape alone does not turn an ordinary bubble into an external-binder proxy.
-/
structure OccurrenceProblem (signature : List Nat) where
  host : CheckedDiagram signature
  pattern : CheckedOpenDiagram signature
  binderSpine : BinderSpine pattern.val.diagram
  terminalBody : binderSpine.TerminalBodyContract pattern.val
  binderTarget : Fin binderSpine.proxyCount → Fin host.val.regionCount
  inRegion : Option (Fin host.val.regionCount) := none
  attachmentSeed :
    Option (Fin pattern.val.boundary.length → Fin host.val.wireCount) := none

namespace OccurrenceProblem

abbrev HostRegion (problem : OccurrenceProblem signature) :=
  Fin problem.host.val.regionCount

abbrev PatternRegion (problem : OccurrenceProblem signature) :=
  Fin problem.pattern.val.diagram.regionCount

abbrev HostNode (problem : OccurrenceProblem signature) :=
  Fin problem.host.val.nodeCount

abbrev PatternNode (problem : OccurrenceProblem signature) :=
  Fin problem.pattern.val.diagram.nodeCount

abbrev HostWire (problem : OccurrenceProblem signature) :=
  Fin problem.host.val.wireCount

abbrev PatternWire (problem : OccurrenceProblem signature) :=
  Fin problem.pattern.val.diagram.wireCount

/--
The effective content root and all material descendants below it.  Administrative
sheet/proxy regions above the terminal body are deliberately absent.
-/
def IsContentRegion (problem : OccurrenceProblem signature)
    (region : problem.PatternRegion) : Prop :=
  region = problem.binderSpine.bodyContainer ∨
    (problem.binderSpine.IsMaterialRegion region ∧
      problem.pattern.val.diagram.Encloses
        problem.binderSpine.bodyContainer region)

instance (problem : OccurrenceProblem signature)
    (region : problem.PatternRegion) :
    Decidable (problem.IsContentRegion region) := by
  unfold IsContentRegion
  infer_instance

def contentRegionBool (problem : OccurrenceProblem signature)
    (region : problem.PatternRegion) : Bool :=
  decide (problem.IsContentRegion region)

/-- The dense intrinsic carrier of pattern content regions. -/
abbrev ContentRegion (problem : OccurrenceProblem signature) :=
  FilteredFiber problem.contentRegionBool

def ContentRegion.origin (problem : OccurrenceProblem signature)
    (region : problem.ContentRegion) : problem.PatternRegion :=
  FilteredFiber.origin problem.contentRegionBool region

@[simp] theorem ContentRegion.origin_is_content
    (problem : OccurrenceProblem signature)
    (region : problem.ContentRegion) :
    problem.IsContentRegion (region.origin problem) := by
  exact of_decide_eq_true
    (FilteredFiber.origin_survives problem.contentRegionBool region)

def contentNodeBool (problem : OccurrenceProblem signature)
    (node : problem.PatternNode) : Bool :=
  problem.contentRegionBool (problem.pattern.val.diagram.nodes node).region

/-- The dense intrinsic carrier of nodes owned by content regions. -/
abbrev ContentNode (problem : OccurrenceProblem signature) :=
  FilteredFiber problem.contentNodeBool

def ContentNode.origin (problem : OccurrenceProblem signature)
    (node : problem.ContentNode) : problem.PatternNode :=
  FilteredFiber.origin problem.contentNodeBool node

def contentTermNodeBool (problem : OccurrenceProblem signature)
    (node : problem.PatternNode) : Bool :=
  problem.contentNodeBool node &&
    match problem.pattern.val.diagram.nodes node with
    | .term _ _ _ => true
    | _ => false

/-- The intrinsic certificate domain: exactly the term nodes in the content. -/
abbrev ContentTermNode (problem : OccurrenceProblem signature) :=
  FilteredFiber problem.contentTermNodeBool

def ContentTermNode.origin (problem : OccurrenceProblem signature)
    (node : problem.ContentTermNode) : problem.PatternNode :=
  FilteredFiber.origin problem.contentTermNodeBool node

def boundaryWireBool (problem : OccurrenceProblem signature)
    (wire : problem.PatternWire) : Bool :=
  decide (wire ∈ problem.pattern.val.boundary)

abbrev BoundaryWire (problem : OccurrenceProblem signature) :=
  FilteredFiber problem.boundaryWireBool

def BoundaryWire.origin (problem : OccurrenceProblem signature)
    (wire : problem.BoundaryWire) : problem.PatternWire :=
  FilteredFiber.origin problem.boundaryWireBool wire

def internalWireBool (problem : OccurrenceProblem signature)
    (wire : problem.PatternWire) : Bool :=
  !problem.boundaryWireBool wire

abbrev InternalWire (problem : OccurrenceProblem signature) :=
  FilteredFiber problem.internalWireBool

def InternalWire.origin (problem : OccurrenceProblem signature)
    (wire : problem.InternalWire) : problem.PatternWire :=
  FilteredFiber.origin problem.internalWireBool wire

end OccurrenceProblem

/--
Unchecked finite occurrence data.  All maps are total exactly on their intended
intrinsic domains.  External binder targets intentionally carry no injectivity
field, and boundary-wire images may alias.
-/
structure RawOccurrenceCertificate (problem : OccurrenceProblem signature) where
  anchor : problem.HostRegion
  regionMap : problem.ContentRegion → problem.HostRegion
  nodeMap : problem.ContentNode → problem.HostNode
  wireMap : problem.PatternWire → problem.HostWire
  attachment : Fin problem.pattern.val.boundary.length → problem.HostWire
  termCertificate : problem.ContentTermNode → Lambda.Certificate

namespace RawOccurrenceCertificate

variable {problem : OccurrenceProblem signature}

def regionImage? (raw : RawOccurrenceCertificate problem)
    (region : problem.PatternRegion) : Option problem.HostRegion :=
  (FilteredFiber.index? problem.contentRegionBool region).map raw.regionMap

def nodeImage? (raw : RawOccurrenceCertificate problem)
    (node : problem.PatternNode) : Option problem.HostNode :=
  (FilteredFiber.index? problem.contentNodeBool node).map raw.nodeMap

def termCertificate? (raw : RawOccurrenceCertificate problem)
    (node : problem.PatternNode) : Option Lambda.Certificate :=
  (FilteredFiber.index? problem.contentTermNodeBool node).map
    raw.termCertificate

def mapEndpoint? (raw : RawOccurrenceCertificate problem)
    (endpoint : CEndpoint problem.pattern.val.diagram.nodeCount) :
    Option (CEndpoint problem.host.val.nodeCount) :=
  (raw.nodeImage? endpoint.node).map fun node =>
    { node := node, port := endpoint.port }

def mappedEndpoints (raw : RawOccurrenceCertificate problem)
    (wire : problem.PatternWire) :
    List (CEndpoint problem.host.val.nodeCount) :=
  (problem.pattern.val.diagram.wires wire).endpoints.filterMap raw.mapEndpoint?

def mappedRegionOwner? (raw : RawOccurrenceCertificate problem)
    (owner : problem.PatternRegion) : Option problem.HostRegion :=
  if owner = problem.binderSpine.bodyContainer then
    some raw.anchor
  else
    raw.regionImage? owner

theorem mappedRegionOwner?_eq_some
    (raw : RawOccurrenceCertificate problem)
    {owner : problem.PatternRegion} {mapped : problem.HostRegion}
    (equality : raw.mappedRegionOwner? owner = some mapped) :
    (owner = problem.binderSpine.bodyContainer ∧ mapped = raw.anchor) ∨
      ∃ content : problem.ContentRegion,
        content.origin problem = owner ∧ raw.regionMap content = mapped := by
  by_cases hroot : owner = problem.binderSpine.bodyContainer
  · left
    refine ⟨hroot, ?_⟩
    simp [mappedRegionOwner?, hroot] at equality
    exact equality.symm
  · right
    have himage : raw.regionImage? owner = some mapped := by
      simpa [mappedRegionOwner?, hroot] using equality
    unfold regionImage? at himage
    cases hindex : FilteredFiber.index? problem.contentRegionBool owner with
    | none => simp [hindex] at himage
    | some content =>
        have horigin := (FilteredFiber.index?_eq_some_iff
          problem.contentRegionBool owner content).1 hindex
        have hmapped : raw.regionMap content = mapped := by
          rw [hindex] at himage
          exact Option.some.inj himage
        exact ⟨content, horigin, hmapped⟩

theorem mappedRegionOwner?_eq_some_proper
    (raw : RawOccurrenceCertificate problem)
    {owner : problem.PatternRegion} {mapped : problem.HostRegion}
    (equality : raw.mappedRegionOwner? owner = some mapped) :
    (owner = problem.binderSpine.bodyContainer ∧ mapped = raw.anchor) ∨
      ∃ content : problem.ContentRegion,
        content.origin problem = owner ∧
          content.origin problem ≠ problem.binderSpine.bodyContainer ∧
            raw.regionMap content = mapped := by
  by_cases hroot : owner = problem.binderSpine.bodyContainer
  · left
    refine ⟨hroot, ?_⟩
    simp [mappedRegionOwner?, hroot] at equality
    exact equality.symm
  · right
    obtain ⟨content, horigin, hmapped⟩ :=
      (raw.mappedRegionOwner?_eq_some equality).resolve_left
        (fun root => hroot root.1)
    exact ⟨content, horigin, fun heq => hroot (horigin.symm.trans heq),
      hmapped⟩

/-- Proper regions preserve constructor, arity, and mapped parent. -/
def ProperRegionValid (raw : RawOccurrenceCertificate problem)
    (region : problem.ContentRegion) : Prop :=
  let source := region.origin problem
  source ≠ problem.binderSpine.bodyContainer →
    match problem.pattern.val.diagram.regions source with
    | .sheet => False
    | .cut parent =>
        ∃ mappedParent,
          raw.mappedRegionOwner? parent = some mappedParent ∧
            problem.host.val.regions (raw.regionMap region) = .cut mappedParent
    | .bubble parent arity =>
        ∃ mappedParent,
          raw.mappedRegionOwner? parent = some mappedParent ∧
            problem.host.val.regions (raw.regionMap region) =
              .bubble mappedParent arity

theorem ProperRegionValid.parent_image
    (raw : RawOccurrenceCertificate problem)
    (region : problem.ContentRegion)
    (valid : raw.ProperRegionValid region)
    (proper : region.origin problem ≠ problem.binderSpine.bodyContainer)
    {parent : problem.PatternRegion}
    (parent_eq :
      (problem.pattern.val.diagram.regions (region.origin problem)).parent? =
        some parent) :
    ∃ mappedParent,
      raw.mappedRegionOwner? parent = some mappedParent ∧
        (problem.host.val.regions (raw.regionMap region)).parent? =
          some mappedParent := by
  cases hsource : problem.pattern.val.diagram.regions (region.origin problem) with
  | sheet => simp [hsource, CRegion.parent?] at parent_eq
  | cut sourceParent =>
      have hparent : sourceParent = parent := by
        rw [hsource] at parent_eq
        exact Option.some.inj parent_eq
      subst sourceParent
      obtain ⟨mappedParent, howner, htarget⟩ := by
        simpa [ProperRegionValid, hsource] using valid proper
      exact ⟨mappedParent, howner, by simp [htarget, CRegion.parent?]⟩
  | bubble sourceParent arity =>
      have hparent : sourceParent = parent := by
        rw [hsource] at parent_eq
        exact Option.some.inj parent_eq
      subst sourceParent
      obtain ⟨mappedParent, howner, htarget⟩ := by
        simpa [ProperRegionValid, hsource] using valid proper
      exact ⟨mappedParent, howner, by simp [htarget, CRegion.parent?]⟩

private def AtomBinderValid (raw : RawOccurrenceCertificate problem)
    (source : problem.PatternRegion) (target : problem.HostRegion) : Prop :=
  (∃ proxy, source = problem.binderSpine.proxy proxy ∧
      target = problem.binderTarget proxy) ∨
    ((∀ proxy, source ≠ problem.binderSpine.proxy proxy) ∧
      raw.regionImage? source = some target)

private def TermNodeValid (raw : RawOccurrenceCertificate problem)
    (sourceIndex : problem.PatternNode)
    (sourcePorts targetPorts : Nat)
    (sourceTerm : Lambda.Term 0 (Fin sourcePorts))
    (targetTerm : Lambda.Term 0 (Fin targetPorts)) : Prop :=
  if portsEq : targetPorts = sourcePorts then
    match raw.termCertificate? sourceIndex with
    | none => False
    | some certificate =>
        Lambda.checkCertificate sourceTerm.closeOverPorts
          ((targetTerm.mapFree (Fin.cast portsEq)).closeOverPorts)
          certificate = true
  else
    False

/-- Node ownership and constructor data, with positional beta-eta certificates. -/
def NodeValid (raw : RawOccurrenceCertificate problem)
    (node : problem.ContentNode) : Prop :=
  let sourceIndex := node.origin problem
  let source := problem.pattern.val.diagram.nodes sourceIndex
  let target := problem.host.val.nodes (raw.nodeMap node)
  raw.mappedRegionOwner? source.region = some target.region ∧
    match source, target with
    | .term _ sourcePorts sourceTerm,
        .term _ targetPorts targetTerm =>
        raw.TermNodeValid sourceIndex sourcePorts targetPorts
          sourceTerm targetTerm
    | .atom _ sourceBinder, .atom _ targetBinder =>
        raw.AtomBinderValid sourceBinder targetBinder
    | .named _ sourceDefinition sourceArity,
        .named _ targetDefinition targetArity =>
        sourceDefinition = targetDefinition ∧ sourceArity = targetArity
    | _, _ => False

namespace NodeValid

variable {problem : OccurrenceProblem signature}
  {raw : RawOccurrenceCertificate problem}
  {node : problem.ContentNode}

/-- Public proof-relevant elimination for a validated term-node image.  The
checker-internal predicate remains hidden; downstream occurrence equivalences
receive exactly the owner equality and checked positional beta-eta witness
that certification promises. -/
theorem term_elim
    (valid : raw.NodeValid node)
    (source_eq : problem.pattern.val.diagram.nodes (node.origin problem) =
      .term sourceRegion sourcePorts sourceTerm)
    (target_eq : problem.host.val.nodes (raw.nodeMap node) =
      .term targetRegion targetPorts targetTerm) :
    raw.mappedRegionOwner? sourceRegion = some targetRegion ∧
      ∃ portsEq : targetPorts = sourcePorts, ∃ certificate,
        raw.termCertificate? (node.origin problem) = some certificate ∧
          Lambda.checkCertificate sourceTerm.closeOverPorts
            ((targetTerm.mapFree (Fin.cast portsEq)).closeOverPorts)
            certificate = true := by
  unfold NodeValid at valid
  simp only [source_eq, target_eq, CNode.region] at valid
  rcases valid with ⟨howner, hterm⟩
  refine ⟨howner, ?_⟩
  unfold TermNodeValid at hterm
  split at hterm
  · rename_i portsEq
    split at hterm
    · contradiction
    · rename_i certificate hcertificate
      exact ⟨portsEq, certificate, hcertificate, hterm⟩
  · contradiction

/-- Public proof-relevant elimination for a validated atom-node image. -/
theorem atom_elim
    (valid : raw.NodeValid node)
    (source_eq : problem.pattern.val.diagram.nodes (node.origin problem) =
      .atom sourceRegion sourceBinder)
    (target_eq : problem.host.val.nodes (raw.nodeMap node) =
      .atom targetRegion targetBinder) :
    raw.mappedRegionOwner? sourceRegion = some targetRegion ∧
      ((∃ proxy,
          sourceBinder = problem.binderSpine.proxy proxy ∧
          targetBinder = problem.binderTarget proxy) ∨
        ((∀ proxy,
            sourceBinder ≠ problem.binderSpine.proxy proxy) ∧
          raw.regionImage? sourceBinder = some targetBinder)) := by
  unfold NodeValid at valid
  simp only [source_eq, target_eq, CNode.region] at valid
  simpa only [AtomBinderValid] using valid

/-- Public proof-relevant elimination for a validated named-node image. -/
theorem named_elim
    (valid : raw.NodeValid node)
    (source_eq : problem.pattern.val.diagram.nodes (node.origin problem) =
      .named sourceRegion sourceDefinition sourceArity)
    (target_eq : problem.host.val.nodes (raw.nodeMap node) =
      .named targetRegion targetDefinition targetArity) :
    raw.mappedRegionOwner? sourceRegion = some targetRegion ∧
      sourceDefinition = targetDefinition ∧ sourceArity = targetArity := by
  unfold NodeValid at valid
  simpa only [source_eq, target_eq, CNode.region] using valid

end NodeValid

def exactChildren (diagram : ConcreteDiagram)
    (region : Fin diagram.regionCount) : List (Fin diagram.regionCount) :=
  filterFin fun child =>
    decide ((diagram.regions child).parent? = some region)

def exactNodes (diagram : ConcreteDiagram)
    (region : Fin diagram.regionCount) : List (Fin diagram.nodeCount) :=
  filterFin fun node => decide ((diagram.nodes node).region = region)

@[simp] theorem mem_exactChildren (diagram : ConcreteDiagram)
    (region child : Fin diagram.regionCount) :
    child ∈ exactChildren diagram region ↔
      (diagram.regions child).parent? = some region := by
  simp [exactChildren]

@[simp] theorem mem_exactNodes (diagram : ConcreteDiagram)
    (region : Fin diagram.regionCount) (node : Fin diagram.nodeCount) :
    node ∈ exactNodes diagram region ↔
      (diagram.nodes node).region = region := by
  simp [exactNodes]

/-- Every proper mapped subtree is exact; only the content root is a subset. -/
def ProperSubtreeExact (raw : RawOccurrenceCertificate problem)
    (region : problem.ContentRegion) : Prop :=
  let source := region.origin problem
  source ≠ problem.binderSpine.bodyContainer →
    List.Perm
        ((exactChildren problem.pattern.val.diagram source).filterMap
          raw.regionImage?)
        (exactChildren problem.host.val (raw.regionMap region)) ∧
      List.Perm
        ((exactNodes problem.pattern.val.diagram source).filterMap raw.nodeImage?)
        (exactNodes problem.host.val (raw.regionMap region)) ∧
      List.Perm
        ((exactScopeWires problem.pattern.val.diagram source).map raw.wireMap)
        (exactScopeWires problem.host.val (raw.regionMap region))

/-- Every source endpoint must lie in the intrinsic node domain. -/
def EndpointsMapped (raw : RawOccurrenceCertificate problem)
    (wire : problem.PatternWire) : Prop :=
  (problem.pattern.val.diagram.wires wire).endpoints.all fun endpoint =>
    (raw.nodeImage? endpoint.node).isSome

/-- Boolean finite-multiset inclusion, retaining endpoint multiplicity. -/
def multisetIncluded [DecidableEq α] (source target : List α) : Prop :=
  source.all fun value => decide (source.count value ≤ target.count value)

instance [DecidableEq α] (source target : List α) :
    Decidable (multisetIncluded source target) := by
  unfold multisetIncluded
  infer_instance

def BoundaryWireValid (raw : RawOccurrenceCertificate problem)
    (wire : problem.BoundaryWire) : Prop :=
  let source := wire.origin problem
  let target := raw.wireMap source
  raw.EndpointsMapped source ∧
    problem.host.val.Encloses
      (problem.host.val.wires target).scope raw.anchor ∧
    multisetIncluded (raw.mappedEndpoints source)
      (problem.host.val.wires target).endpoints

def InternalWireValid (raw : RawOccurrenceCertificate problem)
    (wire : problem.InternalWire) : Prop :=
  let source := wire.origin problem
  let target := raw.wireMap source
  raw.EndpointsMapped source ∧
    raw.mappedRegionOwner?
      (problem.pattern.val.diagram.wires source).scope =
        some (problem.host.val.wires target).scope ∧
    List.Perm (raw.mappedEndpoints source)
      (problem.host.val.wires target).endpoints

/--
The effective content root is mapped as a subset of the anchor: every direct
source occupant is represented directly at the anchor, while extra host
children, nodes, and wires are permitted.
-/
def RootSubset (raw : RawOccurrenceCertificate problem) : Prop :=
  let root := problem.binderSpine.bodyContainer
  (∀ child,
      (problem.pattern.val.diagram.regions child).parent? = some root →
        ∃ content : problem.ContentRegion,
          content.origin problem = child ∧
            (problem.host.val.regions (raw.regionMap content)).parent? =
              some raw.anchor) ∧
    (∀ node,
      (problem.pattern.val.diagram.nodes node).region = root →
        ∃ content : problem.ContentNode,
          content.origin problem = node ∧
            (problem.host.val.nodes (raw.nodeMap content)).region = raw.anchor) ∧
    (∀ wire, wire ∉ problem.pattern.val.boundary →
      (problem.pattern.val.diagram.wires wire).scope = root →
        (problem.host.val.wires (raw.wireMap wire)).scope = raw.anchor)

private def SeedValid (raw : RawOccurrenceCertificate problem) : Prop :=
  (match problem.inRegion with
    | none => True
    | some region => raw.anchor = region) ∧
  match problem.attachmentSeed with
  | none => True
  | some seed => ∀ position, raw.attachment position = seed position

private def decidableForallFin {n : Nat} (predicate : Fin n → Prop)
    (decidable : ∀ index, Decidable (predicate index)) :
    Decidable (∀ index, predicate index) :=
  @Nat.decidableForallFin n predicate decidable

private def decidableExistsFin {n : Nat} (predicate : Fin n → Prop)
    (decidable : ∀ index, Decidable (predicate index)) :
    Decidable (∃ index, predicate index) :=
  @Nat.decidableExistsFin n predicate decidable

private def decidableImplies (premise conclusion : Prop)
    (premiseDecidable : Decidable premise)
    (conclusionDecidable : Decidable conclusion) :
    Decidable (premise → conclusion) :=
  match premiseDecidable, conclusionDecidable with
  | isFalse premiseFalse, _ =>
      isTrue fun premiseTrue => False.elim (premiseFalse premiseTrue)
  | isTrue _, isTrue conclusionTrue => isTrue fun _ => conclusionTrue
  | isTrue premiseTrue, isFalse conclusionFalse =>
      isFalse fun implication => conclusionFalse (implication premiseTrue)

private def decidableInjectiveFin (map : Fin source → Fin target) :
    Decidable (Function.Injective map) := by
  unfold Function.Injective
  exact decidableForallFin _ fun left =>
    decidableForallFin _ fun right => inferInstance

private instance (raw : RawOccurrenceCertificate problem) :
    Decidable raw.SeedValid := by
  unfold SeedValid
  cases problem.inRegion <;> cases problem.attachmentSeed
  · infer_instance
  · rename_i seed
    let predicate := fun position : Fin problem.pattern.val.boundary.length =>
      raw.attachment position = seed position
    exact @instDecidableAnd True (∀ position, predicate position)
      (isTrue trivial) (decidableForallFin predicate fun _ => inferInstance)
  · infer_instance
  · rename_i region seed
    let predicate := fun position : Fin problem.pattern.val.boundary.length =>
      raw.attachment position = seed position
    exact @instDecidableAnd (raw.anchor = region)
      (∀ position, predicate position) inferInstance
      (decidableForallFin predicate fun _ => inferInstance)

private instance (raw : RawOccurrenceCertificate problem) :
    Decidable raw.RootSubset := by
  unfold RootSubset
  dsimp only
  let childPredicate := fun child : problem.PatternRegion =>
    (problem.pattern.val.diagram.regions child).parent? =
        some problem.binderSpine.bodyContainer →
      ∃ content : problem.ContentRegion,
        content.origin problem = child ∧
          (problem.host.val.regions (raw.regionMap content)).parent? =
            some raw.anchor
  let nodePredicate := fun node : problem.PatternNode =>
    (problem.pattern.val.diagram.nodes node).region =
        problem.binderSpine.bodyContainer →
      ∃ content : problem.ContentNode,
        content.origin problem = node ∧
          (problem.host.val.nodes (raw.nodeMap content)).region = raw.anchor
  let wirePredicate := fun wire : problem.PatternWire =>
    wire ∉ problem.pattern.val.boundary →
      (problem.pattern.val.diagram.wires wire).scope =
          problem.binderSpine.bodyContainer →
        (problem.host.val.wires (raw.wireMap wire)).scope = raw.anchor
  have childDecidable : Decidable (∀ child, childPredicate child) :=
    decidableForallFin childPredicate fun child =>
      decidableImplies _ _ inferInstance
        (decidableExistsFin _ fun _ => inferInstance)
  have nodeDecidable : Decidable (∀ node, nodePredicate node) :=
    decidableForallFin nodePredicate fun node =>
      decidableImplies _ _ inferInstance
        (decidableExistsFin _ fun _ => inferInstance)
  have wireDecidable : Decidable (∀ wire, wirePredicate wire) :=
    decidableForallFin wirePredicate fun wire =>
      decidableImplies _ _ inferInstance
        (decidableImplies _ _ inferInstance inferInstance)
  exact @instDecidableAnd (∀ child, childPredicate child)
    ((∀ node, nodePredicate node) ∧ ∀ wire, wirePredicate wire)
    childDecidable (@instDecidableAnd _ _ nodeDecidable wireDecidable)

private instance (raw : RawOccurrenceCertificate problem)
    (region : problem.ContentRegion) :
    Decidable (raw.ProperRegionValid region) := by
  unfold ProperRegionValid
  dsimp only
  cases problem.pattern.val.diagram.regions (region.origin problem)
  <;> infer_instance

private instance (raw : RawOccurrenceCertificate problem)
    (source : problem.PatternRegion) (target : problem.HostRegion) :
    Decidable (raw.AtomBinderValid source target) := by
  unfold AtomBinderValid
  let externalPredicate := fun proxy : Fin problem.binderSpine.proxyCount =>
    source = problem.binderSpine.proxy proxy ∧
      target = problem.binderTarget proxy
  let internalPredicate := fun proxy : Fin problem.binderSpine.proxyCount =>
    source ≠ problem.binderSpine.proxy proxy
  exact @instDecidableOr (∃ proxy, externalPredicate proxy)
    ((∀ proxy, internalPredicate proxy) ∧ raw.regionImage? source = some target)
    (decidableExistsFin externalPredicate fun _ => inferInstance)
    (@instDecidableAnd _ _
      (decidableForallFin internalPredicate fun _ => inferInstance)
      inferInstance)

private instance (raw : RawOccurrenceCertificate problem)
    (sourceIndex : problem.PatternNode) (sourcePorts targetPorts : Nat)
    (sourceTerm : Lambda.Term 0 (Fin sourcePorts))
    (targetTerm : Lambda.Term 0 (Fin targetPorts)) :
    Decidable (raw.TermNodeValid sourceIndex sourcePorts targetPorts
      sourceTerm targetTerm) := by
  unfold TermNodeValid
  split
  · cases raw.termCertificate? sourceIndex <;> infer_instance
  · infer_instance

private instance (raw : RawOccurrenceCertificate problem)
    (node : problem.ContentNode) : Decidable (raw.NodeValid node) := by
  unfold NodeValid
  dsimp only
  cases problem.pattern.val.diagram.nodes (node.origin problem) <;>
    cases problem.host.val.nodes (raw.nodeMap node) <;> infer_instance

private instance (raw : RawOccurrenceCertificate problem)
    (wire : problem.PatternWire) : Decidable (raw.EndpointsMapped wire) := by
  unfold EndpointsMapped
  infer_instance

private instance (raw : RawOccurrenceCertificate problem)
    (wire : problem.BoundaryWire) :
    Decidable (raw.BoundaryWireValid wire) := by
  unfold BoundaryWireValid
  dsimp only
  infer_instance

private instance (raw : RawOccurrenceCertificate problem)
    (wire : problem.InternalWire) :
    Decidable (raw.InternalWireValid wire) := by
  unfold InternalWireValid
  dsimp only
  infer_instance

private instance (raw : RawOccurrenceCertificate problem)
    (region : problem.ContentRegion) :
    Decidable (raw.ProperSubtreeExact region) := by
  unfold ProperSubtreeExact
  dsimp only
  infer_instance

/-- The declarative finite occurrence-embedding relation. -/
def Valid (raw : RawOccurrenceCertificate problem) : Prop :=
  raw.SeedValid ∧
  raw.regionImage? problem.binderSpine.bodyContainer = some raw.anchor ∧
  raw.RootSubset ∧
  Function.Injective raw.regionMap ∧
  (∀ region, raw.ProperRegionValid region) ∧
  Function.Injective raw.nodeMap ∧
  (∀ node, raw.NodeValid node) ∧
  (∀ proxy,
    (∃ parent, problem.host.val.regions (problem.binderTarget proxy) =
        .bubble parent (problem.binderSpine.arity proxy)) ∧
      problem.host.val.Encloses (problem.binderTarget proxy) raw.anchor) ∧
  Function.Injective
    (fun wire : problem.InternalWire => raw.wireMap (wire.origin problem)) ∧
  (∀ boundary : problem.BoundaryWire,
    ∀ internal : problem.InternalWire,
      raw.wireMap (boundary.origin problem) ≠
        raw.wireMap (internal.origin problem)) ∧
  (∀ wire, raw.BoundaryWireValid wire) ∧
  (∀ wire, raw.InternalWireValid wire) ∧
  (∀ position,
    raw.attachment position =
      raw.wireMap (problem.pattern.val.boundary.get position)) ∧
  (∀ region, raw.ProperSubtreeExact region)

namespace Valid

variable {raw : RawOccurrenceCertificate problem}

theorem seeds (valid : raw.Valid) : raw.SeedValid := valid.1

theorem root_image (valid : raw.Valid) :
    raw.regionImage? problem.binderSpine.bodyContainer = some raw.anchor :=
  valid.2.1

theorem root_subset (valid : raw.Valid) : raw.RootSubset := valid.2.2.1

theorem region_injective (valid : raw.Valid) :
    Function.Injective raw.regionMap := valid.2.2.2.1

theorem proper_region (valid : raw.Valid) :
    ∀ region, raw.ProperRegionValid region := valid.2.2.2.2.1

theorem node_injective (valid : raw.Valid) :
    Function.Injective raw.nodeMap := valid.2.2.2.2.2.1

theorem nodes (valid : raw.Valid) :
    ∀ node, raw.NodeValid node := valid.2.2.2.2.2.2.1

theorem binders (valid : raw.Valid) :
    ∀ proxy,
      (∃ parent, problem.host.val.regions (problem.binderTarget proxy) =
          .bubble parent (problem.binderSpine.arity proxy)) ∧
        problem.host.val.Encloses (problem.binderTarget proxy) raw.anchor :=
  valid.2.2.2.2.2.2.2.1

theorem internal_injective (valid : raw.Valid) :
    Function.Injective (fun wire : problem.InternalWire =>
      raw.wireMap (wire.origin problem)) :=
  valid.2.2.2.2.2.2.2.2.1

theorem boundary_internal_disjoint (valid : raw.Valid) :
    ∀ boundary : problem.BoundaryWire,
      ∀ internal : problem.InternalWire,
        raw.wireMap (boundary.origin problem) ≠
          raw.wireMap (internal.origin problem) :=
  valid.2.2.2.2.2.2.2.2.2.1

theorem boundary_wires (valid : raw.Valid) :
    ∀ wire, raw.BoundaryWireValid wire :=
  valid.2.2.2.2.2.2.2.2.2.2.1

theorem internal_wires (valid : raw.Valid) :
    ∀ wire, raw.InternalWireValid wire :=
  valid.2.2.2.2.2.2.2.2.2.2.2.1

theorem attachments (valid : raw.Valid) :
    ∀ position,
      raw.attachment position =
        raw.wireMap (problem.pattern.val.boundary.get position) :=
  valid.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem proper_subtrees (valid : raw.Valid) :
    ∀ region, raw.ProperSubtreeExact region :=
  valid.2.2.2.2.2.2.2.2.2.2.2.2.2

end Valid

instance (raw : RawOccurrenceCertificate problem) : Decidable raw.Valid := by
  unfold Valid
  letI : Decidable (Function.Injective raw.regionMap) :=
    decidableInjectiveFin raw.regionMap
  letI : Decidable (∀ region, raw.ProperRegionValid region) :=
    decidableForallFin _ fun _ => inferInstance
  letI : Decidable (Function.Injective raw.nodeMap) :=
    decidableInjectiveFin raw.nodeMap
  letI : Decidable (∀ node, raw.NodeValid node) :=
    decidableForallFin _ fun _ => inferInstance
  letI : Decidable (∀ proxy,
      (∃ parent, problem.host.val.regions (problem.binderTarget proxy) =
          .bubble parent (problem.binderSpine.arity proxy)) ∧
        problem.host.val.Encloses (problem.binderTarget proxy) raw.anchor) :=
    decidableForallFin _ fun _ => inferInstance
  letI : Decidable (Function.Injective
      (fun wire : problem.InternalWire =>
        raw.wireMap (wire.origin problem))) :=
    decidableInjectiveFin _
  letI : Decidable (∀ boundary : problem.BoundaryWire,
      ∀ internal : problem.InternalWire,
        raw.wireMap (boundary.origin problem) ≠
          raw.wireMap (internal.origin problem)) :=
    decidableForallFin _ fun _ =>
      decidableForallFin _ fun _ => inferInstance
  letI : Decidable (∀ wire, raw.BoundaryWireValid wire) :=
    decidableForallFin _ fun _ => inferInstance
  letI : Decidable (∀ wire, raw.InternalWireValid wire) :=
    decidableForallFin _ fun _ => inferInstance
  letI : Decidable (∀ position,
      raw.attachment position =
        raw.wireMap (problem.pattern.val.boundary.get position)) :=
    decidableForallFin _ fun _ => inferInstance
  letI : Decidable (∀ region, raw.ProperSubtreeExact region) :=
    decidableForallFin _ fun _ => inferInstance
  infer_instance

/--
A diagnostic snapshot of raw map images.  This is deliberately not the matcher
footprint: observational equality is defined later by reconstructed checked
selection together with ordered attachments.
-/
structure MapImageSummary (problem : OccurrenceProblem signature) where
  anchor : problem.HostRegion
  regions : List problem.HostRegion
  nodes : List problem.HostNode
  wires : List problem.HostWire
  attachments : List problem.HostWire
  deriving DecidableEq

def mapImageSummary (raw : RawOccurrenceCertificate problem) :
    MapImageSummary problem where
  anchor := raw.anchor
  regions := List.ofFn raw.regionMap
  nodes := List.ofFn raw.nodeMap
  wires := List.ofFn raw.wireMap
  attachments := List.ofFn raw.attachment

/-- The deterministic checker contains no search bound or reduction fuel. -/
def check (raw : RawOccurrenceCertificate problem) : Bool :=
  decide raw.Valid

theorem check_iff_valid (raw : RawOccurrenceCertificate problem) :
    raw.check = true ↔ raw.Valid := by
  simp [check]

end RawOccurrenceCertificate

/-- A raw finite map package paired with the authoritative validity proof. -/
structure OpenOccurrenceEmbedding (problem : OccurrenceProblem signature) where
  raw : RawOccurrenceCertificate problem
  valid : raw.Valid

namespace OpenOccurrenceEmbedding

def ofValid (raw : RawOccurrenceCertificate problem) (valid : raw.Valid) :
    OpenOccurrenceEmbedding problem :=
  ⟨raw, valid⟩

/-- Sound construction directly from a successful Boolean check. -/
def ofCheck (raw : RawOccurrenceCertificate problem)
    (accepted : raw.check = true) : OpenOccurrenceEmbedding problem :=
  ⟨raw, (RawOccurrenceCertificate.check_iff_valid raw).1 accepted⟩

/-- The proof-producing form of the checker. -/
def check? (raw : RawOccurrenceCertificate problem) :
    Option (OpenOccurrenceEmbedding problem) :=
  if accepted : raw.check = true then some (ofCheck raw accepted) else none

@[simp] theorem check?_isSome_iff (raw : RawOccurrenceCertificate problem) :
    (check? raw).isSome = true ↔ raw.Valid := by
  rw [← RawOccurrenceCertificate.check_iff_valid raw]
  unfold check?
  split <;> simp_all

theorem check?_sound {raw : RawOccurrenceCertificate problem}
    {checked : OpenOccurrenceEmbedding problem}
    (accepted : check? raw = some checked) : checked.raw = raw := by
  unfold check? at accepted
  split at accepted
  · exact (congrArg OpenOccurrenceEmbedding.raw
      (Option.some.inj accepted)).symm
  · contradiction

theorem check?_complete {raw : RawOccurrenceCertificate problem}
    (valid : raw.Valid) : ∃ checked, check? raw = some checked := by
  have accepted := (RawOccurrenceCertificate.check_iff_valid raw).2 valid
  exact ⟨ofCheck raw accepted, by simp [check?, accepted]⟩

theorem check_eq_true (checked : OpenOccurrenceEmbedding problem) :
    checked.raw.check = true :=
  (RawOccurrenceCertificate.check_iff_valid checked.raw).2 checked.valid

end OpenOccurrenceEmbedding

end VisualProof.Diagram
