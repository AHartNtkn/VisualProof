import VisualProof.Diagram.Concrete.Subgraph.FactorizationFrame
import VisualProof.Diagram.Concrete.WireQuantifierSingletonRemoval

namespace VisualProof

namespace WirePrimitive

/-!
One checked authority owns the concrete meaning of an applied wire site.
Primitive checkers consume `AllAppliedSites`; no rule may select only a
proper subset of an acted-on wire's applied heads.
-/

private def argumentWires?
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (arity : Nat) : Option (List source.val.WireId) :=
  (List.range arity).mapM fun position =>
    source.val.endpointOwner? ⟨node, .arg position⟩

/--
One atom-head occurrence of an acted-on wire, with its ordered argument wires
and canonical checked frame at the atom's region.
-/
structure AppliedSite
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) where
  private mk ::
  node : source.val.NodeId
  region : source.val.RegionId
  argumentSignatures : List Sig
  arguments : List source.val.WireId
  frame : SiteCompilation source region
  private node_exact :
    source.val.nodes node = .atom region argumentSignatures
  private head_owner :
    source.val.endpointOwner? ⟨node, .head⟩ = some wire
  private arguments_checked :
    argumentWires? source node argumentSignatures.length =
      some arguments
  private arguments_length_exact :
    arguments.length = argumentSignatures.length

namespace AppliedSite

/-- The concrete endpoint represented by an applied site. -/
def endpoint
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (site : AppliedSite source wire) :
    CEndpoint source.val.nodeCount :=
  ⟨site.node, .head⟩

/-- Ordered arguments have exactly the atom's checked arity. -/
theorem arguments_length
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (site : AppliedSite source wire) :
    site.arguments.length = site.argumentSignatures.length :=
  site.arguments_length_exact

/-- The head owner is the acted-on wire, not caller-supplied metadata. -/
theorem endpoint_owner
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (site : AppliedSite source wire) :
    source.val.endpointOwner? site.endpoint = some wire :=
  site.head_owner

/-- The canonical site factorization belongs to the atom's exact region. -/
theorem node_data
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (site : AppliedSite source wire) :
    source.val.nodes site.node =
      .atom site.region site.argumentSignatures :=
  site.node_exact

/--
The checked site frame projects to the exact compiled atom singleton, and
the atom head resolves to the acted wire. This is the semantic entry point
for checker-owned singleton-erasure folds.
-/
theorem compiled_atom
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (site : AppliedSite source wire) :
    ∃ (outer : ConcreteElaboration.WireContext source.val)
      (_visibleExact :
        site.frame.frame.visible = outer.extend site.region)
      (head :
        Var (outer.extend site.region).sigs
          (.rel site.argumentSignatures))
      (arguments :
        Vars (outer.extend site.region).sigs
          site.argumentSignatures),
      ConcreteElaboration.compileNodes? definitions source.val
          (outer.extend site.region) [site.node] =
        some (.cons (.atom head arguments) .nil) ∧
      ConcreteElaboration.WireContext.origin source.val
          (outer.extend site.region).ids head =
        wire := by
  obtain ⟨outer, _fuel, nodes, _children, visibleExact,
      nodesCompiled, _childrenCompiled, _bodyExact⟩ :=
    site.frame.site_origin
  have member : site.node ∈ source.val.nodesAt site.region := by
    unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList
    apply List.mem_filter.mpr
    exact
      ⟨Data.Finite.mem_allFin site.node,
        by rw [site.node_data]; exact beq_iff_eq.mpr rfl⟩
  obtain ⟨item, singletonCompiled⟩ :=
    ConcreteWireQuantifier.SingletonRemovalSemantics.compileNodes_singleton_of_member
      definitions source.val (outer.extend site.region)
      (source.val.nodesAt site.region) nodes nodesCompiled site.node member
  obtain ⟨head, arguments, itemExact, headOrigin, _argumentOrigins⟩ :=
    ConcreteElaboration.compileNodes?_atom_shape source.val
      (outer.extend site.region) site.node site.node_data singletonCompiled
  have itemSame : item = .atom head arguments :=
    ItemSeq.cons.inj itemExact |>.1
  subst item
  have exactHead :
      ConcreteElaboration.WireContext.origin source.val
          (outer.extend site.region).ids head =
        wire :=
    Option.some.inj (headOrigin.symm.trans site.endpoint_owner)
  exact
    ⟨outer, visibleExact, head, arguments, singletonCompiled, exactHead⟩

end AppliedSite

/-- Check one exact endpoint as an applied atom head of `wire`. -/
def checkAppliedSite
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (endpoint : CEndpoint source.val.nodeCount) :
    Option (AppliedSite source wire) :=
  match endpoint with
  | ⟨node, .head⟩ =>
      match nodeData : source.val.nodes node with
      | .atom region signatures =>
          if owner :
              source.val.endpointOwner? ⟨node, .head⟩ = some wire then
            match argumentsAccepted :
                argumentWires? source node signatures.length with
            | none => none
            | some arguments =>
                if argumentsLength :
                    arguments.length = signatures.length then
                  match compileSite? source region with
                  | none => none
                  | some frame =>
                      some
                        (AppliedSite.mk node region signatures
                          arguments frame nodeData owner argumentsAccepted
                          argumentsLength)
                else
                  none
          else
            none
      | _ => none
  | _ => none

/--
The exhaustive checked site list for one acted-on wire.  Its retained equation
pins both membership and concrete endpoint order.
-/
structure AllAppliedSites
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) where
  private mk ::
  sites : List (AppliedSite source wire)
  private endpoints_exact :
    sites.map AppliedSite.endpoint =
      (source.val.wires wire).endpoints

/--
Accept only when every endpoint of the acted-on wire is an applied atom head.
The resulting list is exhaustive and preserves the wire's concrete order.
-/
def checkAllAppliedSites
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :
    Option (AllAppliedSites source wire) :=
  match
      (source.val.wires wire).endpoints.mapM
        (checkAppliedSite source wire) with
  | none => none
  | some sites =>
      if exact :
          sites.map AppliedSite.endpoint =
            (source.val.wires wire).endpoints then
        some (AllAppliedSites.mk sites exact)
      else
        none

namespace AllAppliedSites

/-- Every acted-on endpoint occurs at exactly one retained applied site. -/
theorem exhaustive
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (all : AllAppliedSites source wire) :
    all.sites.map AppliedSite.endpoint =
      (source.val.wires wire).endpoints :=
  all.endpoints_exact

/-- Exhaustive applied sites and wire endpoints have the same cardinality. -/
theorem length
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (all : AllAppliedSites source wire) :
    all.sites.length = (source.val.wires wire).endpoints.length := by
  rw [← all.exhaustive, List.length_map]

end AllAppliedSites

namespace AppliedSiteErasure

open ConcreteWireQuantifier.SingletonRemovalSemantics

/--
Checker-owned recursive removal of applied heads. Each step is the canonical
checked singleton erasure, and the acted wire is transported into the next
checked state.
-/
private inductive Trace :
    (source : CheckedDiagram definitions) →
    (wire : source.val.WireId) →
    (target : CheckedDiagram definitions) →
    (targetWire : target.val.WireId) →
    Type
  | done
      (source : CheckedDiagram definitions)
      (wire : source.val.WireId)
      (empty : (source.val.wires wire).endpoints = []) :
      Trace source wire source wire
  | step
      {source : CheckedDiagram definitions}
      {wire : source.val.WireId}
      (site : AppliedSite source wire)
      (erasure : CheckedErasure source site.node)
      {target : CheckedDiagram definitions}
      {targetWire : target.val.WireId}
      (tail :
        Trace erasure.target (erasure.wireImage wire) target targetWire) :
      Trace source wire target targetWire

/-- Opaque complete singleton-erasure trace for every applied head. -/
structure Result
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) where
  private mk ::
  target : CheckedDiagram definitions
  targetWire : target.val.WireId
  private trace : Trace source wire target targetWire

private def checkWithFuel :
    (fuel : Nat) →
    (source : CheckedDiagram definitions) →
    (wire : source.val.WireId) →
    Option (Result source wire)
  | 0, source, wire =>
      if empty : (source.val.wires wire).endpoints = [] then
        some ⟨source, wire, .done source wire empty⟩
      else
        none
  | fuel + 1, source, wire =>
      match endpoints : (source.val.wires wire).endpoints with
      | [] =>
          some ⟨source, wire, .done source wire endpoints⟩
      | endpoint :: _ =>
          match checkAppliedSite source wire endpoint with
          | none => none
          | some site =>
              match (CheckedErasure.check source site.node).toOption with
              | none => none
              | some erasure =>
                  match
                      checkWithFuel fuel erasure.target
                        (erasure.wireImage wire) with
                  | none => none
                  | some tail =>
                      some
                        ⟨tail.target, tail.targetWire,
                          .step site erasure tail.trace⟩

/--
Remove every applied head by canonical checked singleton erasures. The fuel
bound is structural: each accepted step removes exactly one source node.
-/
def check
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :
    Option (Result source wire) :=
  checkWithFuel (source.val.nodeCount + 1) source wire

private theorem Trace.target_empty
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {target : CheckedDiagram definitions}
    {targetWire : target.val.WireId}
    (trace : Trace source wire target targetWire) :
    (target.val.wires targetWire).endpoints = [] := by
  induction trace with
  | done _ _ empty => exact empty
  | step _ _ _ induction => exact induction

/-- The final transported wire has no endpoints. -/
theorem Result.target_empty
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : Result source wire) :
    (result.target.val.wires result.targetWire).endpoints = [] :=
  result.trace.target_empty

end AppliedSiteErasure

end WirePrimitive

end VisualProof
