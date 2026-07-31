import VisualProof.Diagram.Concrete.Subgraph.FactorizationFrame

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

end WirePrimitive

end VisualProof
