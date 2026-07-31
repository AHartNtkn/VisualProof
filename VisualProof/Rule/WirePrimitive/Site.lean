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

private theorem optionMapM_get
    (function : α → Option β) :
    ∀ (values : List α) (results : List β),
      values.mapM function = some results →
        ∀ (index : Nat) (bound : index < values.length),
          ∃ resultBound : index < results.length,
            function (values[index]'bound) = some (results[index]'resultBound)
  | [], results, accepted, index, bound => by simp at bound
  | value :: values, results, accepted, index, bound => by
      rw [List.mapM_cons] at accepted
      cases valueResult : function value with
      | none => simp [valueResult] at accepted
      | some result =>
          simp only [valueResult] at accepted
          cases tailResults : values.mapM function with
          | none => simp [tailResults] at accepted
          | some mapped =>
              have resultsExact : results = result :: mapped := by
                simpa [tailResults] using accepted.symm
              subst results
              cases index with
              | zero => exact ⟨by simp, by simpa using valueResult⟩
              | succ index =>
                  have tailBound : index < values.length := by
                    simpa using bound
                  obtain ⟨resultBound, exact⟩ :=
                    optionMapM_get function values mapped tailResults
                      index tailBound
                  exact ⟨by simp [resultBound], exact⟩

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

private theorem relation_signature_ne_argument
    (arguments : List Sig) (index : Fin arguments.length) :
    Sig.rel arguments ≠ arguments.get index := by
  intro same
  have smaller : sizeOf (arguments.get index) < sizeOf arguments :=
    List.sizeOf_lt_of_mem (List.get_mem arguments index)
  have larger : sizeOf arguments < sizeOf (Sig.rel arguments) := by
    simp_wf
  rw [same] at larger
  omega

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

/-- The checked argument tuple is the exact positional endpoint ownership. -/
theorem argument_owner
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (site : AppliedSite source wire)
    (index : Nat) (bound : index < site.arguments.length) :
    source.val.endpointOwner? ⟨site.node, .arg index⟩ =
      some (site.arguments[index]'bound) := by
  have signatureBound : index < site.argumentSignatures.length := by
    simpa [site.arguments_length] using bound
  obtain ⟨resultBound, exact⟩ :=
    optionMapM_get
      (fun position =>
        source.val.endpointOwner? ⟨site.node, .arg position⟩)
      (List.range site.argumentSignatures.length) site.arguments
      (by simpa [argumentWires?] using site.arguments_checked)
      index (by simpa using signatureBound)
  simpa using exact

/-- Every applied head carries exactly the acted relation signature. -/
theorem head_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (site : AppliedSite source wire) :
    (source.val.wires wire).sig = .rel site.argumentSignatures := by
  have checked :=
    (List.all_eq_true.mp source.property.atom_ports_typed)
      site.node (Data.Finite.mem_allFin site.node)
  rw [site.node_data] at checked
  simp only at checked
  rw [site.head_owner, Bool.and_eq_true] at checked
  exact eq_of_beq checked.1

/-- Every positional applied argument carries its declared signature. -/
theorem argument_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (site : AppliedSite source wire)
    (index : Nat) (bound : index < site.arguments.length) :
    (source.val.wires (site.arguments[index]'bound)).sig =
      site.argumentSignatures[index]'(by
        simpa [site.arguments_length] using bound) := by
  have signatureBound : index < site.argumentSignatures.length := by
    simpa [site.arguments_length] using bound
  have checked :=
    (List.all_eq_true.mp source.property.atom_ports_typed)
      site.node (Data.Finite.mem_allFin site.node)
  rw [site.node_data] at checked
  rw [Bool.and_eq_true] at checked
  have positionChecked :=
    (List.all_eq_true.mp checked.2)
      index (by simpa using signatureBound)
  rw [site.argument_owner index bound] at positionChecked
  simp only [List.getElem?_eq_getElem signatureBound] at positionChecked
  exact eq_of_beq positionChecked

/-- The acted head's scope encloses the applied atom region. -/
theorem head_visible
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (site : AppliedSite source wire) :
    source.val.Encloses (source.val.wires wire).scope site.region := by
  have occurrence := ConcreteDiagram.endpointOwner?_occurs source.val
    site.endpoint wire site.endpoint_owner
  have checked :=
    (List.all_eq_true.mp source.property.wire_scopes_enclose)
      (wire, site.endpoint) occurrence
  change decide
    (source.val.Encloses (source.val.wires wire).scope
      (source.val.nodes site.node).region) = true at checked
  rw [site.node_data] at checked
  exact of_decide_eq_true checked

/-- Every positional argument is visible at the applied atom region. -/
theorem argument_visible
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (site : AppliedSite source wire)
    (index : Nat) (bound : index < site.arguments.length) :
    source.val.Encloses
      (source.val.wires (site.arguments[index]'bound)).scope site.region := by
  let endpoint : CEndpoint source.val.nodeCount :=
    ⟨site.node, .arg index⟩
  have owner := site.argument_owner index bound
  have occurrence := ConcreteDiagram.endpointOwner?_occurs source.val
    endpoint (site.arguments[index]'bound) owner
  have checked :=
    (List.all_eq_true.mp source.property.wire_scopes_enclose)
      (site.arguments[index]'bound, endpoint) occurrence
  rw [site.node_data] at checked
  exact of_decide_eq_true checked

/-- A finite recursive relation signature cannot be one of its own arguments. -/
theorem argument_ne_head
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (site : AppliedSite source wire)
    (index : Nat) (bound : index < site.arguments.length) :
    site.arguments[index] ≠ wire := by
  intro same
  have argumentSignature := site.argument_signature index bound
  have relationSignature := site.head_signature
  rw [same, relationSignature] at argumentSignature
  exact relation_signature_ne_argument site.argumentSignatures
    ⟨index, by simpa [site.arguments_length] using bound⟩ argumentSignature

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

private theorem argumentWires?_complete
    (source : CheckedDiagram definitions)
    (node : source.val.NodeId)
    (region : source.val.RegionId)
    (signatures : List Sig)
    (nodeData : source.val.nodes node = .atom region signatures) :
    ∃ arguments,
      argumentWires? source node signatures.length = some arguments ∧
        arguments.length = signatures.length := by
  suffices complete :
      ∀ positions : List Nat,
        (∀ position, position ∈ positions → position < signatures.length) →
          ∃ arguments,
            positions.mapM (fun position =>
                source.val.endpointOwner? ⟨node, .arg position⟩) =
              some arguments ∧
            arguments.length = positions.length by
    simpa [argumentWires?] using
      complete (List.range signatures.length) (by
        intro position member
        exact List.mem_range.mp member)
  intro positions bounded
  induction positions with
  | nil =>
      exact ⟨[], rfl, rfl⟩
  | cons position rest induction =>
      have positionBound : position < signatures.length :=
        bounded position (by simp)
      obtain ⟨wire, owner⟩ :=
        ConcreteDiagram.endpointOwner?_complete definitions source.val
          source.property
          node (.arg position)
          (by
            simp [ConcreteDiagram.requiredPorts, nodeData, positionBound])
      obtain ⟨arguments, argumentsAccepted, argumentsLength⟩ :=
        induction (by
          intro candidate member
          exact bounded candidate (by simp [member]))
      refine ⟨wire :: arguments, ?_, ?_⟩
      · simp [owner, argumentsAccepted]
      · simp [argumentsLength]

/--
Every incident atom head accepted by the checked diagram can be recovered by
the executable applied-site checker.  No semantic evidence is supplied by the
caller: required-port ownership and the canonical site frame come from the
checked diagram itself.
-/
theorem checkAppliedSite_complete
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (endpoint : CEndpoint source.val.nodeCount)
    (member : endpoint ∈ (source.val.wires wire).endpoints)
    (head : endpoint.port = .head)
    (region : source.val.RegionId)
    (signatures : List Sig)
    (nodeData : source.val.nodes endpoint.node = .atom region signatures) :
    ∃ site,
      checkAppliedSite source wire endpoint = some site ∧
        site.endpoint = endpoint := by
  rcases endpoint with ⟨node, port⟩
  simp only at head
  subst port
  change source.val.nodes node = .atom region signatures at nodeData
  have owner :
      source.val.endpointOwner? ⟨node, .head⟩ = some wire :=
    ConcreteDiagram.endpointOwner?_eq_of_incident definitions source.val
      source.property node .head
      (by simp [ConcreteDiagram.requiredPorts, nodeData])
      wire member
  obtain ⟨arguments, argumentsAccepted, argumentsLength⟩ :=
    argumentWires?_complete source node region signatures nodeData
  obtain ⟨frame, frameAccepted⟩ := compileSite_complete source region
  let site : AppliedSite source wire :=
    AppliedSite.mk node region signatures arguments frame nodeData owner
      argumentsAccepted argumentsLength
  refine ⟨site, ?_, rfl⟩
  simp only [checkAppliedSite]
  split
  · rename_i actualRegion actualSignatures actualNodeData
    have same :
        CNode.atom actualRegion actualSignatures =
          CNode.atom region signatures :=
      actualNodeData.symm.trans nodeData
    cases same
    rw [dif_pos owner]
    split
    · rename_i rejected
      have impossible : (none : Option (List source.val.WireId)) =
          some arguments := rejected.symm.trans argumentsAccepted
      contradiction
    · rename_i actualArguments actualArgumentsAccepted
      have argumentsExact : actualArguments = arguments :=
        Option.some.inj
          (actualArgumentsAccepted.symm.trans argumentsAccepted)
      subst actualArguments
      rw [dif_pos argumentsLength]
      split
      · rename_i rejected
        have impossible : (none : Option (SiteCompilation source region)) =
            some frame := rejected.symm.trans frameAccepted
        contradiction
      · rename_i actualFrame actualFrameAccepted
        have frameExact : actualFrame = frame :=
          SiteCompilation.unique actualFrame frame
        subst actualFrame
        congr
  · rename_i impossible
    exact False.elim (impossible region signatures nodeData)

namespace AppliedSite

/-- Rechecking a checker-owned applied site returns that same receipt. -/
theorem checked
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (site : AppliedSite source wire) :
    checkAppliedSite source wire site.endpoint = some site := by
  cases site
  rename_i node region argumentSignatures arguments frame nodeExact headOwner
    argumentsChecked argumentsLength
  change checkAppliedSite source wire ⟨node, .head⟩ = _
  simp only [checkAppliedSite]
  split
  · rename_i actualRegion actualSignatures nodeData
    have same :
        CNode.atom actualRegion actualSignatures =
          CNode.atom region argumentSignatures :=
      nodeData.symm.trans nodeExact
    cases same
    obtain ⟨canonicalFrame, canonicalAccepted⟩ :=
      compileSite_complete source region
    have frameExact : canonicalFrame = frame :=
      SiteCompilation.unique canonicalFrame frame
    subst canonicalFrame
    rw [dif_pos headOwner]
    split
    · rename_i rejected
      have impossible : (none : Option (List source.val.WireId)) =
          some arguments := rejected.symm.trans argumentsChecked
      contradiction
    · rename_i actualArguments actualArgumentsAccepted
      have argumentsExact : actualArguments = arguments :=
        Option.some.inj (actualArgumentsAccepted.symm.trans argumentsChecked)
      subst actualArguments
      rw [dif_pos argumentsLength]
      split
      · rename_i rejected
        have impossible : (none : Option (SiteCompilation source region)) =
            some frame := rejected.symm.trans canonicalAccepted
        contradiction
      · rename_i actualFrame actualFrameAccepted
        have actualFrameExact : actualFrame = frame :=
          SiteCompilation.unique actualFrame frame
        subst actualFrame
        congr
  · rename_i impossible
    exact False.elim (impossible region argumentSignatures nodeExact)

end AppliedSite

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

private theorem appliedSites_mapM_complete
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId) :
    (endpoints : List (CEndpoint source.val.nodeCount)) →
    (∀ endpoint, endpoint ∈ endpoints →
      endpoint ∈ (source.val.wires wire).endpoints ∧
        endpoint.port = .head ∧
          ∃ region signatures,
            source.val.nodes endpoint.node = .atom region signatures) →
    ∃ sites,
      endpoints.mapM (checkAppliedSite source wire) = some sites ∧
        sites.map AppliedSite.endpoint = endpoints
  | [], _ => ⟨[], rfl, rfl⟩
  | endpoint :: rest, applied => by
      obtain ⟨member, head, region, signatures, nodeData⟩ :=
        applied endpoint (by simp)
      obtain ⟨site, siteAccepted, endpointExact⟩ :=
        checkAppliedSite_complete source wire endpoint
          member head region signatures nodeData
      obtain ⟨sites, sitesAccepted, endpointsExact⟩ :=
        appliedSites_mapM_complete source wire rest (by
          intro candidate member
          exact applied candidate (by simp [member]))
      refine ⟨site :: sites, ?_, ?_⟩
      · simp [siteAccepted, sitesAccepted]
      · simp [endpointExact, endpointsExact]

/--
If every concrete endpoint of a checked wire is an atom head, the executable
exhaustive-site checker succeeds.  This is the totality bridge used by the
strongest-form primitive compiler.
-/
theorem checkAllAppliedSites_complete
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (applied :
      ∀ endpoint,
        endpoint ∈ (source.val.wires wire).endpoints →
          endpoint.port = .head ∧
            ∃ region signatures,
              source.val.nodes endpoint.node = .atom region signatures) :
    ∃ all, checkAllAppliedSites source wire = some all := by
  obtain ⟨sites, sitesAccepted, endpointsExact⟩ :=
    appliedSites_mapM_complete source wire
      (source.val.wires wire).endpoints (by
        intro endpoint member
        exact ⟨member, applied endpoint member⟩)
  simp [checkAllAppliedSites, sitesAccepted, endpointsExact]

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

private theorem sites_mapM_checked
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId} :
    (sites : List (AppliedSite source wire)) →
      (sites.map AppliedSite.endpoint).mapM
          (checkAppliedSite source wire) =
        some sites
  | [] => rfl
  | site :: rest => by
      simp [site.checked, sites_mapM_checked rest]

/-- Rechecking an exhaustive checker-owned site list returns the same receipt. -/
theorem checked
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (all : AllAppliedSites source wire) :
    checkAllAppliedSites source wire = some all := by
  cases all
  rename_i sites endpointsExact
  have checkedEndpoints :
      (source.val.wires wire).endpoints.mapM
          (checkAppliedSite source wire) =
        some sites := by
    rw [← endpointsExact]
    exact sites_mapM_checked sites
  unfold checkAllAppliedSites
  rw [checkedEndpoints]
  simp only
  split
  · congr
  · rename_i rejected
    exact False.elim (rejected endpointsExact)

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

/--
Eliminate the sealed checker trace into a proposition. Downstream semantic
proofs receive only the exact applied site, its canonical checked erasure, and
the induction hypothesis for the checker-produced tail; the private trace
constructors remain unavailable.
-/
theorem Result.inductionOn
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (result : Result source wire)
    (motive :
      ∀ (source : CheckedDiagram definitions)
        (_wire : source.val.WireId)
        (target : CheckedDiagram definitions)
        (_targetWire : target.val.WireId),
        Prop)
    (done :
      ∀ (source : CheckedDiagram definitions)
        (wire : source.val.WireId)
        (_empty : (source.val.wires wire).endpoints = []),
        motive source wire source wire)
    (step :
      ∀ {source : CheckedDiagram definitions}
        {wire : source.val.WireId}
        (site : AppliedSite source wire)
        (erasure : CheckedErasure source site.node)
        {target : CheckedDiagram definitions}
        {targetWire : target.val.WireId},
        motive erasure.target (erasure.wireImage wire) target targetWire →
          motive source wire target targetWire) :
    motive source wire result.target result.targetWire := by
  rcases result with ⟨target, targetWire, trace⟩
  induction trace with
  | done source wire empty =>
      exact done source wire empty
  | step site erasure tail induction =>
      exact step site erasure induction

end AppliedSiteErasure

end WirePrimitive

end VisualProof
