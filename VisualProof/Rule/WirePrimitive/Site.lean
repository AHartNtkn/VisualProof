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

/-- Ordered typed tuples in one duplicate-free concrete context are
determined by their exact concrete wire origins. -/
theorem variables_eq_of_origins
    {argumentTypes : List Sig}
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (nodup : context.ids.Nodup)
    (left right : Vars context.sigs argumentTypes)
    (same :
      ConcreteElaboration.variableOrigins diagram context left =
        ConcreteElaboration.variableOrigins diagram context right) :
    left = right := by
  induction left with
  | nil =>
      cases right
      rfl
  | cons leftHead leftTail induction =>
      cases right with
      | cons rightHead rightTail =>
          simp only [ConcreteElaboration.variableOrigins, List.cons.injEq]
            at same
          have headExact :=
            InsertionCompilation.NaturalityInternal.origin_injective
              diagram context.ids nodup same.1
          subst rightHead
          exact congrArg (Vars.cons leftHead)
            (induction rightTail same.2)

/-- Renaming a typed tuple transports its concrete origin list pointwise
whenever the variable renaming implements the stated concrete wire map. -/
theorem variableOrigins_rename
    {argumentTypes : List Sig}
    (sourceDiagram : ConcreteDiagram sourceDefinitionCount)
    (targetDiagram : ConcreteDiagram targetDefinitionCount)
    (sourceContext : ConcreteElaboration.WireContext sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext targetDiagram)
    (rho : WireRenaming sourceContext.sigs targetContext.sigs)
    (wireMap : sourceDiagram.WireId → targetDiagram.WireId)
    (originExact :
      ∀ {signature} (value : Var sourceContext.sigs signature),
        ConcreteElaboration.WireContext.origin targetDiagram
            targetContext.ids (rho value) =
          wireMap (ConcreteElaboration.WireContext.origin sourceDiagram
            sourceContext.ids value))
    (variables : Vars sourceContext.sigs argumentTypes) :
    ConcreteElaboration.variableOrigins targetDiagram targetContext
        (Vars.rename rho variables) =
      (ConcreteElaboration.variableOrigins sourceDiagram sourceContext
        variables).map wireMap := by
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      simp only [Vars.rename, ConcreteElaboration.variableOrigins,
        List.map_cons]
      rw [originExact head, induction]

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

private theorem variableOrigins_length
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    {argumentSigs : List Sig}
    (values : Vars context.sigs argumentSigs) :
    (ConcreteElaboration.variableOrigins diagram context values).length =
      argumentSigs.length := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simp [ConcreteElaboration.variableOrigins, induction]

private theorem argumentOrigins_get
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (node : diagram.NodeId)
    (start : Nat)
    {argumentSigs : List Sig}
    (values : Vars context.sigs argumentSigs)
    (origins :
      ConcreteElaboration.ArgumentOrigins diagram context node start values)
    (index : Nat)
    (bound : index < argumentSigs.length) :
    diagram.endpointOwner? ⟨node, .arg (start + index)⟩ =
      some ((ConcreteElaboration.variableOrigins diagram context values).get
        ⟨index, by simpa [variableOrigins_length] using bound⟩) := by
  induction values generalizing start index with
  | nil => simp at bound
  | @cons signature rest head tail induction =>
      cases index with
      | zero =>
          simpa [ConcreteElaboration.ArgumentOrigins,
            ConcreteElaboration.variableOrigins] using origins.1
      | succ index =>
          have tailBound : index < rest.length := by simpa using bound
          have tailExact := induction (start := start + 1) origins.2
            index tailBound
          simpa [ConcreteElaboration.variableOrigins, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using tailExact

/-- The checked site frame also exposes the exact ordered concrete origins
of the compiled argument tuple. -/
theorem compiled_atom_arguments
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
          (outer.extend site.region).ids head = wire ∧
      ConcreteElaboration.variableOrigins source.val
          (outer.extend site.region) arguments = site.arguments := by
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
  obtain ⟨head, arguments, itemExact, headOrigin, argumentOrigins⟩ :=
    ConcreteElaboration.compileNodes?_atom_shape source.val
      (outer.extend site.region) site.node site.node_data singletonCompiled
  have itemSame : item = .atom head arguments :=
    ItemSeq.cons.inj itemExact |>.1
  subst item
  have exactHead :
      ConcreteElaboration.WireContext.origin source.val
          (outer.extend site.region).ids head = wire :=
    Option.some.inj (headOrigin.symm.trans site.endpoint_owner)
  have argumentsExact :
      ConcreteElaboration.variableOrigins source.val
          (outer.extend site.region) arguments = site.arguments := by
    apply List.ext_get
    · simpa [variableOrigins_length] using site.arguments_length.symm
    · intro index leftBound rightBound
      have compiledOwner := argumentOrigins_get source.val
        (outer.extend site.region) site.node 0 arguments argumentOrigins
        index (by
          rw [← variableOrigins_length source.val
            (outer.extend site.region) arguments]
          exact leftBound)
      have siteOwner := site.argument_owner index rightBound
      exact Option.some.inj (compiledOwner.symm.trans (by
        simpa using siteOwner))
  exact ⟨outer, visibleExact, head, arguments, singletonCompiled,
    exactHead, argumentsExact⟩

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

private theorem get_of_list_eq
    {left right : List α}
    (same : left = right)
    (position : Fin right.length) :
    left.get (Fin.cast (congrArg List.length same).symm position) =
      right.get position := by
  subst right
  rfl

private theorem eraseDups_length_le
    [BEq α] [LawfulBEq α] (values : List α) :
    values.eraseDups.length ≤ values.length := by
  match values with
  | [] => simp
  | head :: tail =>
      rw [List.eraseDups_cons]
      simp only [List.length_cons, Nat.succ_le_succ_iff]
      exact Nat.le_trans
        (eraseDups_length_le
          (tail.filter fun value => !value == head))
        (List.length_filter_le _ tail)
termination_by values.length
decreasing_by
  simpa using Nat.lt_succ_of_le (List.length_filter_le _ tail)

private theorem nodup_of_eraseDups_length_eq
    [BEq α] [LawfulBEq α]
    (values : List α)
    (exact : values.eraseDups.length = values.length) :
    values.Nodup := by
  match values with
  | [] => simp
  | head :: tail =>
      rw [List.eraseDups_cons] at exact
      simp only [List.length_cons, Nat.succ.injEq] at exact
      let retained := tail.filter fun value => !value == head
      have retainedLength : retained.length = tail.length := by
        apply Nat.le_antisymm
        · exact List.length_filter_le _ tail
        · rw [← exact]
          exact eraseDups_length_le retained
      have retainedEquality : retained = tail :=
        List.Sublist.eq_of_length List.filter_sublist retainedLength
      rw [List.nodup_cons]
      constructor
      · intro member
        have accepted : (!head == head) = true := by
          have : head ∈ retained := by
            rw [retainedEquality]
            exact member
          exact (List.mem_filter.mp this).2
        simp at accepted
      · apply nodup_of_eraseDups_length_eq tail
        simpa [retained, retainedEquality] using exact
termination_by values.length
decreasing_by simp_wf

private theorem component_sublist_flatMap
    (values : List α)
    (value : α)
    (member : value ∈ values)
    (function : α → List β) :
    (function value).Sublist (values.flatMap function) := by
  induction values with
  | nil => contradiction
  | cons head tail induction =>
      rw [List.mem_cons] at member
      cases member with
      | inl same =>
          subst head
          exact List.sublist_append_left _ _
      | inr member =>
          exact (induction member).trans
            (List.sublist_append_right _ _)

/-- Every exhaustive applied-site endpoint sequence is duplicate-free. -/
theorem endpoints_nodup
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (sites : AllAppliedSites source wire) :
    (sites.sites.map AppliedSite.endpoint).Nodup := by
  have allNodup :
      (source.val.endpointOccurrences.map Prod.snd).Nodup := by
    apply nodup_of_eraseDups_length_eq
    have exact := source.property.no_duplicate_endpoints
    unfold ConcreteDiagram.NoDuplicateEndpoints at exact
    simpa using exact
  have component :
      ((source.val.wires wire).endpoints.map fun endpoint =>
          (wire, endpoint)).Sublist source.val.endpointOccurrences := by
    unfold ConcreteDiagram.endpointOccurrences
    exact component_sublist_flatMap source.val.wiresList wire
      (Data.Finite.mem_allFin wire)
      (fun candidate =>
        (source.val.wires candidate).endpoints.map fun endpoint =>
          (candidate, endpoint))
  have endpointComponent := component.map Prod.snd
  have simplified :
      ((source.val.wires wire).endpoints.map fun endpoint =>
          (wire, endpoint)).map Prod.snd =
        (source.val.wires wire).endpoints := by
    simp [List.map_map, Function.comp_def]
  rw [simplified] at endpointComponent
  have localNodup := endpointComponent.nodup allNodup
  rw [sites.endpoints_exact]
  exact localNodup

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

/-- Transport one exhaustive applied-site position through an explicitly
supplied concrete isomorphism.  The target position is the dense index of the
mapped head occurrence in the target wire's exhaustive endpoint list. -/
def transportPosition
    {source target : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (iso : ConcreteIso source.val target.val)
    (sourceSites : AllAppliedSites source wire)
    (targetSites : AllAppliedSites target (iso.wires wire))
    (position : Fin sourceSites.sites.length) :
    Fin targetSites.sites.length :=
  let endpoint := (sourceSites.sites.get position).endpoint
  have sourceMember : endpoint ∈ (source.val.wires wire).endpoints := by
    rw [← sourceSites.exhaustive]
    exact List.mem_map.mpr
      ⟨sourceSites.sites.get position, List.get_mem _ _, rfl⟩
  let mapped := iso.endpointMap wire endpoint
  have targetMember :
      mapped ∈ (target.val.wires (iso.wires wire)).endpoints :=
    iso.endpointMap_mem wire endpoint sourceMember
  Fin.cast targetSites.length.symm <|
    DenseList.index (target.val.wires (iso.wires wire)).endpoints
      mapped targetMember

/-- The target site selected by `transportPosition` is exactly the source
head occurrence transported through the supplied isomorphism. -/
theorem transportPosition_endpoint
    {source target : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (iso : ConcreteIso source.val target.val)
    (sourceSites : AllAppliedSites source wire)
    (targetSites : AllAppliedSites target (iso.wires wire))
    (position : Fin sourceSites.sites.length) :
    (targetSites.sites.get
        (transportPosition iso sourceSites targetSites position)).endpoint =
      iso.endpointMap wire (sourceSites.sites.get position).endpoint := by
  let endpoint := (sourceSites.sites.get position).endpoint
  have sourceMember : endpoint ∈ (source.val.wires wire).endpoints := by
    rw [← sourceSites.exhaustive]
    exact List.mem_map.mpr
      ⟨sourceSites.sites.get position, List.get_mem _ _, rfl⟩
  let mapped := iso.endpointMap wire endpoint
  have targetMember :
      mapped ∈ (target.val.wires (iso.wires wire)).endpoints :=
    iso.endpointMap_mem wire endpoint sourceMember
  let endpointPosition :=
    DenseList.index (target.val.wires (iso.wires wire)).endpoints
      mapped targetMember
  have selected := get_of_list_eq targetSites.exhaustive endpointPosition
  have selectedPosition :
      Fin.cast (congrArg List.length targetSites.exhaustive).symm
          endpointPosition =
        Fin.cast (by simp)
          (transportPosition iso sourceSites targetSites position) := by
    apply Fin.ext
    rfl
  rw [selectedPosition] at selected
  have endpointExact :=
    DenseList.get_index
      (target.val.wires (iso.wires wire)).endpoints mapped targetMember
  rw [endpointExact] at selected
  simpa [endpoint, mapped] using selected

/-- Argument ownership at a transported applied-site position is exactly
the supplied concrete isomorphism's wire image of the source attachment. -/
theorem transportPosition_argument_owner
    {source target : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (iso : ConcreteIso source.val target.val)
    (sourceSites : AllAppliedSites source wire)
    (targetSites : AllAppliedSites target (iso.wires wire))
    (position : Fin sourceSites.sites.length)
    (index : Nat)
    (bound : index < (sourceSites.sites.get position).arguments.length) :
    target.val.endpointOwner?
        ⟨(targetSites.sites.get
          (transportPosition iso sourceSites targetSites position)).node,
          .arg index⟩ =
      some (iso.wires
        ((sourceSites.sites.get position).arguments[index]'bound)) := by
  let sourceSite := sourceSites.sites.get position
  let targetPosition :=
    transportPosition iso sourceSites targetSites position
  let targetSite := targetSites.sites.get targetPosition
  have sourceMember : sourceSite.endpoint ∈
      (source.val.wires wire).endpoints := by
    rw [← sourceSites.exhaustive]
    exact List.mem_map.mpr
      ⟨sourceSite, List.get_mem sourceSites.sites position, rfl⟩
  have corresponds :=
    iso.endpointMap_corresponds wire sourceSite.endpoint sourceMember
  have transportedEndpoint :=
    transportPosition_endpoint iso sourceSites targetSites position
  have nodeExact : targetSite.node = iso.nodes sourceSite.node := by
    change
      (targetSites.sites.get targetPosition).endpoint.node =
        iso.nodes sourceSite.endpoint.node
    rw [transportedEndpoint]
    exact corresponds.1
  have owner := iso.atom_owner_forward source.property target.property
    sourceSite.node_data (sourceSite.argument_owner index bound)
  change target.val.endpointOwner?
      ⟨targetSite.node, .arg index⟩ =
    some (iso.wires (sourceSite.arguments[index]'bound))
  rw [nodeExact]
  exact owner

/-- Pull one exhaustive target-site position back through the supplied
isomorphism's endpoint inverse. -/
def inverseTransportPosition
    {source target : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (iso : ConcreteIso source.val target.val)
    (sourceSites : AllAppliedSites source wire)
    (targetSites : AllAppliedSites target (iso.wires wire))
    (position : Fin targetSites.sites.length) :
    Fin sourceSites.sites.length :=
  let candidate := (targetSites.sites.get position).endpoint
  have targetMember :
      candidate ∈ (target.val.wires (iso.wires wire)).endpoints := by
    rw [← targetSites.exhaustive]
    exact List.mem_map.mpr
      ⟨targetSites.sites.get position, List.get_mem _ _, rfl⟩
  let endpoint := iso.endpointInverse wire candidate
  have sourceMember : endpoint ∈ (source.val.wires wire).endpoints :=
    iso.endpointInverse_mem wire candidate targetMember
  Fin.cast sourceSites.length.symm <|
    DenseList.index (source.val.wires wire).endpoints endpoint sourceMember

/-- The source site selected by `inverseTransportPosition` is exactly the
target head occurrence pulled back through the supplied isomorphism. -/
theorem inverseTransportPosition_endpoint
    {source target : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (iso : ConcreteIso source.val target.val)
    (sourceSites : AllAppliedSites source wire)
    (targetSites : AllAppliedSites target (iso.wires wire))
    (position : Fin targetSites.sites.length) :
    (sourceSites.sites.get
        (inverseTransportPosition iso sourceSites targetSites position)).endpoint =
      iso.endpointInverse wire
        (targetSites.sites.get position).endpoint := by
  let candidate := (targetSites.sites.get position).endpoint
  have targetMember :
      candidate ∈ (target.val.wires (iso.wires wire)).endpoints := by
    rw [← targetSites.exhaustive]
    exact List.mem_map.mpr
      ⟨targetSites.sites.get position, List.get_mem _ _, rfl⟩
  let endpoint := iso.endpointInverse wire candidate
  have sourceMember : endpoint ∈ (source.val.wires wire).endpoints :=
    iso.endpointInverse_mem wire candidate targetMember
  let endpointPosition :=
    DenseList.index (source.val.wires wire).endpoints endpoint sourceMember
  have selected := get_of_list_eq sourceSites.exhaustive endpointPosition
  have selectedPosition :
      Fin.cast (congrArg List.length sourceSites.exhaustive).symm
          endpointPosition =
        Fin.cast (by simp)
          (inverseTransportPosition iso sourceSites targetSites position) := by
    apply Fin.ext
    rfl
  rw [selectedPosition] at selected
  have endpointExact :=
    DenseList.get_index (source.val.wires wire).endpoints endpoint sourceMember
  rw [endpointExact] at selected
  simpa [candidate, endpoint] using selected

private theorem denseIndex_value_congr
    [DecidableEq α]
    (values : List α)
    {left right : α}
    (same : left = right)
    (leftMember : left ∈ values)
    (rightMember : right ∈ values) :
    DenseList.index values left leftMember =
      DenseList.index values right rightMember := by
  subst right
  rfl

private theorem get_injective_of_nodup
    [DecidableEq α]
    {values : List α}
    (nodup : values.Nodup) :
    Function.Injective values.get := by
  intro left right same
  calc
    left = DenseList.index values (values.get left)
        (List.get_mem values left) :=
      (DenseList.index_get values nodup left).symm
    _ = DenseList.index values (values.get right)
        (List.get_mem values right) :=
      denseIndex_value_congr values same _ _
    _ = right := DenseList.index_get values nodup right

/-- Exhaustive applied-site positions are transported bijectively through a
concrete isomorphism, using only its supplied endpoint correspondence. -/
def transportPositionEquiv
    {source target : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (iso : ConcreteIso source.val target.val)
    (sourceSites : AllAppliedSites source wire)
    (targetSites : AllAppliedSites target (iso.wires wire)) :
    Data.Finite.FiniteEquiv
      (Fin sourceSites.sites.length) (Fin targetSites.sites.length) where
  toFun := transportPosition iso sourceSites targetSites
  invFun := inverseTransportPosition iso sourceSites targetSites
  left_inv := by
    intro position
    let mapped := transportPosition iso sourceSites targetSites position
    let pulled :=
      inverseTransportPosition iso sourceSites targetSites mapped
    have pulledEndpoint :=
      inverseTransportPosition_endpoint iso sourceSites targetSites mapped
    rw [transportPosition_endpoint iso sourceSites targetSites position]
      at pulledEndpoint
    have sourceMember :
        (sourceSites.sites.get position).endpoint ∈
          (source.val.wires wire).endpoints := by
      rw [← sourceSites.exhaustive]
      exact List.mem_map.mpr
        ⟨sourceSites.sites.get position, List.get_mem _ _, rfl⟩
    rw [iso.endpointMap_left_inv wire
      (sourceSites.sites.get position).endpoint sourceMember]
      at pulledEndpoint
    have mappedGet :
        (sourceSites.sites.map AppliedSite.endpoint).get
            (Fin.cast (by simp) pulled) =
          (sourceSites.sites.map AppliedSite.endpoint).get
            (Fin.cast (by simp) position) := by
      simpa [pulled] using pulledEndpoint
    have castExact :=
      get_injective_of_nodup sourceSites.endpoints_nodup mappedGet
    apply Fin.ext
    simpa [pulled] using congrArg Fin.val castExact
  right_inv := by
    intro position
    let pulled :=
      inverseTransportPosition iso sourceSites targetSites position
    let mapped := transportPosition iso sourceSites targetSites pulled
    have mappedEndpoint :=
      transportPosition_endpoint iso sourceSites targetSites pulled
    rw [inverseTransportPosition_endpoint iso sourceSites targetSites position]
      at mappedEndpoint
    have targetMember :
        (targetSites.sites.get position).endpoint ∈
          (target.val.wires (iso.wires wire)).endpoints := by
      rw [← targetSites.exhaustive]
      exact List.mem_map.mpr
        ⟨targetSites.sites.get position, List.get_mem _ _, rfl⟩
    rw [iso.endpointMap_right_inv wire
      (targetSites.sites.get position).endpoint targetMember]
      at mappedEndpoint
    have mappedGet :
        (targetSites.sites.map AppliedSite.endpoint).get
            (Fin.cast (by simp) mapped) =
          (targetSites.sites.map AppliedSite.endpoint).get
            (Fin.cast (by simp) position) := by
      simpa [mapped] using mappedEndpoint
    have castExact :=
      get_injective_of_nodup targetSites.endpoints_nodup mappedGet
    apply Fin.ext
    simpa [mapped] using congrArg Fin.val castExact

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
