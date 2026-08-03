import VisualProof.Diagram.Concrete.Subgraph.FactorizationNaturalitySupport

namespace VisualProof
namespace InsertionCompilation
namespace NaturalityInternal

theorem concreteAttachmentTargets_mem_iff
    {definitions : List (List Sig)}
    (base : CheckedDiagram definitions)
    (fragment : CheckedOpenDiagram definitions)
    (target :
      Fin fragment.val.boundary.length → base.val.WireId)
    (source : fragment.val.diagram.WireId)
    (wire : base.val.WireId) :
    wire ∈ concreteAttachmentTargets base fragment target source ↔
      ∃ position : Fin fragment.val.boundary.length,
        fragment.val.boundary.get position = source ∧
          target position = wire := by
  unfold concreteAttachmentTargets
  rw [List.mem_eraseDups, List.mem_filterMap]
  constructor
  · rintro ⟨position, _, emitted⟩
    split at emitted
    · rename_i sameSource
      exact
        ⟨position, sameSource,
          Option.some.inj emitted⟩
    · contradiction
  · rintro ⟨position, sameSource, rfl⟩
    refine ⟨position, Data.Finite.mem_allFin position, ?_⟩
    have sameSource' :
        fragment.val.boundary[position.val] = source := by
      simpa [List.get_eq_getElem] using sameSource
    simp [sameSource']

theorem identityRequest_components
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment)
    (request :
      ConcreteIdentityRequest base.val fragment.val.diagram)
    (member : request ∈ attachment.identityRequests) :
    request.source ∈ fragment.val.boundary ∧
      request.attachments =
        concreteAttachmentTargets base fragment attachment.target
          request.source ∧
      2 ≤ request.attachments.length := by
  rw [attachment.identityRequests_exact] at member
  unfold computedIdentityRequests at member
  rw [List.mem_eraseDups, List.mem_filterMap] at member
  rcases member with ⟨source, sourceMember, emitted⟩
  dsimp at emitted
  split at emitted
  · rename_i enough
    have requestEquality := Option.some.inj emitted |>.symm
    subst request
    refine ⟨?_, rfl, enough⟩
    simpa only [List.mem_eraseDups] using sourceMember
  · contradiction

private theorem identityRequest_for_source
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment)
    (source : fragment.val.diagram.WireId)
    (sourceMember : source ∈ fragment.val.boundary)
    (enough :
      2 ≤
        (concreteAttachmentTargets base fragment attachment.target
          source).length) :
    ({ source := source
       attachments :=
        concreteAttachmentTargets base fragment attachment.target source } :
      ConcreteIdentityRequest base.val fragment.val.diagram) ∈
        attachment.identityRequests := by
  rw [attachment.identityRequests_exact]
  unfold computedIdentityRequests
  rw [List.mem_eraseDups, List.mem_filterMap]
  refine ⟨source, ?_, ?_⟩
  · simpa only [List.mem_eraseDups] using sourceMember
  · dsimp
    rw [if_pos enough]

theorem identityNode_port_incident
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (identity : Fin attachment.identityRequests.length)
    (port :
      Fin (attachment.identityRequests.get identity).attachments.length) :
    (⟨attachment.identityNode identity, .identity port.val⟩ :
        CEndpoint attachment.diagram.nodeCount) ∈
      (attachment.diagram.wires
        (attachment.hostWire
          ((attachment.identityRequests.get identity).attachments.get
            port))).endpoints := by
  rw [compiled.host_wire_endpoints]
  apply List.mem_append_right
  apply
    (compiled.generatedEndpoint_mem_iff
      (attachment.hostWire
        ((attachment.identityRequests.get identity).attachments.get port))
      ⟨attachment.identityNode identity, .identity port.val⟩).mpr
  apply List.mem_append_right
  unfold ConcreteSpliceAttachment.identityEndpointOccurrences
  apply List.mem_flatMap.mpr
  refine ⟨identity, Data.Finite.mem_allFin identity, ?_⟩
  apply List.mem_map.mpr
  exact ⟨port, Data.Finite.mem_allFin port, rfl⟩

private theorem identityIncidentWires_mem_iff_attachment
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (identity : Fin attachment.identityRequests.length)
    (wire : attachment.diagram.WireId) :
    wire ∈
        attachment.diagram.identityIncidentWires
          (attachment.identityNode identity) ↔
      ∃ port :
          Fin
            (attachment.identityRequests.get identity).attachments.length,
        wire =
          attachment.hostWire
            ((attachment.identityRequests.get identity).attachments.get
              port) := by
  constructor
  · intro incident
    obtain ⟨endpoint, endpointIncident, nodeEquality⟩ :=
      (ConcreteDiagram.mem_identityIncidentWires attachment.diagram
        (attachment.identityNode identity) wire).mp incident
    rcases endpoint with ⟨node, portData⟩
    change node = attachment.identityNode identity at nodeEquality
    subst node
    have required :=
      ConcreteDiagram.incident_port_required definitions attachment.diagram
        compiled.generated_wellFormed wire
        (⟨attachment.identityNode identity, portData⟩ :
          CEndpoint attachment.diagram.nodeCount)
        endpointIncident
    change
      portData ∈
        attachment.diagram.requiredPorts
          (attachment.identityNode identity) at required
    unfold ConcreteDiagram.requiredPorts at required
    rw [compiled.identity_node] at required
    change
      portData ∈
        (List.range
          (attachment.identityRequests.get identity).attachments.length).map
            CPort.identity at required
    rcases List.mem_map.mp required with
      ⟨index, indexMember, portEquality⟩
    subst portData
    have bound : index <
        (attachment.identityRequests.get identity).attachments.length :=
      List.mem_range.mp indexMember
    let port :
        Fin
          (attachment.identityRequests.get identity).attachments.length :=
      ⟨index, bound⟩
    have actualOwner :=
      ConcreteDiagram.endpointOwner?_eq_of_incident definitions
        attachment.diagram compiled.generated_wellFormed
        (attachment.identityNode identity) (.identity index)
        (by
          unfold ConcreteDiagram.requiredPorts
          rw [compiled.identity_node]
          exact List.mem_map.mpr
            ⟨index, indexMember, rfl⟩)
        wire endpointIncident
    have expectedIncident :=
      identityNode_port_incident compiled identity port
    have expectedOwner :=
      ConcreteDiagram.endpointOwner?_eq_of_incident definitions
        attachment.diagram compiled.generated_wellFormed
        (attachment.identityNode identity) (.identity index)
        (by
          unfold ConcreteDiagram.requiredPorts
          rw [compiled.identity_node]
          exact List.mem_map.mpr
            ⟨index, indexMember, rfl⟩)
        (attachment.hostWire
          ((attachment.identityRequests.get identity).attachments.get port))
        expectedIncident
    exact
      ⟨port, Option.some.inj
        (actualOwner.symm.trans expectedOwner)⟩
  · rintro ⟨port, rfl⟩
    apply
      (ConcreteDiagram.mem_identityIncidentWires attachment.diagram
        (attachment.identityNode identity)
        (attachment.hostWire
          ((attachment.identityRequests.get identity).attachments.get
            port))).mpr
    exact
      ⟨⟨attachment.identityNode identity, .identity port.val⟩,
        identityNode_port_incident compiled identity port, rfl⟩

private def identityIncidentVars
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (context : ConcreteElaboration.WireContext diagram)
    (node : diagram.NodeId)
    (region : diagram.RegionId)
    (sig : Sig)
    (arity : Nat)
    (nodeData : diagram.nodes node = .identity region sig arity)
    (visible :
      ∀ wire, wire ∈ diagram.identityIncidentWires node →
        wire ∈ context.ids) :
    List
      (Var
        (context.ids.map fun wire => (diagram.wires wire).sig)
        sig) :=
  (diagram.identityIncidentWires node).attach.map fun attached =>
    castVar
      (ConcreteDiagram.identityIncidentWire_signature definitions diagram
        wellFormed nodeData attached.val attached.property)
      (varForMember diagram context.ids attached.val
        (visible attached.val attached.property))

private theorem identityIncident_visible
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (context : ConcreteElaboration.WireContext diagram)
    (node : diagram.NodeId)
    (region : diagram.RegionId)
    (sig : Sig)
    (arity : Nat)
    (nodeData : diagram.nodes node = .identity region sig arity)
    (items : ItemSeq definitions context.sigs)
    (compiled :
      ConcreteElaboration.compileNodes? definitions diagram context [node] =
        some items)
    (wire : diagram.WireId)
    (incident : wire ∈ diagram.identityIncidentWires node) :
    wire ∈ context.ids := by
  obtain ⟨ports, _, _, origins⟩ :=
    ConcreteElaboration.compileNodes?_identity_origins diagram wellFormed
      context node nodeData compiled
  obtain ⟨value, _, valueOrigin⟩ := (origins wire).mp incident
  rw [← valueOrigin]
  exact origin_member diagram context.ids value

private theorem identityIncidentVars_origins
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (context : ConcreteElaboration.WireContext diagram)
    (node : diagram.NodeId)
    (region : diagram.RegionId)
    (sig : Sig)
    (arity : Nat)
    (nodeData : diagram.nodes node = .identity region sig arity)
    (visible :
      ∀ wire, wire ∈ diagram.identityIncidentWires node →
        wire ∈ context.ids)
    (wire : diagram.WireId) :
    wire ∈ diagram.identityIncidentWires node ↔
      ∃ value ∈
          identityIncidentVars definitions diagram wellFormed context node
            region sig arity nodeData visible,
        ConcreteElaboration.WireContext.origin diagram context.ids value =
          wire := by
  constructor
  · intro member
    let attached :
        {wire // wire ∈ diagram.identityIncidentWires node} :=
      ⟨wire, member⟩
    let value :=
      castVar
        (ConcreteDiagram.identityIncidentWire_signature definitions diagram
          wellFormed nodeData wire member)
        (varForMember diagram context.ids wire (visible wire member))
    refine ⟨value, ?_, ?_⟩
    · unfold identityIncidentVars value
      apply List.mem_map.mpr
      exact ⟨attached, List.mem_attach _ _, rfl⟩
    · unfold value
      rw [origin_castVar, varForMember_origin]
  · rintro ⟨value, member, origin⟩
    unfold identityIncidentVars at member
    rcases List.mem_map.mp member with
      ⟨attached, _, valueEquality⟩
    subst value
    rw [origin_castVar, varForMember_origin] at origin
    simpa [origin] using attached.property

private theorem generatedTargetPacked_identityIncident
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (outer : ConcreteElaboration.WireContext base.val)
    (visibleEquality : compiled.site.frame.visible = outer.extend site)
    (targetAbove :
      ConcreteElaboration.ContextAbove attachment.diagram
        (hostContext attachment outer) (attachment.hostRegion site))
    (identity : Fin attachment.identityRequests.length)
    (items :
      ItemSeq definitions
        (generatedSiteContext attachment outer).sigs)
    (itemsCompiled :
      ConcreteElaboration.compileNodes? definitions attachment.diagram
          (generatedSiteContext attachment outer)
          [attachment.identityNode identity] =
        some items)
    (position : Fin fragment.val.boundary.length)
    (sameSource :
      fragment.val.boundary.get position =
        (attachment.identityRequests.get identity).source) :
    ∃ value ∈
        identityIncidentVars definitions attachment.diagram
          compiled.generated_wellFormed
          (generatedSiteContext attachment outer)
          (attachment.identityNode identity)
          (attachment.hostRegion site)
          (attachment.identityRequests.get identity).sig
          (attachment.identityRequests.get identity).attachments.length
          (compiled.identity_node identity)
          (identityIncident_visible definitions attachment.diagram
            compiled.generated_wellFormed
            (generatedSiteContext attachment outer)
            (attachment.identityNode identity)
            (attachment.hostRegion site)
            (attachment.identityRequests.get identity).sig
            (attachment.identityRequests.get identity).attachments.length
            (compiled.identity_node identity) items itemsCompiled),
      generatedTargetPacked compiled outer visibleEquality position =
        (⟨(attachment.identityRequests.get identity).sig, value⟩ :
          PackedVar (generatedSiteContext attachment outer).sigs) := by
  let request := attachment.identityRequests.get identity
  have requestMember : request ∈ attachment.identityRequests :=
    List.get_mem attachment.identityRequests identity
  have components :=
    identityRequest_components attachment request requestMember
  have targetMember : attachment.target position ∈ request.attachments := by
    rw [components.2.1]
    exact
      (concreteAttachmentTargets_mem_iff base fragment
        attachment.target request.source
        (attachment.target position)).mpr
        ⟨position, sameSource, rfl⟩
  let port :=
    DenseList.index request.attachments
      (attachment.target position) targetMember
  have incident :
      attachment.hostWire (attachment.target position) ∈
        attachment.diagram.identityIncidentWires
          (attachment.identityNode identity) := by
    apply
      (identityIncidentWires_mem_iff_attachment compiled identity
        (attachment.hostWire (attachment.target position))).mpr
    refine ⟨port, ?_⟩
    exact
      congrArg attachment.hostWire
        (DenseList.get_index request.attachments
          (attachment.target position) targetMember).symm
  have origins :=
    (identityIncidentVars_origins definitions attachment.diagram
      compiled.generated_wellFormed
      (generatedSiteContext attachment outer)
      (attachment.identityNode identity)
      (attachment.hostRegion site)
      request.sig request.attachments.length
      (compiled.identity_node identity)
      (identityIncident_visible definitions attachment.diagram
        compiled.generated_wellFormed
        (generatedSiteContext attachment outer)
        (attachment.identityNode identity)
        (attachment.hostRegion site)
        request.sig request.attachments.length
        (compiled.identity_node identity) items itemsCompiled)
      (attachment.hostWire (attachment.target position))).mp incident
  obtain ⟨value, valueMember, valueOrigin⟩ := origins
  refine ⟨value, valueMember, ?_⟩
  apply packedOrigin_injective attachment.diagram
    (generatedSiteContext attachment outer).ids
    (generatedSiteContext_nodup compiled outer targetAbove)
  exact
    (generatedTargetPacked_origin compiled outer visibleEquality
      position).trans valueOrigin.symm

private theorem identity_singleton_denotes_iff_incident
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (context : ConcreteElaboration.WireContext diagram)
    (contextNodup : context.ids.Nodup)
    (node : diagram.NodeId)
    (region : diagram.RegionId)
    (sig : Sig)
    (arity : Nat)
    (nodeData : diagram.nodes node = .identity region sig arity)
    (items : ItemSeq definitions context.sigs)
    (compiled :
      ConcreteElaboration.compileNodes? definitions diagram context [node] =
        some items)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context.sigs) :
    denoteItemSeq pre definitionEnv env items ↔
      AllEqual
        ((identityIncidentVars definitions diagram wellFormed context node
          region sig arity nodeData
          (identityIncident_visible definitions diagram wellFormed context
            node region sig arity nodeData items compiled)).map (env sig)) := by
  let visible :=
    identityIncident_visible definitions diagram wellFormed context node
      region sig arity nodeData items compiled
  change
    denoteItemSeq pre definitionEnv env items ↔
      AllEqual
        ((identityIncidentVars definitions diagram wellFormed context node
          region sig arity nodeData visible).map (env sig))
  obtain ⟨ports, two, itemsEquality, origins⟩ :=
    ConcreteElaboration.compileNodes?_identity_origins diagram wellFormed
      context node nodeData compiled
  subst items
  simp only [denoteItemSeq, and_true, denoteItem_identity]
  apply AllEqual.iff_of_mem_iff
  intro denoted
  constructor
  · intro portMember
    rcases List.mem_map.mp portMember with
      ⟨port, portIn, denotedEquality⟩
    let wire :=
      ConcreteElaboration.WireContext.origin diagram context.ids port
    have incident : wire ∈ diagram.identityIncidentWires node :=
      (origins wire).mpr ⟨port, portIn, rfl⟩
    have targetOrigin :=
      (identityIncidentVars_origins definitions diagram wellFormed context
        node region sig arity nodeData visible wire).mp incident
    obtain ⟨target, targetIn, targetOrigin⟩ := targetOrigin
    have portOrigin :
        ConcreteElaboration.WireContext.origin diagram context.ids port =
          wire := rfl
    have samePort : port = target :=
      origin_injective diagram context.ids contextNodup
        (portOrigin.trans targetOrigin.symm)
    exact List.mem_map.mpr
      ⟨target, targetIn, by simpa [samePort] using denotedEquality⟩
  · intro incidentMember
    rcases List.mem_map.mp incidentMember with
      ⟨incidentVar, incidentVarIn, denotedEquality⟩
    let wire :=
      ConcreteElaboration.WireContext.origin diagram context.ids incidentVar
    have incident : wire ∈ diagram.identityIncidentWires node :=
      (identityIncidentVars_origins definitions diagram wellFormed context
        node region sig arity nodeData visible wire).mpr
        ⟨incidentVar, incidentVarIn, rfl⟩
    obtain ⟨port, portIn, portOrigin⟩ := (origins wire).mp incident
    have incidentOrigin :
        ConcreteElaboration.WireContext.origin diagram context.ids
            incidentVar =
          wire := rfl
    have samePort : port = incidentVar :=
      origin_injective diagram context.ids contextNodup
        (portOrigin.trans incidentOrigin.symm)
    exact List.mem_map.mpr
      ⟨port, portIn, by simpa [samePort] using denotedEquality⟩

private def generatedIdentityRequestHolds
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (outer : ConcreteElaboration.WireContext base.val)
    (visibleEquality : compiled.site.frame.visible = outer.extend site)
    (env : Env pre (generatedSiteContext attachment outer).sigs)
    (identity : Fin attachment.identityRequests.length) : Prop :=
  ∀ left right : Fin fragment.val.boundary.length,
    fragment.val.boundary.get left =
        (attachment.identityRequests.get identity).source →
    fragment.val.boundary.get right =
        (attachment.identityRequests.get identity).source →
    evaluatePacked env
        (generatedTargetPacked compiled outer visibleEquality left) =
      evaluatePacked env
        (generatedTargetPacked compiled outer visibleEquality right)

private theorem identity_singleton_denotes_iff_request
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (outer : ConcreteElaboration.WireContext base.val)
    (visibleEquality : compiled.site.frame.visible = outer.extend site)
    (targetAbove :
      ConcreteElaboration.ContextAbove attachment.diagram
        (hostContext attachment outer) (attachment.hostRegion site))
    (identity : Fin attachment.identityRequests.length)
    (items :
      ItemSeq definitions
        (generatedSiteContext attachment outer).sigs)
    (itemsCompiled :
      ConcreteElaboration.compileNodes? definitions attachment.diagram
          (generatedSiteContext attachment outer)
          [attachment.identityNode identity] =
        some items)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre (generatedSiteContext attachment outer).sigs) :
    denoteItemSeq pre definitionEnv env items ↔
      generatedIdentityRequestHolds compiled outer visibleEquality env
        identity := by
  let request := attachment.identityRequests.get identity
  let visible :=
    identityIncident_visible definitions attachment.diagram
      compiled.generated_wellFormed
      (generatedSiteContext attachment outer)
      (attachment.identityNode identity)
      (attachment.hostRegion site) request.sig request.attachments.length
      (compiled.identity_node identity) items itemsCompiled
  let incidentVars :=
    identityIncidentVars definitions attachment.diagram
      compiled.generated_wellFormed
      (generatedSiteContext attachment outer)
      (attachment.identityNode identity)
      (attachment.hostRegion site) request.sig request.attachments.length
      (compiled.identity_node identity) visible
  rw [identity_singleton_denotes_iff_incident definitions
    attachment.diagram compiled.generated_wellFormed
    (generatedSiteContext attachment outer)
    (generatedSiteContext_nodup compiled outer targetAbove)
    (attachment.identityNode identity)
    (attachment.hostRegion site) request.sig request.attachments.length
    (compiled.identity_node identity) items itemsCompiled pre
    definitionEnv env]
  change
    AllEqual (incidentVars.map (env request.sig)) ↔
      ∀ left right : Fin fragment.val.boundary.length,
        fragment.val.boundary.get left = request.source →
        fragment.val.boundary.get right = request.source →
        evaluatePacked env
            (generatedTargetPacked compiled outer visibleEquality left) =
          evaluatePacked env
            (generatedTargetPacked compiled outer visibleEquality right)
  constructor
  · intro allEqual left right leftSource rightSource
    obtain ⟨leftValue, leftMember, leftPacked⟩ :=
      generatedTargetPacked_identityIncident compiled outer
        visibleEquality targetAbove identity items itemsCompiled left
        leftSource
    obtain ⟨rightValue, rightMember, rightPacked⟩ :=
      generatedTargetPacked_identityIncident compiled outer
        visibleEquality targetAbove identity items itemsCompiled right
        rightSource
    rw [leftPacked, rightPacked]
    exact congrArg
      (fun value => (⟨request.sig, value⟩ : Sigma pre.Domain))
      (allEqual
        (env request.sig leftValue)
        (List.mem_map.mpr ⟨leftValue, leftMember, rfl⟩)
        (env request.sig rightValue)
        (List.mem_map.mpr ⟨rightValue, rightMember, rfl⟩))
  · intro positionsEqual
    have locate :
        ∀ value ∈ incidentVars,
          ∃ position : Fin fragment.val.boundary.length,
            fragment.val.boundary.get position = request.source ∧
              generatedTargetPacked compiled outer visibleEquality
                  position =
                (⟨request.sig, value⟩ :
                  PackedVar
                    (generatedSiteContext attachment outer).sigs) := by
      intro value valueMember
      let originWire :=
        ConcreteElaboration.WireContext.origin attachment.diagram
          (generatedSiteContext attachment outer).ids value
      have incident :
          originWire ∈
            attachment.diagram.identityIncidentWires
              (attachment.identityNode identity) := by
        apply
          (identityIncidentVars_origins definitions attachment.diagram
            compiled.generated_wellFormed
            (generatedSiteContext attachment outer)
            (attachment.identityNode identity)
            (attachment.hostRegion site) request.sig
            request.attachments.length
            (compiled.identity_node identity) visible originWire).mpr
        exact ⟨value, valueMember, rfl⟩
      obtain ⟨port, wireEquality⟩ :=
        (identityIncidentWires_mem_iff_attachment compiled identity
          originWire).mp incident
      have requestMember : request ∈ attachment.identityRequests :=
        List.get_mem attachment.identityRequests identity
      have components :=
        identityRequest_components attachment request requestMember
      have attachmentMember :
          request.attachments.get port ∈
            concreteAttachmentTargets base fragment attachment.target
              request.source := by
        rw [← components.2.1]
        exact List.get_mem request.attachments port
      obtain ⟨position, sameSource, targetEquality⟩ :=
        (concreteAttachmentTargets_mem_iff base fragment
          attachment.target request.source
          (request.attachments.get port)).mp attachmentMember
      refine ⟨position, sameSource, ?_⟩
      apply packedOrigin_injective attachment.diagram
        (generatedSiteContext attachment outer).ids
        (generatedSiteContext_nodup compiled outer targetAbove)
      exact
        (generatedTargetPacked_origin compiled outer visibleEquality
          position).trans
          ((congrArg attachment.hostWire targetEquality).trans
            wireEquality.symm)
    intro leftValue leftMember rightValue rightMember
    rcases List.mem_map.mp leftMember with
      ⟨leftVar, leftVarMember, rfl⟩
    rcases List.mem_map.mp rightMember with
      ⟨rightVar, rightVarMember, rfl⟩
    obtain ⟨leftPosition, leftSource, leftPacked⟩ :=
      locate leftVar leftVarMember
    obtain ⟨rightPosition, rightSource, rightPacked⟩ :=
      locate rightVar rightVarMember
    have packedValuesEqual :=
      positionsEqual leftPosition rightPosition leftSource rightSource
    rw [leftPacked, rightPacked] at packedValuesEqual
    exact eq_of_heq (Sigma.mk.inj packedValuesEqual).2

theorem identityNodes_denote_iff_requests
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (outer : ConcreteElaboration.WireContext base.val)
    (visibleEquality : compiled.site.frame.visible = outer.extend site)
    (targetAbove :
      ConcreteElaboration.ContextAbove attachment.diagram
        (hostContext attachment outer) (attachment.hostRegion site))
    (indices : List (Fin attachment.identityRequests.length))
    (items :
      ItemSeq definitions
        (generatedSiteContext attachment outer).sigs)
    (itemsCompiled :
      ConcreteElaboration.compileNodes? definitions attachment.diagram
          (generatedSiteContext attachment outer)
          (indices.map attachment.identityNode) =
        some items)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre (generatedSiteContext attachment outer).sigs) :
    denoteItemSeq pre definitionEnv env items ↔
      ∀ identity, identity ∈ indices →
        generatedIdentityRequestHolds compiled outer visibleEquality env
          identity := by
  induction indices generalizing items with
  | nil =>
      rw [ConcreteElaboration.compileNodes?_equation] at itemsCompiled
      have itemsEquality :
          (.nil : ItemSeq definitions
            (generatedSiteContext attachment outer).sigs) = items :=
        Option.some.inj itemsCompiled
      rw [← itemsEquality]
      simp [denoteItemSeq]
  | cons identity tail induction =>
      obtain ⟨headItem, tailItems, headCompiled, tailCompiled,
          itemsEquality⟩ :=
        compileNodes_cons_components definitions attachment.diagram
          (generatedSiteContext attachment outer)
          (attachment.identityNode identity)
          (tail.map attachment.identityNode) items
          (by simpa using itemsCompiled)
      subst items
      have headNatural :=
        identity_singleton_denotes_iff_request compiled outer
          visibleEquality targetAbove identity (.cons headItem .nil)
          headCompiled pre definitionEnv env
      have tailNatural :=
        induction tailItems tailCompiled
      simpa only [denoteItemSeq_cons, denoteItemSeq_nil, and_true,
        List.mem_cons, forall_eq_or_imp] using
          and_congr headNatural tailNatural

private def generatedIdentityPositionsHold
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (outer : ConcreteElaboration.WireContext base.val)
    (visibleEquality : compiled.site.frame.visible = outer.extend site)
    (env : Env pre (generatedSiteContext attachment outer).sigs) : Prop :=
  ∀ left right : Fin fragment.val.boundary.length,
    fragment.val.boundary.get left =
        fragment.val.boundary.get right →
    evaluatePacked env
        (generatedTargetPacked compiled outer visibleEquality left) =
      evaluatePacked env
        (generatedTargetPacked compiled outer visibleEquality right)

theorem generatedIdentityRequests_iff_positions
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (outer : ConcreteElaboration.WireContext base.val)
    (visibleEquality : compiled.site.frame.visible = outer.extend site)
    (targetAbove :
      ConcreteElaboration.ContextAbove attachment.diagram
        (hostContext attachment outer) (attachment.hostRegion site))
    (env : Env pre (generatedSiteContext attachment outer).sigs) :
    (∀ identity,
        identity ∈
            Data.Finite.allFin attachment.identityRequests.length →
          generatedIdentityRequestHolds compiled outer visibleEquality env
            identity) ↔
      generatedIdentityPositionsHold compiled outer visibleEquality env := by
  constructor
  · intro requests left right sameSource
    by_cases sameTarget :
        attachment.target left = attachment.target right
    · have samePacked :
          generatedTargetPacked compiled outer visibleEquality left =
            generatedTargetPacked compiled outer visibleEquality right := by
        apply packedOrigin_injective attachment.diagram
          (generatedSiteContext attachment outer).ids
          (generatedSiteContext_nodup compiled outer targetAbove)
        rw [generatedTargetPacked_origin, generatedTargetPacked_origin,
          sameTarget]
      exact congrArg (evaluatePacked env) samePacked
    · let source := fragment.val.boundary.get left
      let targets :=
        concreteAttachmentTargets base fragment attachment.target source
      have sourceMember : source ∈ fragment.val.boundary :=
        List.get_mem fragment.val.boundary left
      have leftMember : attachment.target left ∈ targets := by
        exact
          (concreteAttachmentTargets_mem_iff base fragment
            attachment.target source (attachment.target left)).mpr
            ⟨left, rfl, rfl⟩
      have rightMember : attachment.target right ∈ targets := by
        exact
          (concreteAttachmentTargets_mem_iff base fragment
            attachment.target source (attachment.target right)).mpr
            ⟨right, sameSource.symm, rfl⟩
      have enough : 2 ≤ targets.length := by
        cases targetsEquation : targets with
        | nil => simp [targetsEquation] at leftMember
        | cons head tail =>
            cases tailEquation : tail with
            | nil =>
                simp only [targetsEquation, tailEquation,
                  List.mem_singleton] at leftMember rightMember
                exact
                  (sameTarget
                    (leftMember.trans rightMember.symm)).elim
            | cons next rest =>
                simp
      let request :
          ConcreteIdentityRequest base.val fragment.val.diagram :=
        { source := source
          attachments := targets }
      have requestMember : request ∈ attachment.identityRequests :=
        identityRequest_for_source attachment source sourceMember enough
      let identity :=
        DenseList.index attachment.identityRequests request requestMember
      have requestAt :
          attachment.identityRequests.get identity = request :=
        DenseList.get_index attachment.identityRequests request requestMember
      have requestHolds :=
        requests identity (Data.Finite.mem_allFin identity)
      unfold generatedIdentityRequestHolds at requestHolds
      rw [requestAt] at requestHolds
      exact requestHolds left right rfl sameSource.symm
  · intro positions identity _
    intro left right leftSource rightSource
    exact
      positions left right (leftSource.trans rightSource.symm)

theorem generatedIdentityPositions_iff_boundaryDenote
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (outer : ConcreteElaboration.WireContext base.val)
    (visibleEquality : compiled.site.frame.visible = outer.extend site)
    (env : Env pre (generatedSiteContext attachment outer).sigs) :
    generatedIdentityPositionsHold compiled outer visibleEquality env ↔
      Vars.denote
          (Env.comp
            (generatedFrameEnvironment compiled outer visibleEquality env)
            compiled.intrinsicAttachment.classMap)
          fragmentCompiled.boundary =
        Vars.denote
          (generatedFrameEnvironment compiled outer visibleEquality env)
          compiled.targets.positions := by
  let frameEnv :=
    generatedFrameEnvironment compiled outer visibleEquality env
  constructor
  · intro positionsHold
    apply Vars.denote_eq_of_entries
    intro tuplePosition
    let position : Fin fragment.val.boundary.length :=
      ⟨tuplePosition.val, by
        simpa only [checkedBoundarySigs, List.length_map]
          using tuplePosition.isLt⟩
    change
      evaluatePacked
          (Env.comp frameEnv
            compiled.intrinsicAttachment.classMap)
          (fragmentCompiled.boundaryPackedAt position) =
        evaluatePacked frameEnv
          (compiled.targetPackedAt position)
    rcases boundaryEquation :
        fragmentCompiled.boundaryPackedAt position with
      ⟨sig, fiber⟩
    let source :=
      ExtractedBoundaryCompiler.wireOfPacked
        fragment.val.diagram
        (ConcreteElaboration.openBoundaryWires fragment.val)
        (⟨sig, fiber⟩ :
          PackedVar fragmentCompiled.openDiagram.classes)
    let member := compiled.intrinsicClassWire_mem_boundary fiber
    let representative :=
      attachment.representativePosition source member
    have classPackedEquality :
        (⟨sig, compiled.intrinsicAttachment.classMap fiber⟩ :
            PackedVar compiled.site.frame.visible.sigs) =
          compiled.targetPackedAt representative := by
      simpa only [source, member, representative] using
        compiled.intrinsicAttachment_classMap_eq_representative fiber
    have boundaryOrigin :=
      fragmentCompiled.boundaryPackedAt_origin position
    rw [boundaryEquation] at boundaryOrigin
    have representativeSource :
        fragment.val.boundary.get representative =
          fragment.val.boundary.get position := by
      calc
        fragment.val.boundary.get representative = source :=
          DenseList.get_index fragment.val.boundary source member
        _ = fragment.val.boundary.get position := by
          simpa only [source] using boundaryOrigin
    have representativeValue :=
      positionsHold representative position representativeSource
    have frameTargetsEqual :
        evaluatePacked frameEnv
            (compiled.targetPackedAt representative) =
          evaluatePacked frameEnv
            (compiled.targetPackedAt position) := by
      calc
        evaluatePacked frameEnv
            (compiled.targetPackedAt representative) =
            evaluatePacked env
              (generatedTargetPacked compiled outer visibleEquality
                representative) :=
          (evaluate_generatedTargetPacked compiled outer visibleEquality
            env representative).symm
        _ = evaluatePacked env
              (generatedTargetPacked compiled outer visibleEquality
                position) :=
          representativeValue
        _ = evaluatePacked frameEnv
              (compiled.targetPackedAt position) :=
          evaluate_generatedTargetPacked compiled outer visibleEquality
            env position
    exact
      (congrArg (evaluatePacked frameEnv) classPackedEquality).trans
        frameTargetsEqual
  · intro boundaryDenote left right sameSource
    let leftTuple :
        Fin (checkedBoundarySigs fragment).length :=
      ⟨left.val, by
        simpa only [checkedBoundarySigs, List.length_map]
          using left.isLt⟩
    let rightTuple :
        Fin (checkedBoundarySigs fragment).length :=
      ⟨right.val, by
        simpa only [checkedBoundarySigs, List.length_map]
          using right.isLt⟩
    have leftEntry :=
      Vars.entries_eq_of_denote
        (Env.comp frameEnv
          compiled.intrinsicAttachment.classMap)
        frameEnv fragmentCompiled.boundary
        compiled.targets.positions boundaryDenote leftTuple
    have rightEntry :=
      Vars.entries_eq_of_denote
        (Env.comp frameEnv
          compiled.intrinsicAttachment.classMap)
        frameEnv fragmentCompiled.boundary
        compiled.targets.positions boundaryDenote rightTuple
    change
      evaluatePacked
          (Env.comp frameEnv
            compiled.intrinsicAttachment.classMap)
          (fragmentCompiled.boundaryPackedAt left) =
        evaluatePacked frameEnv
          (compiled.targetPackedAt left)
      at leftEntry
    change
      evaluatePacked
          (Env.comp frameEnv
            compiled.intrinsicAttachment.classMap)
          (fragmentCompiled.boundaryPackedAt right) =
        evaluatePacked frameEnv
          (compiled.targetPackedAt right)
      at rightEntry
    have boundaryPackedEqual :
        fragmentCompiled.boundaryPackedAt left =
          fragmentCompiled.boundaryPackedAt right :=
      (fragmentCompiled.boundaryPackedAt_eq_iff left right).mpr sameSource
    have frameTargetsEqual :
        evaluatePacked frameEnv
            (compiled.targetPackedAt left) =
          evaluatePacked frameEnv
            (compiled.targetPackedAt right) := by
      exact leftEntry.symm.trans
        ((congrArg
          (evaluatePacked
            (Env.comp frameEnv
              compiled.intrinsicAttachment.classMap))
          boundaryPackedEqual).trans rightEntry)
    calc
      evaluatePacked env
          (generatedTargetPacked compiled outer visibleEquality left) =
          evaluatePacked frameEnv (compiled.targetPackedAt left) :=
        evaluate_generatedTargetPacked compiled outer visibleEquality
          env left
      _ = evaluatePacked frameEnv (compiled.targetPackedAt right) :=
        frameTargetsEqual
      _ = evaluatePacked env
          (generatedTargetPacked compiled outer visibleEquality right) :=
        (evaluate_generatedTargetPacked compiled outer visibleEquality
          env right).symm

private theorem hostRegion_injective
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment) :
    Function.Injective attachment.hostRegion := by
  intro left right same
  apply Fin.ext
  simpa [ConcreteSpliceAttachment.hostRegion] using congrArg Fin.val same

private theorem fragmentRegion_eq_hostRegion_iff
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (fragmentRegion : fragment.val.diagram.RegionId)
    (hostRegion : base.val.RegionId) :
    attachment.fragmentRegion fragmentRegion =
        attachment.hostRegion hostRegion ↔
      fragmentRegion = fragment.val.diagram.root ∧ hostRegion = site := by
  constructor
  · intro same
    have atSite :
        attachment.fragmentRegion fragmentRegion =
          attachment.hostRegion site ↔
        fragmentRegion = fragment.val.diagram.root :=
      compiled.fragmentRegion_eq_site_iff fragmentRegion
    have hostSame : hostRegion = site := by
      by_cases root : fragmentRegion = fragment.val.diagram.root
      · apply hostRegion_injective attachment
        simpa [root, ConcreteSpliceAttachment.fragmentRegion] using same.symm
      · unfold ConcreteSpliceAttachment.fragmentRegion at same
        simp only [root, ↓reduceDIte] at same
        exact
          (attachment.hostRegion_ne_freshRegion hostRegion _ same.symm).elim
    refine ⟨?_, hostSame⟩
    rw [hostSame] at same
    exact atSite.mp same
  · rintro ⟨rfl, rfl⟩
    simp [ConcreteSpliceAttachment.fragmentRegion]

private theorem hostWires_offsite
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (region : base.val.RegionId)
    (notSite : region ≠ site) :
    attachment.diagram.wiresAt (attachment.hostRegion region) =
      (base.val.wiresAt region).map attachment.hostWire := by
  have hostFilter :
      (Data.Finite.allFin base.val.wireCount).filter
          (fun wire =>
            (attachment.diagram.wires
                (attachment.hostWire wire)).scope ==
              attachment.hostRegion region) =
        base.val.wiresAt region := by
    unfold ConcreteDiagram.wiresAt ConcreteDiagram.wiresList
    apply List.filter_congr
    intro wire _
    simp only [ConcreteSpliceAttachment.diagram_wire_hostWire_scope]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact
      ⟨fun same => hostRegion_injective attachment same,
        fun same => congrArg attachment.hostRegion same⟩
  have freshFilter :
      (Data.Finite.allFin
          attachment.fragmentInternalWires.length).filter
          (fun fresh =>
            (attachment.diagram.wires
                (attachment.freshWire fresh)).scope ==
              attachment.hostRegion region) =
        [] := by
    apply List.filter_eq_nil_iff.mpr
    intro fresh _
    simp only [
      ConcreteSpliceAttachment.diagram_wire_freshWire_scope]
    intro equalTrue
    have same := eq_of_beq equalTrue
    have atSite :=
      (fragmentRegion_eq_hostRegion_iff compiled
        (fragment.val.diagram.wires
          (attachment.fragmentInternalWires.get fresh)).scope
        region).mp same
    exact notSite atSite.2
  unfold ConcreteDiagram.wiresAt ConcreteDiagram.wiresList
  change
    (Data.Finite.allFin attachment.wireCount).filter _ = _
  rw [compiled.wire_allocations, List.filter_append,
    List.filter_map, List.filter_map]
  change
    List.map attachment.hostWire
          ((Data.Finite.allFin base.val.wireCount).filter
            (fun wire =>
              (attachment.diagram.wires
                  (attachment.hostWire wire)).scope ==
                attachment.hostRegion region)) ++
        List.map attachment.freshWire
          ((Data.Finite.allFin
            attachment.fragmentInternalWires.length).filter
            (fun fresh =>
              (attachment.diagram.wires
                  (attachment.freshWire fresh)).scope ==
                attachment.hostRegion region)) =
      _
  rw [hostFilter, freshFilter]
  simp [ConcreteDiagram.wiresAt, ConcreteDiagram.wiresList]

theorem hostNodes_offsite
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (region : base.val.RegionId)
    (notSite : region ≠ site) :
    attachment.diagram.nodesAt (attachment.hostRegion region) =
      (base.val.nodesAt region).map attachment.hostNode := by
  have hostFilter :
      (Data.Finite.allFin base.val.nodeCount).filter
          (fun node =>
            (attachment.diagram.nodes
                (attachment.hostNode node)).region ==
              attachment.hostRegion region) =
        base.val.nodesAt region := by
    unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList
    apply List.filter_congr
    intro node _
    simp only [ConcreteSpliceAttachment.diagram_node_hostNode_region]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact
      ⟨fun same => hostRegion_injective attachment same,
        fun same => congrArg attachment.hostRegion same⟩
  have fragmentFilter :
      (Data.Finite.allFin fragment.val.diagram.nodeCount).filter
          (fun node =>
            (attachment.diagram.nodes
                (attachment.fragmentNode node)).region ==
              attachment.hostRegion region) =
        [] := by
    apply List.filter_eq_nil_iff.mpr
    intro node _
    simp only [ConcreteSpliceAttachment.diagram_node_fragmentNode_region]
    intro equalTrue
    have same := eq_of_beq equalTrue
    have atSite :=
      (fragmentRegion_eq_hostRegion_iff compiled
        (fragment.val.diagram.nodes node).region region).mp same
    exact notSite atSite.2
  have identityFilter :
      (Data.Finite.allFin attachment.identityRequests.length).filter
          (fun identity =>
            (attachment.diagram.nodes
                (attachment.identityNode identity)).region ==
              attachment.hostRegion region) =
        [] := by
    apply List.filter_eq_nil_iff.mpr
    intro identity _
    rw [ConcreteSpliceAttachment.diagram_node_identityNode]
    simp only [CNode.region]
    intro equalTrue
    have mappedSame :
        attachment.hostRegion site =
          attachment.hostRegion region := by
      simpa only [beq_iff_eq] using equalTrue
    have same := hostRegion_injective attachment mappedSame
    exact notSite same.symm
  unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList
  change
    (Data.Finite.allFin attachment.nodeCount).filter _ = _
  rw [compiled.node_allocations, List.filter_append,
    List.filter_append, List.filter_map, List.filter_map,
    List.filter_map]
  change
    List.map attachment.hostNode
          ((Data.Finite.allFin base.val.nodeCount).filter
            (fun node =>
              (attachment.diagram.nodes
                  (attachment.hostNode node)).region ==
                attachment.hostRegion region)) ++
        List.map attachment.fragmentNode
          ((Data.Finite.allFin
            fragment.val.diagram.nodeCount).filter
            (fun node =>
              (attachment.diagram.nodes
                  (attachment.fragmentNode node)).region ==
                attachment.hostRegion region)) ++
        List.map attachment.identityNode
          ((Data.Finite.allFin
            attachment.identityRequests.length).filter
            (fun identity =>
              (attachment.diagram.nodes
                  (attachment.identityNode identity)).region ==
                attachment.hostRegion region)) =
      _
  rw [hostFilter, fragmentFilter, identityFilter]
  simp [ConcreteDiagram.nodesAt, ConcreteDiagram.nodesList]

theorem hostChildren_offsite
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (region : base.val.RegionId)
    (notSite : region ≠ site) :
    attachment.diagram.childrenOf (attachment.hostRegion region) =
      (base.val.childrenOf region).map attachment.hostRegion := by
  let targetIsChild : attachment.diagram.RegionId → Bool :=
    fun child =>
      match attachment.diagram.regions child with
      | .sheet => false
      | .cut parent => parent == attachment.hostRegion region
  let sourceIsChild : base.val.RegionId → Bool :=
    fun child =>
      match base.val.regions child with
      | .sheet => false
      | .cut parent => parent == region
  have targetChildren :
      attachment.diagram.childrenOf (attachment.hostRegion region) =
        attachment.diagram.regionsList.filter targetIsChild := by
    unfold ConcreteDiagram.childrenOf
    apply List.filter_congr
    intro child _
    unfold targetIsChild
    cases attachment.diagram.regions child <;> rfl
  have sourceChildren :
      base.val.childrenOf region =
        base.val.regionsList.filter sourceIsChild := by
    unfold ConcreteDiagram.childrenOf
    apply List.filter_congr
    intro child _
    unfold sourceIsChild
    cases base.val.regions child <;> rfl
  have hostFilter :
      (Data.Finite.allFin base.val.regionCount).filter
          (targetIsChild ∘ attachment.hostRegion) =
        (Data.Finite.allFin base.val.regionCount).filter
          sourceIsChild := by
    apply List.filter_congr
    intro child _
    simp only [Function.comp_apply]
    unfold targetIsChild sourceIsChild
    rw [ConcreteSpliceAttachment.diagram_region_hostRegion]
    cases data : base.val.regions child with
    | sheet =>
        simp [mapRegion]
    | cut parent =>
        simp only [mapRegion]
        apply Bool.eq_iff_iff.mpr
        simp only [beq_iff_eq]
        exact
          ⟨fun same => hostRegion_injective attachment same,
            fun same => congrArg attachment.hostRegion same⟩
  have freshFilter :
      (Data.Finite.allFin attachment.fragmentRegions.length).filter
          (targetIsChild ∘ attachment.freshRegion) =
        [] := by
    apply List.filter_eq_nil_iff.mpr
    intro fresh _
    simp only [Function.comp_apply]
    unfold targetIsChild
    rw [ConcreteSpliceAttachment.diagram_region_freshRegion]
    cases data :
        fragment.val.diagram.regions
          (attachment.fragmentRegions.get fresh) with
    | sheet =>
        simp [mapRegion]
    | cut parent =>
        simp only [mapRegion]
        intro equalTrue
        have same :
            attachment.fragmentRegion parent =
              attachment.hostRegion region := by
          simpa only [beq_iff_eq] using equalTrue
        have atSite :=
          (fragmentRegion_eq_hostRegion_iff compiled parent region).mp same
        exact notSite atSite.2
  rw [targetChildren, sourceChildren]
  have allocations :
      attachment.diagram.regionsList =
        (Data.Finite.allFin base.val.regionCount).map
            attachment.hostRegion ++
          (Data.Finite.allFin
            attachment.fragmentRegions.length).map
              attachment.freshRegion := by
    unfold ConcreteDiagram.regionsList
    change Data.Finite.allFin attachment.regionCount = _
    exact compiled.region_allocations
  have allocatedFilter :=
    congrArg (List.filter targetIsChild) allocations
  have expandedFilter :
      attachment.diagram.regionsList.filter targetIsChild =
        List.map attachment.hostRegion
            ((Data.Finite.allFin base.val.regionCount).filter
              (targetIsChild ∘ attachment.hostRegion)) ++
          List.map attachment.freshRegion
            ((Data.Finite.allFin
              attachment.fragmentRegions.length).filter
              (targetIsChild ∘ attachment.freshRegion)) := by
    refine allocatedFilter.trans ?_
    calc
      List.filter _
          (List.map attachment.hostRegion
              (Data.Finite.allFin base.val.regionCount) ++
            List.map attachment.freshRegion
              (Data.Finite.allFin
                attachment.fragmentRegions.length)) =
          List.filter _
              (List.map attachment.hostRegion
                (Data.Finite.allFin base.val.regionCount)) ++
            List.filter _
              (List.map attachment.freshRegion
                (Data.Finite.allFin
                  attachment.fragmentRegions.length)) :=
        List.filter_append _ _
      _ =
          List.map attachment.hostRegion
              ((Data.Finite.allFin base.val.regionCount).filter
                (_ ∘ attachment.hostRegion)) ++
            List.filter _
              (List.map attachment.freshRegion
                (Data.Finite.allFin
                  attachment.fragmentRegions.length)) :=
        congrArg
          (fun hostPart =>
            hostPart ++
              List.filter _
                (List.map attachment.freshRegion
                  (Data.Finite.allFin
                    attachment.fragmentRegions.length)))
          List.filter_map
      _ = _ :=
        congrArg
          (fun freshPart =>
            List.map attachment.hostRegion
                ((Data.Finite.allFin base.val.regionCount).filter
                  (_ ∘ attachment.hostRegion)) ++
              freshPart)
          List.filter_map
  rw [expandedFilter]
  have hostMapped :=
    congrArg (List.map attachment.hostRegion) hostFilter
  rw [hostMapped]
  have freshMapped :
      List.map attachment.freshRegion
          ((Data.Finite.allFin
            attachment.fragmentRegions.length).filter
            (targetIsChild ∘ attachment.freshRegion)) =
        [] := by
    simpa only [List.map_nil] using
      congrArg (List.map attachment.freshRegion) freshFilter
  rw [freshMapped]
  unfold ConcreteDiagram.regionsList
  simp

private theorem fragmentEndpoint_incident
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment)
    (wire : fragment.val.diagram.WireId)
    (endpoint : CEndpoint fragment.val.diagram.nodeCount)
    (incident :
      endpoint ∈ (fragment.val.diagram.wires wire).endpoints) :
    attachment.fragmentEndpoint endpoint ∈
      (attachment.diagram.wires
        (attachment.fragmentWire wire)).endpoints := by
  have generated :
      attachment.fragmentEndpoint endpoint ∈
        attachment.generatedEndpoints (attachment.fragmentWire wire) := by
    apply List.mem_filterMap.mpr
    refine
      ⟨(attachment.fragmentWire wire,
          attachment.fragmentEndpoint endpoint), ?_, by simp⟩
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨(wire, endpoint), ?_, rfl⟩
    simp [ConcreteDiagram.endpointOccurrences,
      ConcreteDiagram.wiresList, Data.Finite.mem_allFin, incident]
  by_cases boundary : wire ∈ fragment.val.boundary
  · have generatedAtTarget :
        attachment.fragmentEndpoint endpoint ∈
          attachment.generatedEndpoints
            (attachment.hostWire
              (attachment.representativeTarget wire boundary)) := by
      simpa [ConcreteSpliceAttachment.fragmentWire, boundary] using generated
    rw [show attachment.fragmentWire wire =
        attachment.hostWire
          (attachment.representativeTarget wire boundary) by
      simp [ConcreteSpliceAttachment.fragmentWire, boundary]]
    unfold ConcreteSpliceAttachment.diagram
      ConcreteSpliceAttachment.wireTable
      ConcreteSpliceAttachment.hostWire
    simp only [Fin.addCases_left]
    exact List.mem_append_right _ generatedAtTarget
  · have generatedAtFresh :
        attachment.fragmentEndpoint endpoint ∈
          attachment.generatedEndpoints
            (attachment.freshWire
              (DenseList.index attachment.fragmentInternalWires wire (by
                simp [ConcreteSpliceAttachment.fragmentInternalWires,
                  ConcreteDiagram.wiresList, Data.Finite.mem_allFin,
                  boundary]))) := by
      simpa [ConcreteSpliceAttachment.fragmentWire, boundary] using generated
    rw [show attachment.fragmentWire wire =
        attachment.freshWire
          (DenseList.index attachment.fragmentInternalWires wire (by
            simp [ConcreteSpliceAttachment.fragmentInternalWires,
              ConcreteDiagram.wiresList, Data.Finite.mem_allFin,
              boundary])) by
      simp [ConcreteSpliceAttachment.fragmentWire, boundary]]
    unfold ConcreteSpliceAttachment.diagram
      ConcreteSpliceAttachment.wireTable
      ConcreteSpliceAttachment.freshWire
    simp only [Fin.addCases_right]
    exact generatedAtFresh

private theorem hostEndpoint_incident
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment)
    (wire : base.val.WireId)
    (endpoint : CEndpoint base.val.nodeCount)
    (incident : endpoint ∈ (base.val.wires wire).endpoints) :
    attachment.hostEndpoint endpoint ∈
      (attachment.diagram.wires
        (attachment.hostWire wire)).endpoints := by
  unfold ConcreteSpliceAttachment.diagram
    ConcreteSpliceAttachment.wireTable
    ConcreteSpliceAttachment.hostWire
  simp only [Fin.addCases_left]
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨endpoint, incident, rfl⟩

private theorem compileNodes_cons_eq_singleton_bind
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : ConcreteElaboration.WireContext diagram)
    (node : diagram.NodeId)
    (nodes : List diagram.NodeId) :
    ConcreteElaboration.compileNodes? definitions diagram context
        (node :: nodes) =
      (do
        let headItems ←
          ConcreteElaboration.compileNodes? definitions diagram
            context [node]
        let tailItems ←
          ConcreteElaboration.compileNodes? definitions diagram
            context nodes
        pure (headItems.append tailItems)) := by
  rw [ConcreteElaboration.compileNodes?_equation]
  dsimp only
  rw [ConcreteElaboration.compileNodes?_equation definitions diagram context
    [node]]
  dsimp only
  rw [ConcreteElaboration.compileNodes?_equation definitions diagram context
    []]
  cases headEquation :
      ConcreteElaboration.Internal.compileNode? definitions diagram context
        node with
  | none => simp [headEquation]
  | some head =>
      cases tailEquation :
          ConcreteElaboration.compileNodes? definitions diagram context nodes with
      | none => simp [headEquation, tailEquation]
      | some tail => simp [headEquation, tailEquation, ItemSeq.append]

private theorem compileNodes_cons_split
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : ConcreteElaboration.WireContext diagram)
    (node : diagram.NodeId)
    (nodes : List diagram.NodeId)
    (items : ItemSeq definitions context.sigs)
    (compiled :
      ConcreteElaboration.compileNodes? definitions diagram context
          (node :: nodes) = some items) :
    ∃ (headItems tailItems : ItemSeq definitions context.sigs),
      ConcreteElaboration.compileNodes? definitions diagram context [node] =
          some headItems ∧
      ConcreteElaboration.compileNodes? definitions diagram context nodes =
          some tailItems ∧
      items = headItems.append tailItems := by
  rw [compileNodes_cons_eq_singleton_bind] at compiled
  obtain ⟨headItems, headCompiled, compiled⟩ :=
    Option.bind_eq_some_iff.mp compiled
  obtain ⟨tailItems, tailCompiled, compiled⟩ :=
    Option.bind_eq_some_iff.mp compiled
  have itemsEquality : headItems.append tailItems = items :=
    Option.some.inj compiled
  subst items
  exact ⟨headItems, tailItems, headCompiled, tailCompiled, rfl⟩

private theorem ItemSeq.renameWires_append
    (rho : WireRenaming source target) :
    (left right : ItemSeq definitions source) →
      (left.append right).renameWires rho =
        (left.renameWires rho).append (right.renameWires rho)
  | .nil, _ => rfl
  | .cons head tail, right =>
      congrArg (ItemSeq.cons (head.renameWires rho))
        (ItemSeq.renameWires_append rho tail right)

theorem copiedFragmentNodes_natural
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (sourceContext :
      ConcreteElaboration.WireContext fragment.val.diagram)
    (targetContext :
      ConcreteElaboration.WireContext attachment.diagram)
    (targetNodup : targetContext.ids.Nodup)
    (rho : WireRenaming sourceContext.sigs targetContext.sigs)
    (contextAction :
      ∀ {sig} (value : Var sourceContext.sigs sig),
        ConcreteElaboration.WireContext.origin attachment.diagram
            targetContext.ids (rho value) =
          attachment.fragmentWire
            (ConcreteElaboration.WireContext.origin
              fragment.val.diagram sourceContext.ids value)) :
    ∀ (nodes : List fragment.val.diagram.NodeId)
      {sourceItems : ItemSeq definitions sourceContext.sigs},
      ConcreteElaboration.compileNodes? definitions
          fragment.val.diagram sourceContext nodes = some sourceItems →
      ∃ targetItems : ItemSeq definitions targetContext.sigs,
        ConcreteElaboration.compileNodes? definitions
            attachment.diagram targetContext
            (nodes.map attachment.fragmentNode) = some targetItems ∧
        targetItems = sourceItems.renameWires rho := by
  intro nodes
  induction nodes with
  | nil =>
      intro sourceItems sourceCompiled
      have sourceEquality :
          (ItemSeq.nil : ItemSeq definitions sourceContext.sigs) =
            sourceItems :=
        Option.some.inj (by
          rw [ConcreteElaboration.compileNodes?_equation] at sourceCompiled
          exact sourceCompiled)
      subst sourceItems
      refine ⟨.nil, ?_, rfl⟩
      rw [ConcreteElaboration.compileNodes?_equation]
      rfl
  | cons node tail induction =>
      intro sourceItems sourceCompiled
      obtain ⟨headItems, tailItems, headCompiled, tailCompiled,
          sourceEquality⟩ :=
        compileNodes_cons_split definitions fragment.val.diagram
          sourceContext node tail sourceItems sourceCompiled
      obtain ⟨targetHead, targetHeadCompiled, targetHeadEquality⟩ :=
        ConcreteElaboration.compileNodes?_singleton_natural
          compiled.generated_wellFormed targetNodup rho
          attachment.fragmentWire (fragmentWire_signature attachment)
          contextAction attachment.fragmentRegion node
          (attachment.fragmentNode node)
          (by
            rw [compiled.fragment_node_source]
            unfold ConcreteSpliceAttachment.renameFragmentNode
            cases nodeData : fragment.val.diagram.nodes node <;> rfl)
          (by
            intro port wire incident
            simpa [ConcreteSpliceAttachment.fragmentEndpoint] using
              fragmentEndpoint_incident attachment wire
                (⟨node, port⟩ :
                  CEndpoint fragment.val.diagram.nodeCount) incident)
          headCompiled
      obtain ⟨targetTail, targetTailCompiled, targetTailEquality⟩ :=
        induction tailCompiled
      refine ⟨targetHead.append targetTail, ?_, ?_⟩
      · rw [List.map_cons, compileNodes_cons_eq_singleton_bind]
        simp [targetHeadCompiled, targetTailCompiled]
      · rw [sourceEquality, ItemSeq.renameWires_append,
          ← targetHeadEquality, ← targetTailEquality]

private theorem fragmentExtended_visible
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (region : fragment.val.diagram.RegionId)
    (nonroot : region ≠ fragment.val.diagram.root)
    (sourceContext :
      ConcreteElaboration.WireContext fragment.val.diagram)
    (targetContext :
      ConcreteElaboration.WireContext attachment.diagram)
    (rho : WireRenaming sourceContext.sigs targetContext.sigs)
    (contextAction :
      ∀ {sig} (value : Var sourceContext.sigs sig),
        ConcreteElaboration.WireContext.origin attachment.diagram
            targetContext.ids (rho value) =
          attachment.fragmentWire
            (ConcreteElaboration.WireContext.origin
              fragment.val.diagram sourceContext.ids value))
    (wire : fragment.val.diagram.WireId)
    (member : wire ∈ (sourceContext.extend region).ids) :
    attachment.fragmentWire wire ∈
      (targetContext.extend (attachment.fragmentRegion region)).ids := by
  change
    wire ∈ fragment.val.diagram.wiresAt region ++ sourceContext.ids
      at member
  change
    attachment.fragmentWire wire ∈
      attachment.diagram.wiresAt (attachment.fragmentRegion region) ++
        targetContext.ids
  rcases List.mem_append.mp member with localMember | outer
  · apply List.mem_append_left
    rw [compiled.fragment_wires region nonroot]
    exact List.mem_map.mpr ⟨wire, localMember, rfl⟩
  · let sourceValue :=
      varForMember fragment.val.diagram sourceContext.ids wire outer
    have targetMember :=
      origin_member attachment.diagram targetContext.ids (rho sourceValue)
    have origin :=
      contextAction sourceValue
    rw [varForMember_origin] at origin
    apply List.mem_append_right
    exact origin ▸ targetMember

def fragmentExtendedRenaming
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (region : fragment.val.diagram.RegionId)
    (nonroot : region ≠ fragment.val.diagram.root)
    (sourceContext :
      ConcreteElaboration.WireContext fragment.val.diagram)
    (targetContext :
      ConcreteElaboration.WireContext attachment.diagram)
    (rho : WireRenaming sourceContext.sigs targetContext.sigs)
    (contextAction :
      ∀ {sig} (value : Var sourceContext.sigs sig),
        ConcreteElaboration.WireContext.origin attachment.diagram
            targetContext.ids (rho value) =
          attachment.fragmentWire
            (ConcreteElaboration.WireContext.origin
              fragment.val.diagram sourceContext.ids value)) :
    WireRenaming (sourceContext.extend region).sigs
      (targetContext.extend (attachment.fragmentRegion region)).sigs :=
  contextEmbedding fragment.val.diagram attachment.diagram
    (sourceContext.extend region).ids
    (targetContext.extend (attachment.fragmentRegion region)).ids
    attachment.fragmentWire (fragmentWire_signature attachment)
    (fragmentExtended_visible compiled region nonroot sourceContext
      targetContext rho contextAction)

theorem fragmentExtendedRenaming_contextAction
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (region : fragment.val.diagram.RegionId)
    (nonroot : region ≠ fragment.val.diagram.root)
    (sourceContext :
      ConcreteElaboration.WireContext fragment.val.diagram)
    (targetContext :
      ConcreteElaboration.WireContext attachment.diagram)
    (rho : WireRenaming sourceContext.sigs targetContext.sigs)
    (contextAction :
      ∀ {sig} (value : Var sourceContext.sigs sig),
        ConcreteElaboration.WireContext.origin attachment.diagram
            targetContext.ids (rho value) =
          attachment.fragmentWire
            (ConcreteElaboration.WireContext.origin
              fragment.val.diagram sourceContext.ids value))
    {sig : Sig}
    (value : Var (sourceContext.extend region).sigs sig) :
    ConcreteElaboration.WireContext.origin attachment.diagram
        (targetContext.extend
          (attachment.fragmentRegion region)).ids
        (fragmentExtendedRenaming compiled region nonroot sourceContext
          targetContext rho contextAction value) =
      attachment.fragmentWire
        (ConcreteElaboration.WireContext.origin fragment.val.diagram
          (sourceContext.extend region).ids value) :=
  contextEmbedding_origin fragment.val.diagram attachment.diagram
    (sourceContext.extend region).ids
    (targetContext.extend (attachment.fragmentRegion region)).ids
    attachment.fragmentWire (fragmentWire_signature attachment)
    (fragmentExtended_visible compiled region nonroot sourceContext
      targetContext rho contextAction)
    value

theorem fragmentRegionLocalSigs_eq
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (region : fragment.val.diagram.RegionId)
    (nonroot : region ≠ fragment.val.diagram.root) :
    (attachment.diagram.wiresAt
        (attachment.fragmentRegion region)).map
          (fun wire => (attachment.diagram.wires wire).sig) =
      (fragment.val.diagram.wiresAt region).map
        (fun wire => (fragment.val.diagram.wires wire).sig) := by
  rw [compiled.fragment_wires region nonroot]
  calc
    _ = List.map
          (fun wire =>
            (attachment.diagram.wires
              (attachment.fragmentWire wire)).sig)
          (fragment.val.diagram.wiresAt region) := by
        exact
          @List.map_map attachment.diagram.WireId Sig
            fragment.val.diagram.WireId
            (fun wire => (attachment.diagram.wires wire).sig)
            attachment.fragmentWire
            (fragment.val.diagram.wiresAt region)
    _ = _ := by
      apply List.map_congr_left
      intro wire _
      exact fragmentWire_signature attachment wire

theorem copiedHostNodes_natural
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (sourceContext : ConcreteElaboration.WireContext base.val)
    (targetContext :
      ConcreteElaboration.WireContext attachment.diagram)
    (targetNodup : targetContext.ids.Nodup)
    (rho : WireRenaming sourceContext.sigs targetContext.sigs)
    (contextAction :
      ∀ {sig} (value : Var sourceContext.sigs sig),
        ConcreteElaboration.WireContext.origin attachment.diagram
            targetContext.ids (rho value) =
          attachment.hostWire
            (ConcreteElaboration.WireContext.origin
              base.val sourceContext.ids value)) :
    ∀ (nodes : List base.val.NodeId)
      {sourceItems : ItemSeq definitions sourceContext.sigs},
      ConcreteElaboration.compileNodes? definitions
          base.val sourceContext nodes = some sourceItems →
      ∃ targetItems : ItemSeq definitions targetContext.sigs,
        ConcreteElaboration.compileNodes? definitions
            attachment.diagram targetContext
            (nodes.map attachment.hostNode) = some targetItems ∧
        targetItems = sourceItems.renameWires rho := by
  intro nodes
  induction nodes with
  | nil =>
      intro sourceItems sourceCompiled
      have sourceEquality :
          (ItemSeq.nil : ItemSeq definitions sourceContext.sigs) =
            sourceItems :=
        Option.some.inj (by
          rw [ConcreteElaboration.compileNodes?_equation] at sourceCompiled
          exact sourceCompiled)
      subst sourceItems
      refine ⟨.nil, ?_, rfl⟩
      rw [ConcreteElaboration.compileNodes?_equation]
      rfl
  | cons node tail induction =>
      intro sourceItems sourceCompiled
      obtain ⟨headItems, tailItems, headCompiled, tailCompiled,
          sourceEquality⟩ :=
        compileNodes_cons_split definitions base.val sourceContext
          node tail sourceItems sourceCompiled
      obtain ⟨targetHead, targetHeadCompiled, targetHeadEquality⟩ :=
        ConcreteElaboration.compileNodes?_singleton_natural
          compiled.generated_wellFormed targetNodup rho
          attachment.hostWire attachment.diagram_wire_hostWire
          contextAction attachment.hostRegion node
          (attachment.hostNode node)
          (by
            rw [compiled.host_node_source]
            unfold ConcreteSpliceAttachment.renameHostNode
            cases nodeData : base.val.nodes node <;> rfl)
          (by
            intro port wire incident
            simpa [ConcreteSpliceAttachment.hostEndpoint] using
              hostEndpoint_incident attachment wire
                (⟨node, port⟩ : CEndpoint base.val.nodeCount) incident)
          headCompiled
      obtain ⟨targetTail, targetTailCompiled, targetTailEquality⟩ :=
        induction tailCompiled
      refine ⟨targetHead.append targetTail, ?_, ?_⟩
      · rw [List.map_cons, compileNodes_cons_eq_singleton_bind]
        simp [targetHeadCompiled, targetTailCompiled]
      · rw [sourceEquality, ItemSeq.renameWires_append,
          ← targetHeadEquality, ← targetTailEquality]

private theorem hostExtended_visible
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (region : base.val.RegionId)
    (notSite : region ≠ site)
    (sourceContext : ConcreteElaboration.WireContext base.val)
    (targetContext :
      ConcreteElaboration.WireContext attachment.diagram)
    (rho : WireRenaming sourceContext.sigs targetContext.sigs)
    (contextAction :
      ∀ {sig} (value : Var sourceContext.sigs sig),
        ConcreteElaboration.WireContext.origin attachment.diagram
            targetContext.ids (rho value) =
          attachment.hostWire
            (ConcreteElaboration.WireContext.origin
              base.val sourceContext.ids value))
    (wire : base.val.WireId)
    (member : wire ∈ (sourceContext.extend region).ids) :
    attachment.hostWire wire ∈
      (targetContext.extend (attachment.hostRegion region)).ids := by
  change wire ∈ base.val.wiresAt region ++ sourceContext.ids at member
  change
    attachment.hostWire wire ∈
      attachment.diagram.wiresAt (attachment.hostRegion region) ++
        targetContext.ids
  rcases List.mem_append.mp member with localMember | outer
  · apply List.mem_append_left
    rw [hostWires_offsite compiled region notSite]
    exact List.mem_map.mpr ⟨wire, localMember, rfl⟩
  · let sourceValue :=
      varForMember base.val sourceContext.ids wire outer
    have targetMember :=
      origin_member attachment.diagram targetContext.ids (rho sourceValue)
    have origin := contextAction sourceValue
    rw [varForMember_origin] at origin
    apply List.mem_append_right
    exact origin ▸ targetMember

def hostExtendedRenaming
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (region : base.val.RegionId)
    (notSite : region ≠ site)
    (sourceContext : ConcreteElaboration.WireContext base.val)
    (targetContext :
      ConcreteElaboration.WireContext attachment.diagram)
    (rho : WireRenaming sourceContext.sigs targetContext.sigs)
    (contextAction :
      ∀ {sig} (value : Var sourceContext.sigs sig),
        ConcreteElaboration.WireContext.origin attachment.diagram
            targetContext.ids (rho value) =
          attachment.hostWire
            (ConcreteElaboration.WireContext.origin
              base.val sourceContext.ids value)) :
    WireRenaming (sourceContext.extend region).sigs
      (targetContext.extend (attachment.hostRegion region)).sigs :=
  contextEmbedding base.val attachment.diagram
    (sourceContext.extend region).ids
    (targetContext.extend (attachment.hostRegion region)).ids
    attachment.hostWire attachment.diagram_wire_hostWire
    (hostExtended_visible compiled region notSite sourceContext
      targetContext rho contextAction)

theorem hostExtendedRenaming_contextAction
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (region : base.val.RegionId)
    (notSite : region ≠ site)
    (sourceContext : ConcreteElaboration.WireContext base.val)
    (targetContext :
      ConcreteElaboration.WireContext attachment.diagram)
    (rho : WireRenaming sourceContext.sigs targetContext.sigs)
    (contextAction :
      ∀ {sig} (value : Var sourceContext.sigs sig),
        ConcreteElaboration.WireContext.origin attachment.diagram
            targetContext.ids (rho value) =
          attachment.hostWire
            (ConcreteElaboration.WireContext.origin
              base.val sourceContext.ids value))
    {sig : Sig}
    (value : Var (sourceContext.extend region).sigs sig) :
    ConcreteElaboration.WireContext.origin attachment.diagram
        (targetContext.extend (attachment.hostRegion region)).ids
        (hostExtendedRenaming compiled region notSite sourceContext
          targetContext rho contextAction value) =
      attachment.hostWire
        (ConcreteElaboration.WireContext.origin base.val
          (sourceContext.extend region).ids value) :=
  contextEmbedding_origin base.val attachment.diagram
    (sourceContext.extend region).ids
    (targetContext.extend (attachment.hostRegion region)).ids
    attachment.hostWire attachment.diagram_wire_hostWire
    (hostExtended_visible compiled region notSite sourceContext
      targetContext rho contextAction)
    value

theorem hostRegionLocalSigs_eq
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (region : base.val.RegionId)
    (notSite : region ≠ site) :
    (attachment.diagram.wiresAt
        (attachment.hostRegion region)).map
          (fun wire => (attachment.diagram.wires wire).sig) =
      (base.val.wiresAt region).map
        (fun wire => (base.val.wires wire).sig) := by
  rw [hostWires_offsite compiled region notSite]
  calc
    _ = List.map
          (fun wire =>
            (attachment.diagram.wires
              (attachment.hostWire wire)).sig)
          (base.val.wiresAt region) := by
        exact
          @List.map_map attachment.diagram.WireId Sig
            base.val.WireId
            (fun wire => (attachment.diagram.wires wire).sig)
            attachment.hostWire
            (base.val.wiresAt region)
    _ = _ := by
      apply List.map_congr_left
      intro wire _
      exact attachment.diagram_wire_hostWire wire

private theorem hostRegionLocal_origin
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (region : base.val.RegionId)
    (notSite : region ≠ site)
    (value :
      PackedVar
        ((base.val.wiresAt region).map
          (fun wire => (base.val.wires wire).sig))) :
    packedOrigin attachment.diagram
        (attachment.diagram.wiresAt (attachment.hostRegion region))
        (castPacked
          (hostRegionLocalSigs_eq compiled region notSite).symm
          value) =
      attachment.hostWire
        (packedOrigin base.val (base.val.wiresAt region) value) := by
  let mapped :=
    castPacked
      (hostRegionLocalSigs_eq compiled region notSite).symm value
  have mappedOffset :
      packedOffset mapped = packedOffset value :=
    packedOffset_castPacked
      (hostRegionLocalSigs_eq compiled region notSite).symm value
  have targetLookup :=
    packedOrigin_get? attachment.diagram
      (attachment.diagram.wiresAt (attachment.hostRegion region)) mapped
  have sourceLookup :=
    packedOrigin_get? base.val (base.val.wiresAt region) value
  have allocation :=
    congrArg
      (fun ids => ids[packedOffset value]?)
      (hostWires_offsite compiled region notSite)
  have mapLookup :
      ((base.val.wiresAt region).map attachment.hostWire)[
          packedOffset value]? =
        (base.val.wiresAt region)[packedOffset value]?.map
          attachment.hostWire := by
    simp
  have lookupIndex :=
    congrArg
      (fun offset =>
        (attachment.diagram.wiresAt
          (attachment.hostRegion region))[offset]?)
      mappedOffset
  have targetAtValue :
      (attachment.diagram.wiresAt
        (attachment.hostRegion region))[packedOffset value]? =
          some
            (packedOrigin attachment.diagram
              (attachment.diagram.wiresAt
                (attachment.hostRegion region)) mapped) :=
    lookupIndex.symm.trans targetLookup
  have mappedSource :=
    congrArg (Option.map attachment.hostWire) sourceLookup
  exact Option.some.inj
    (targetAtValue.symm.trans
      (allocation.trans (mapLookup.trans mappedSource)))

theorem hostExtendedRenaming_extendEnvironment
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (region : base.val.RegionId)
    (notSite : region ≠ site)
    (sourceContext : ConcreteElaboration.WireContext base.val)
    (targetContext :
      ConcreteElaboration.WireContext attachment.diagram)
    (targetExtendedNodup :
      (targetContext.extend (attachment.hostRegion region)).ids.Nodup)
    (rho : WireRenaming sourceContext.sigs targetContext.sigs)
    (contextAction :
      ∀ {sig} (value : Var sourceContext.sigs sig),
        ConcreteElaboration.WireContext.origin attachment.diagram
            targetContext.ids (rho value) =
          attachment.hostWire
            (ConcreteElaboration.WireContext.origin
              base.val sourceContext.ids value))
    (pre : PreModel)
    (sourceValues :
      ConcreteElaboration.WireValues pre
        ((base.val.wiresAt region).map
          fun wire => (base.val.wires wire).sig))
    (targetEnv : Env pre targetContext.sigs) :
    Env.comp
        (ConcreteElaboration.extendEnvironment attachment.diagram
          targetContext (attachment.hostRegion region)
          ((hostRegionLocalSigs_eq compiled region notSite).symm ▸
            sourceValues)
          targetEnv)
        (hostExtendedRenaming compiled region notSite sourceContext
          targetContext rho contextAction) =
      ConcreteElaboration.extendEnvironment base.val
        sourceContext region sourceValues (Env.comp targetEnv rho) := by
  funext sig value
  rcases
      var_append_cases base.val
        (base.val.wiresAt region) sourceContext.ids value with
    ⟨localValue, same⟩ | ⟨outerValue, same⟩
  · subst value
    have mappedLocal :
        hostExtendedRenaming compiled region notSite sourceContext
            targetContext rho contextAction
            (appendLeftIds base.val sourceContext.ids localValue) =
          appendLeftIds attachment.diagram targetContext.ids
            ((hostRegionLocalSigs_eq compiled region notSite).symm ▸
              localValue) := by
      apply origin_injective attachment.diagram
        (targetContext.extend (attachment.hostRegion region)).ids
        targetExtendedNodup
      rw [hostExtendedRenaming_contextAction]
      change
        attachment.hostWire
            (ConcreteElaboration.WireContext.origin base.val
              (base.val.wiresAt region ++ sourceContext.ids)
              (appendLeftIds base.val sourceContext.ids localValue)) =
          ConcreteElaboration.WireContext.origin attachment.diagram
            (attachment.diagram.wiresAt
                (attachment.hostRegion region) ++ targetContext.ids)
            (appendLeftIds attachment.diagram targetContext.ids
              ((hostRegionLocalSigs_eq compiled region notSite).symm ▸
                localValue))
      rw [appendLeftIds_origin, appendLeftIds_origin]
      change
        attachment.hostWire
            (packedOrigin base.val (base.val.wiresAt region)
              (⟨sig, localValue⟩ : PackedVar
                ((base.val.wiresAt region).map
                  fun wire => (base.val.wires wire).sig))) =
          packedOrigin attachment.diagram
            (attachment.diagram.wiresAt (attachment.hostRegion region))
            (castPacked
              (hostRegionLocalSigs_eq compiled region notSite).symm
              (⟨sig, localValue⟩ : PackedVar
                ((base.val.wiresAt region).map
                  fun wire => (base.val.wires wire).sig)))
      exact
        (hostRegionLocal_origin compiled region notSite
          (⟨sig, localValue⟩ : PackedVar
            ((base.val.wiresAt region).map
              fun wire => (base.val.wires wire).sig))).symm
    let targetValues :=
      (hostRegionLocalSigs_eq compiled region notSite).symm ▸
        sourceValues
    change
      ConcreteElaboration.extendEnvironment attachment.diagram
          targetContext (attachment.hostRegion region)
          targetValues targetEnv sig
          (hostExtendedRenaming compiled region notSite sourceContext
            targetContext rho contextAction
            (appendLeftIds base.val sourceContext.ids localValue)) =
        ConcreteElaboration.extendEnvironment base.val
          sourceContext region sourceValues (Env.comp targetEnv rho) sig
          (appendLeftIds base.val sourceContext.ids localValue)
    rw [mappedLocal]
    calc
      _ = wireValue targetValues
            ((hostRegionLocalSigs_eq compiled region notSite).symm ▸
              localValue) :=
        extendEnvironment_local attachment.diagram targetContext
          (attachment.hostRegion region) pre targetValues targetEnv _
      _ = wireValue sourceValues localValue := by
        unfold targetValues
        exact
          wireValue_cast
            (hostRegionLocalSigs_eq compiled region notSite).symm
            sourceValues localValue
      _ = _ :=
        (extendEnvironment_local base.val sourceContext region
          pre sourceValues (Env.comp targetEnv rho) localValue).symm
  · subst value
    have mappedOuter :
        hostExtendedRenaming compiled region notSite sourceContext
            targetContext rho contextAction
            (ConcreteElaboration.appendRightVar base.val
              (base.val.wiresAt region) outerValue) =
          ConcreteElaboration.appendRightVar attachment.diagram
            (attachment.diagram.wiresAt (attachment.hostRegion region))
            (rho outerValue) := by
      apply origin_injective attachment.diagram
        (targetContext.extend (attachment.hostRegion region)).ids
        targetExtendedNodup
      rw [hostExtendedRenaming_contextAction]
      change
        attachment.hostWire
            (ConcreteElaboration.WireContext.origin base.val
              (base.val.wiresAt region ++ sourceContext.ids)
              (ConcreteElaboration.appendRightVar base.val
                (base.val.wiresAt region) outerValue)) =
          ConcreteElaboration.WireContext.origin attachment.diagram
            (attachment.diagram.wiresAt
                (attachment.hostRegion region) ++ targetContext.ids)
            (ConcreteElaboration.appendRightVar attachment.diagram
              (attachment.diagram.wiresAt
                (attachment.hostRegion region))
              (rho outerValue))
      rw [ConcreteElaboration.origin_appendRightVar,
        ConcreteElaboration.origin_appendRightVar, contextAction]
    change
      ConcreteElaboration.extendEnvironment attachment.diagram
          targetContext (attachment.hostRegion region)
          ((hostRegionLocalSigs_eq compiled region notSite).symm ▸
            sourceValues)
          targetEnv sig
          (hostExtendedRenaming compiled region notSite sourceContext
            targetContext rho contextAction
            (ConcreteElaboration.appendRightVar base.val
              (base.val.wiresAt region) outerValue)) =
        ConcreteElaboration.extendEnvironment base.val
          sourceContext region sourceValues (Env.comp targetEnv rho) sig
          (ConcreteElaboration.appendRightVar base.val
            (base.val.wiresAt region) outerValue)
    rw [mappedOuter]
    calc
      _ = targetEnv sig (rho outerValue) :=
        extendEnvironment_outer attachment.diagram targetContext
          (attachment.hostRegion region) pre
          ((hostRegionLocalSigs_eq compiled region notSite).symm ▸
            sourceValues)
          targetEnv (rho outerValue)
      _ = Env.comp targetEnv rho sig outerValue := rfl
      _ = _ :=
        (extendEnvironment_outer base.val sourceContext region
          pre sourceValues (Env.comp targetEnv rho) outerValue).symm

theorem hostContext_extend_offsite
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (sourceContext : ConcreteElaboration.WireContext base.val)
    (region : base.val.RegionId)
    (notSite : region ≠ site) :
    hostContext attachment (sourceContext.extend region) =
      (hostContext attachment sourceContext).extend
        (attachment.hostRegion region) := by
  apply congrArg ConcreteElaboration.WireContext.mk
  unfold hostContext ConcreteElaboration.WireContext.extend
  rw [List.map_append, hostWires_offsite compiled region notSite]
  rfl

def hostContextRenamingThrough
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment)
    (sourceContext : ConcreteElaboration.WireContext base.val)
    (targetContext :
      ConcreteElaboration.WireContext attachment.diagram)
    (same : hostContext attachment sourceContext = targetContext) :
    WireRenaming sourceContext.sigs targetContext.sigs :=
  congrArg ConcreteElaboration.WireContext.sigs same ▸
    hostContextRenaming attachment sourceContext

private theorem hostContextRenamingThrough_origin
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment)
    (sourceContext : ConcreteElaboration.WireContext base.val)
    (targetContext :
      ConcreteElaboration.WireContext attachment.diagram)
    (same : hostContext attachment sourceContext = targetContext)
    {sig : Sig} (value : Var sourceContext.sigs sig) :
    ConcreteElaboration.WireContext.origin attachment.diagram
        targetContext.ids
        (hostContextRenamingThrough attachment sourceContext
          targetContext same value) =
      attachment.hostWire
        (ConcreteElaboration.WireContext.origin base.val
          sourceContext.ids value) := by
  cases same
  exact hostContextRenaming_origin attachment sourceContext value

theorem hostContextRenamingThrough_self
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment)
    (sourceContext : ConcreteElaboration.WireContext base.val) :
    (fun {sig} value =>
      hostContextRenamingThrough attachment sourceContext
        (hostContext attachment sourceContext) rfl
        (sig := sig) value) =
      (fun {sig} value =>
        hostContextRenaming attachment sourceContext
          (sig := sig) value) :=
  rfl

theorem hostContextRenamingThrough_extend
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (sourceContext : ConcreteElaboration.WireContext base.val)
    (region : base.val.RegionId)
    (notSite : region ≠ site)
    (targetNodup :
      ((hostContext attachment sourceContext).extend
        (attachment.hostRegion region)).ids.Nodup) :
    (fun {sig} value =>
      hostContextRenamingThrough attachment
        (sourceContext.extend region)
        ((hostContext attachment sourceContext).extend
          (attachment.hostRegion region))
        (hostContext_extend_offsite compiled sourceContext region
          notSite) (sig := sig) value) =
      (fun {sig} value =>
        hostExtendedRenaming compiled region notSite sourceContext
          (hostContext attachment sourceContext)
          (hostContextRenaming attachment sourceContext)
          (hostContextRenaming_origin attachment sourceContext)
          (sig := sig) value) := by
  funext sig value
  apply origin_injective attachment.diagram
    ((hostContext attachment sourceContext).extend
      (attachment.hostRegion region)).ids targetNodup
  rw [hostContextRenamingThrough_origin,
    hostExtendedRenaming_contextAction]

private theorem fragmentRegionLocal_origin
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (region : fragment.val.diagram.RegionId)
    (nonroot : region ≠ fragment.val.diagram.root)
    (value :
      PackedVar
        ((fragment.val.diagram.wiresAt region).map
          (fun wire => (fragment.val.diagram.wires wire).sig))) :
    packedOrigin attachment.diagram
        (attachment.diagram.wiresAt
          (attachment.fragmentRegion region))
        (castPacked
          (fragmentRegionLocalSigs_eq compiled region nonroot).symm
          value) =
      attachment.fragmentWire
        (packedOrigin fragment.val.diagram
          (fragment.val.diagram.wiresAt region) value) := by
  let mapped :=
    castPacked
      (fragmentRegionLocalSigs_eq compiled region nonroot).symm
      value
  have mappedOffset :
      packedOffset mapped = packedOffset value :=
    packedOffset_castPacked
      (fragmentRegionLocalSigs_eq compiled region nonroot).symm value
  have targetLookup :=
    packedOrigin_get? attachment.diagram
      (attachment.diagram.wiresAt
        (attachment.fragmentRegion region)) mapped
  have sourceLookup :=
    packedOrigin_get? fragment.val.diagram
      (fragment.val.diagram.wiresAt region) value
  have allocation :=
    congrArg
      (fun ids => ids[packedOffset value]?)
      (compiled.fragment_wires region nonroot)
  have mapLookup :
      ((fragment.val.diagram.wiresAt region).map
          attachment.fragmentWire)[packedOffset value]? =
        (fragment.val.diagram.wiresAt region)[
          packedOffset value]?.map attachment.fragmentWire := by
    simp
  have lookupIndex :=
    congrArg
      (fun offset =>
        (attachment.diagram.wiresAt
          (attachment.fragmentRegion region))[offset]?)
      mappedOffset
  have targetAtValue :
      (attachment.diagram.wiresAt
        (attachment.fragmentRegion region))[packedOffset value]? =
          some
            (packedOrigin attachment.diagram
              (attachment.diagram.wiresAt
                (attachment.fragmentRegion region)) mapped) :=
    lookupIndex.symm.trans targetLookup
  have mappedSource :=
    congrArg (Option.map attachment.fragmentWire) sourceLookup
  exact Option.some.inj
    (targetAtValue.symm.trans
      (allocation.trans (mapLookup.trans mappedSource)))

theorem fragmentExtendedRenaming_extendEnvironment
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment)
    (region : fragment.val.diagram.RegionId)
    (nonroot : region ≠ fragment.val.diagram.root)
    (sourceContext :
      ConcreteElaboration.WireContext fragment.val.diagram)
    (targetContext :
      ConcreteElaboration.WireContext attachment.diagram)
    (targetExtendedNodup :
      (targetContext.extend
        (attachment.fragmentRegion region)).ids.Nodup)
    (rho : WireRenaming sourceContext.sigs targetContext.sigs)
    (contextAction :
      ∀ {sig} (value : Var sourceContext.sigs sig),
        ConcreteElaboration.WireContext.origin attachment.diagram
            targetContext.ids (rho value) =
          attachment.fragmentWire
            (ConcreteElaboration.WireContext.origin
              fragment.val.diagram sourceContext.ids value))
    (pre : PreModel)
    (sourceValues :
      ConcreteElaboration.WireValues pre
        ((fragment.val.diagram.wiresAt region).map
          fun wire => (fragment.val.diagram.wires wire).sig))
    (targetEnv : Env pre targetContext.sigs) :
    Env.comp
        (ConcreteElaboration.extendEnvironment attachment.diagram
          targetContext (attachment.fragmentRegion region)
          ((fragmentRegionLocalSigs_eq compiled region nonroot).symm ▸
            sourceValues)
          targetEnv)
        (fragmentExtendedRenaming compiled region nonroot sourceContext
          targetContext rho contextAction) =
      ConcreteElaboration.extendEnvironment fragment.val.diagram
        sourceContext region sourceValues (Env.comp targetEnv rho) := by
  funext sig value
  rcases
      var_append_cases fragment.val.diagram
        (fragment.val.diagram.wiresAt region) sourceContext.ids value with
    ⟨localValue, same⟩ | ⟨outerValue, same⟩
  · subst value
    have mappedLocal :
        fragmentExtendedRenaming compiled region nonroot sourceContext
            targetContext rho contextAction
            (appendLeftIds fragment.val.diagram sourceContext.ids
              localValue) =
          appendLeftIds attachment.diagram targetContext.ids
            ((fragmentRegionLocalSigs_eq compiled region nonroot).symm ▸
              localValue) := by
      apply origin_injective attachment.diagram
        (targetContext.extend
          (attachment.fragmentRegion region)).ids
        targetExtendedNodup
      rw [fragmentExtendedRenaming_contextAction]
      change
        attachment.fragmentWire
            (ConcreteElaboration.WireContext.origin fragment.val.diagram
              (fragment.val.diagram.wiresAt region ++ sourceContext.ids)
              (appendLeftIds fragment.val.diagram sourceContext.ids
                localValue)) =
          ConcreteElaboration.WireContext.origin attachment.diagram
            (attachment.diagram.wiresAt
                (attachment.fragmentRegion region) ++ targetContext.ids)
            (appendLeftIds attachment.diagram targetContext.ids
              ((fragmentRegionLocalSigs_eq compiled region nonroot).symm ▸
                localValue))
      rw [appendLeftIds_origin, appendLeftIds_origin]
      change
        attachment.fragmentWire
            (packedOrigin fragment.val.diagram
              (fragment.val.diagram.wiresAt region)
              (⟨sig, localValue⟩ : PackedVar
                ((fragment.val.diagram.wiresAt region).map
                  fun wire => (fragment.val.diagram.wires wire).sig))) =
          packedOrigin attachment.diagram
            (attachment.diagram.wiresAt
              (attachment.fragmentRegion region))
            (castPacked
              (fragmentRegionLocalSigs_eq compiled region nonroot).symm
              (⟨sig, localValue⟩ : PackedVar
                ((fragment.val.diagram.wiresAt region).map
                  fun wire => (fragment.val.diagram.wires wire).sig)))
      exact
        (fragmentRegionLocal_origin compiled region nonroot
          (⟨sig, localValue⟩ : PackedVar
            ((fragment.val.diagram.wiresAt region).map
              fun wire => (fragment.val.diagram.wires wire).sig))).symm
    let targetValues :=
      (fragmentRegionLocalSigs_eq compiled region nonroot).symm ▸
        sourceValues
    change
      ConcreteElaboration.extendEnvironment attachment.diagram
          targetContext (attachment.fragmentRegion region)
          targetValues targetEnv sig
          (fragmentExtendedRenaming compiled region nonroot sourceContext
            targetContext rho contextAction
            (appendLeftIds fragment.val.diagram sourceContext.ids
              localValue)) =
        ConcreteElaboration.extendEnvironment fragment.val.diagram
          sourceContext region sourceValues (Env.comp targetEnv rho) sig
          (appendLeftIds fragment.val.diagram sourceContext.ids localValue)
    rw [mappedLocal]
    calc
      _ = wireValue targetValues
            ((fragmentRegionLocalSigs_eq compiled region nonroot).symm ▸
              localValue) :=
        extendEnvironment_local attachment.diagram targetContext
          (attachment.fragmentRegion region) pre targetValues targetEnv _
      _ = wireValue sourceValues localValue := by
        unfold targetValues
        exact
          wireValue_cast
            (fragmentRegionLocalSigs_eq compiled region nonroot).symm
            sourceValues localValue
      _ = _ :=
        (extendEnvironment_local fragment.val.diagram sourceContext region
          pre sourceValues (Env.comp targetEnv rho) localValue).symm
  · subst value
    have mappedOuter :
        fragmentExtendedRenaming compiled region nonroot sourceContext
            targetContext rho contextAction
            (ConcreteElaboration.appendRightVar fragment.val.diagram
              (fragment.val.diagram.wiresAt region) outerValue) =
          ConcreteElaboration.appendRightVar attachment.diagram
            (attachment.diagram.wiresAt
              (attachment.fragmentRegion region))
            (rho outerValue) := by
      apply origin_injective attachment.diagram
        (targetContext.extend
          (attachment.fragmentRegion region)).ids
        targetExtendedNodup
      rw [fragmentExtendedRenaming_contextAction]
      change
        attachment.fragmentWire
            (ConcreteElaboration.WireContext.origin fragment.val.diagram
              (fragment.val.diagram.wiresAt region ++ sourceContext.ids)
              (ConcreteElaboration.appendRightVar fragment.val.diagram
                (fragment.val.diagram.wiresAt region) outerValue)) =
          ConcreteElaboration.WireContext.origin attachment.diagram
            (attachment.diagram.wiresAt
                (attachment.fragmentRegion region) ++ targetContext.ids)
            (ConcreteElaboration.appendRightVar attachment.diagram
              (attachment.diagram.wiresAt
                (attachment.fragmentRegion region))
              (rho outerValue))
      rw [ConcreteElaboration.origin_appendRightVar,
        ConcreteElaboration.origin_appendRightVar,
        contextAction]
    change
      ConcreteElaboration.extendEnvironment attachment.diagram
          targetContext (attachment.fragmentRegion region)
          ((fragmentRegionLocalSigs_eq compiled region nonroot).symm ▸
            sourceValues)
          targetEnv sig
          (fragmentExtendedRenaming compiled region nonroot sourceContext
            targetContext rho contextAction
            (ConcreteElaboration.appendRightVar fragment.val.diagram
              (fragment.val.diagram.wiresAt region) outerValue)) =
        ConcreteElaboration.extendEnvironment fragment.val.diagram
          sourceContext region sourceValues (Env.comp targetEnv rho) sig
          (ConcreteElaboration.appendRightVar fragment.val.diagram
            (fragment.val.diagram.wiresAt region) outerValue)
    rw [mappedOuter]
    calc
      _ = targetEnv sig (rho outerValue) :=
        extendEnvironment_outer attachment.diagram targetContext
          (attachment.fragmentRegion region) pre
          ((fragmentRegionLocalSigs_eq compiled region nonroot).symm ▸
            sourceValues)
          targetEnv (rho outerValue)
      _ = Env.comp targetEnv rho sig outerValue := rfl
      _ = _ :=
        (extendEnvironment_outer fragment.val.diagram sourceContext region
          pre sourceValues (Env.comp targetEnv rho) outerValue).symm


end NaturalityInternal
end InsertionCompilation
end VisualProof
