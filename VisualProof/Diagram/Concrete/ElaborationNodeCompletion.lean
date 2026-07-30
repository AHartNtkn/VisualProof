import VisualProof.Diagram.Concrete.ElaborationDenotation
namespace VisualProof
universe u

namespace ConcreteElaboration

open Internal
namespace WireContext

def Covers (context : WireContext diagram)
    (region : diagram.RegionId) : Prop :=
  ∀ wire, diagram.Encloses (diagram.wires wire).scope region →
    wire ∈ context.ids

private theorem member_wiresAt (diagram : ConcreteDiagram definitionCount)
    (region : diagram.RegionId) (wire : diagram.WireId)
    (scope : (diagram.wires wire).scope = region) :
    wire ∈ diagram.wiresAt region := by
  have member : wire ∈ diagram.wiresList := by
    exact Data.Finite.mem_allFin wire
  simp [ConcreteDiagram.wiresAt, scope, member]

theorem extend_covers_root
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions) :
    ((WireContext.empty diagram).extend diagram.root).Covers diagram.root := by
  intro wire encloses
  have scope := root_has_no_strict_ancestor definitions diagram wellFormed
    (diagram.wires wire).scope encloses
  simp [WireContext.extend,
    member_wiresAt diagram diagram.root wire scope]

theorem extend_covers_child
    (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram)
    (parent child : diagram.RegionId)
    (parentCoverage : context.Covers parent)
    (childData : diagram.regions child = .cut parent) :
    (context.extend child).Covers child := by
  intro wire encloses
  rcases encloses_child_split diagram (diagram.wires wire).scope child parent
    childData encloses with localScope | inherited
  · simp [WireContext.extend,
      member_wiresAt diagram child wire localScope]
  · simp [WireContext.extend, parentCoverage wire inherited]

end WireContext

private theorem resolvePort?_complete
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (context : WireContext diagram) (region : diagram.RegionId)
    (coverage : context.Covers region)
    (node : diagram.NodeId) (nodeRegion : (diagram.nodes node).region = region)
    (port : CPort) (expected : Sig)
    (required : port ∈ diagram.requiredPorts node)
    (typed : ∀ wire, diagram.endpointOwner? ⟨node, port⟩ = some wire →
      (diagram.wires wire).sig = expected) :
    ∃ resolved,
      resolvePort? diagram context node port expected = some resolved := by
  obtain ⟨wire, owner⟩ :=
    endpointOwner?_complete definitions diagram wellFormed node port required
  have inScope := endpoint_scope definitions diagram wellFormed
    ⟨node, port⟩ wire owner
  rw [nodeRegion] at inScope
  have member := coverage wire inScope
  obtain ⟨wireVar, wireResolved⟩ :=
    resolveWire?_complete diagram context wire member
  have signature := typed wire owner
  exact ⟨signature ▸ wireVar, by
    simp [resolvePort?, owner, resolveExpected?, signature, wireResolved]⟩

private theorem atom_head_typed
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (node : diagram.NodeId) (region : diagram.RegionId) (args : List Sig)
    (nodeData : diagram.nodes node = .atom region args)
    (wire : diagram.WireId)
    (owner : diagram.endpointOwner? ⟨node, .head⟩ = some wire) :
    (diagram.wires wire).sig = .rel args := by
  have checked := wellFormed.atom_ports_typed
  unfold ConcreteDiagram.AtomPortsTyped at checked
  have nodeChecked := (List.all_eq_true.mp checked) node
    (Data.Finite.mem_allFin node)
  rw [nodeData, Bool.and_eq_true] at nodeChecked
  rw [owner] at nodeChecked
  exact eq_of_beq nodeChecked.1

private theorem atom_arg_typed
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (node : diagram.NodeId) (region : diagram.RegionId) (args : List Sig)
    (nodeData : diagram.nodes node = .atom region args)
    (index : Nat) (bound : index < args.length)
    (wire : diagram.WireId)
    (owner : diagram.endpointOwner? ⟨node, .arg index⟩ = some wire) :
    (diagram.wires wire).sig = args[index] := by
  have checked := wellFormed.atom_ports_typed
  unfold ConcreteDiagram.AtomPortsTyped at checked
  have nodeChecked := (List.all_eq_true.mp checked) node
    (Data.Finite.mem_allFin node)
  rw [nodeData, Bool.and_eq_true] at nodeChecked
  have indexChecked := (List.all_eq_true.mp nodeChecked.2) index
    (by simpa using bound)
  rw [owner] at indexChecked
  have lookup : args[index]? = some args[index] :=
    List.getElem?_eq_getElem bound
  rw [lookup] at indexChecked
  exact eq_of_beq indexChecked

private theorem ref_arg_typed
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (node : diagram.NodeId) (region : diagram.RegionId)
    (definition : Fin definitions.length) (args : List Sig)
    (nodeData : diagram.nodes node = .ref region definition args)
    (index : Nat) (bound : index < args.length)
    (wire : diagram.WireId)
    (owner : diagram.endpointOwner? ⟨node, .arg index⟩ = some wire) :
    (diagram.wires wire).sig = args[index] := by
  have checked := wellFormed.ref_ports_typed
  unfold ConcreteDiagram.RefPortsTyped at checked
  have nodeChecked := (List.all_eq_true.mp checked) node
    (Data.Finite.mem_allFin node)
  rw [nodeData] at nodeChecked
  have indexChecked := (List.all_eq_true.mp nodeChecked) index
    (by simpa using bound)
  rw [owner] at indexChecked
  have lookup : args[index]? = some args[index] :=
    List.getElem?_eq_getElem bound
  rw [lookup] at indexChecked
  exact eq_of_beq indexChecked

private theorem resolveArgs?_complete
    (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram) (node : diagram.NodeId)
    (args : List Sig) (index : Nat)
    (complete : ∀ offset (bound : offset < args.length),
      ∃ resolved,
        resolvePort? diagram context node (.arg (index + offset))
          args[offset] = some resolved) :
    ∃ resolved, resolveArgs? diagram context node args index = some resolved := by
  induction args generalizing index with
  | nil => exact ⟨.nil, rfl⟩
  | cons sig rest ih =>
      obtain ⟨head, headResolved⟩ := complete 0 (by simp)
      obtain ⟨tail, tailResolved⟩ := ih (index := index + 1) (by
        intro offset bound
        obtain ⟨resolved, resolvedEq⟩ :=
          complete (offset + 1) (by simp; omega)
        exact ⟨resolved, by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            resolvedEq⟩)
      have headResolved' :
          resolvePort? diagram context node (.arg index) sig = some head := by
        simpa using headResolved
      exact ⟨.cons head tail, by
        simp [resolveArgs?, headResolved', tailResolved]⟩

private theorem resolveIdentityPorts?_complete
    (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram) (node : diagram.NodeId) (sig : Sig)
    (remaining index : Nat)
    (complete : ∀ offset (_bound : offset < remaining),
      ∃ resolved,
        resolvePort? diagram context node (.identity (index + offset)) sig =
          some resolved) :
    ∃ resolved,
      resolveIdentityPorts? diagram context node sig remaining index =
        some resolved := by
  induction remaining generalizing index with
  | zero => exact ⟨⟨[], rfl⟩, rfl⟩
  | succ remaining ih =>
      obtain ⟨head, headResolved⟩ := complete 0 (by omega)
      obtain ⟨tail, tailResolved⟩ := ih (index := index + 1) (by
        intro offset bound
        obtain ⟨resolved, resolvedEq⟩ :=
          complete (offset + 1) (by omega)
        exact ⟨resolved, by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            resolvedEq⟩)
      have headResolved' :
          resolvePort? diagram context node (.identity index) sig =
            some head := by
        simpa using headResolved
      exact ⟨⟨head :: tail.val, by simp [tail.property]⟩, by
        simp [resolveIdentityPorts?, headResolved', tailResolved]⟩

/--
Compile one checked identity directly from its exact concrete node and the
checker-owned incident wire for every required port. This is the narrow
identity compiler boundary used by source-driven generated identities.
-/
theorem compileNodes?_identity_singleton_of_incident
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (context : WireContext diagram)
    (node : diagram.NodeId)
    (region : diagram.RegionId)
    (sig : Sig)
    (arity : Nat)
    (nodeData : diagram.nodes node = .identity region sig arity)
    (portsVisible :
      ∀ index (_bound : index < arity),
        ∃ wire : diagram.WireId,
          (⟨node, .identity index⟩ : CEndpoint diagram.nodeCount) ∈
              (diagram.wires wire).endpoints ∧
            wire ∈ context.ids) :
    ∃ items : ItemSeq definitions context.sigs,
      compileNodes? definitions diagram context [node] = some items := by
  have arityWitness :=
    ConcreteDiagram.identity_arity definitions diagram wellFormed node
      region sig arity nodeData
  obtain ⟨ports, portsResolved⟩ :=
    resolveIdentityPorts?_complete diagram context node sig arity 0 (by
      intro index bound
      obtain ⟨wire, incident, visible⟩ := portsVisible index bound
      have required :
          CPort.identity index ∈ diagram.requiredPorts node := by
        simp [ConcreteDiagram.requiredPorts, nodeData, bound]
      have owner :=
        ConcreteDiagram.endpointOwner?_eq_of_incident definitions diagram
          wellFormed node (.identity index) required wire incident
      have signature :=
        ConcreteDiagram.identity_port_typed definitions diagram wellFormed
          node region sig arity nodeData index bound wire owner
      obtain ⟨wireVar, wireResolved⟩ :=
        resolveWire?_complete diagram context wire visible
      exact
        ⟨signature ▸ wireVar, by
          simp [resolvePort?, owner, resolveExpected?, signature,
            wireResolved]⟩)
  let item : Item definitions context.sigs :=
    .identity sig ports.val (by
      simpa only [ports.property] using arityWitness)
  refine ⟨.cons item .nil, ?_⟩
  simp [compileNodes?, compileNode?, nodeData, arityWitness, portsResolved,
    item]

private theorem compileIdentityNode?_forward_denotation
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (leftWellFormed : left.WellFormed definitions)
    (rightWellFormed : right.WellFormed definitions)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    {pre : PreModel}
    (definitionEnv : DefinitionEnv pre definitions)
    {leftEnv : Env pre leftContext.sigs}
    {rightEnv : Env pre rightContext.sigs}
    (envs : EnvironmentsCorrespond iso leftContext rightContext
      leftEnv rightEnv)
    {node : left.NodeId} {region : left.RegionId}
    {sig : Sig} {arity : Nat}
    (nodeData : left.nodes node = .identity region sig arity)
    (leftItem : Item definitions leftContext.sigs)
    (leftCompiled :
      compileNode? definitions left leftContext node = some leftItem) :
    ∃ rightItem,
      compileNode? definitions right rightContext (iso.nodes node) =
        some rightItem ∧
      (denoteItem pre definitionEnv leftEnv leftItem ↔
        denoteItem pre definitionEnv rightEnv rightItem) := by
  simp only [compileNode?, nodeData] at leftCompiled
  split at leftCompiled
  · rename_i arityWitness
    cases portsEquation :
        resolveIdentityPorts? left leftContext node sig arity 0 with
    | none =>
        simp [portsEquation] at leftCompiled
    | some leftPorts =>
        have itemEquality :
            (Item.identity sig leftPorts.val (by
              simpa [leftPorts.property] using arityWitness) :
              Item definitions leftContext.sigs) = leftItem := by
          exact Option.some.inj (by
            simpa [portsEquation] using leftCompiled)
        subst leftItem
        have rightNodeData :
            right.nodes (iso.nodes node) =
              .identity (iso.regions region) sig arity := by
          rw [iso.node_table, nodeData]
          rfl
        obtain ⟨rightPorts, rightPortsEquation⟩ :=
          resolveIdentityPorts?_complete right rightContext (iso.nodes node)
            sig arity 0 (by
              intro targetIndex targetBound
              obtain ⟨targetWire, targetOwner⟩ :=
                ConcreteDiagram.endpointOwner?_complete definitions right
                  rightWellFormed (iso.nodes node)
                  (.identity targetIndex)
                  (by
                    simp [ConcreteDiagram.requiredPorts, rightNodeData,
                      targetBound])
              obtain ⟨sourceIndex, sourceOwner⟩ :=
                iso.identity_owner_backward leftWellFormed nodeData targetOwner
              have sourceIncident :=
                ConcreteDiagram.endpointOwner?_incident left
                  ⟨node, .identity sourceIndex⟩
                  (iso.wires.symm targetWire) sourceOwner
              have sourceRequired :=
                ConcreteDiagram.incident_port_required definitions left
                  leftWellFormed (iso.wires.symm targetWire)
                  ⟨node, .identity sourceIndex⟩ sourceIncident
              have sourceBound : sourceIndex < arity := by
                simpa [ConcreteDiagram.requiredPorts, nodeData] using
                  sourceRequired
              obtain ⟨leftVar, leftResolved, _⟩ :=
                resolveIdentityPorts?_at left leftContext node sig arity 0
                  leftPorts portsEquation sourceIndex sourceBound
              have leftExpected :
                  resolveExpected? left leftContext
                      (iso.wires.symm targetWire) sig =
                    some leftVar := by
                simpa [resolvePort?, sourceOwner] using leftResolved
              obtain ⟨rightVar, rightExpected, _⟩ :=
                resolveExpected?_forward_value iso contexts envs
                  (iso.wires.symm targetWire) sig leftVar leftExpected
              have mappedWire :
                  iso.wires (iso.wires.symm targetWire) = targetWire :=
                iso.wires.right_inv targetWire
              refine ⟨rightVar, ?_⟩
              rw [mappedWire] at rightExpected
              simpa [resolvePort?, targetOwner] using rightExpected)
        let rightItem : Item definitions rightContext.sigs :=
          .identity sig rightPorts.val (by
            simpa [rightPorts.property] using arityWitness)
        refine ⟨rightItem, ?_, ?_⟩
        · simp [rightItem, compileNode?, rightNodeData, arityWitness,
            rightPortsEquation]
        · simp only [rightItem, denoteItem_identity]
          apply AllEqual.iff_of_mem_iff
          intro value
          constructor
          · intro member
            rcases List.mem_map.mp member with
              ⟨leftVar, leftMember, leftValue⟩
            obtain ⟨sourceIndex, sourceBound, leftResolved⟩ :=
              resolveIdentityPorts?_mem left leftContext node sig arity 0
                leftPorts portsEquation leftVar leftMember
            obtain ⟨targetIndex, rightVar, rightResolved, valuesEqual⟩ :=
              resolveIdentityPort?_forward_value iso rightWellFormed
                contexts envs nodeData sourceIndex leftVar
                  (by simpa using leftResolved)
            have targetBound :=
              identity_resolved_index_bound definitions right rightWellFormed
                rightContext (iso.nodes node) (iso.regions region) sig arity
                targetIndex rightNodeData rightVar rightResolved
            have rightMember :=
              resolveIdentityPorts?_member_of_resolved right rightContext
                (iso.nodes node) sig arity 0 rightPorts rightPortsEquation
                targetIndex targetBound rightVar (by simpa using rightResolved)
            exact List.mem_map.mpr
              ⟨rightVar, rightMember, valuesEqual.symm.trans leftValue⟩
          · intro member
            rcases List.mem_map.mp member with
              ⟨rightVar, rightMember, rightValue⟩
            obtain ⟨targetIndex, targetBound, rightResolved⟩ :=
              resolveIdentityPorts?_mem right rightContext (iso.nodes node)
                sig arity 0 rightPorts rightPortsEquation rightVar rightMember
            obtain ⟨sourceIndex, leftVar, leftResolved, valuesEqual⟩ :=
              resolveIdentityPort?_backward_value iso leftWellFormed
                contexts envs nodeData targetIndex rightVar
                  (by simpa using rightResolved)
            have sourceBound :=
              identity_resolved_index_bound definitions left leftWellFormed
                leftContext node region sig arity sourceIndex nodeData
                leftVar leftResolved
            have leftMember :=
              resolveIdentityPorts?_member_of_resolved left leftContext node
                sig arity 0 leftPorts portsEquation sourceIndex sourceBound
                leftVar (by simpa using leftResolved)
            exact List.mem_map.mpr
              ⟨leftVar, leftMember, valuesEqual.trans rightValue⟩
  · simp at leftCompiled

private theorem compileNode?_forward_denotation
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (leftWellFormed : left.WellFormed definitions)
    (rightWellFormed : right.WellFormed definitions)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    {pre : PreModel}
    (definitionEnv : DefinitionEnv pre definitions)
    {leftEnv : Env pre leftContext.sigs}
    {rightEnv : Env pre rightContext.sigs}
    (envs : EnvironmentsCorrespond iso leftContext rightContext
      leftEnv rightEnv)
    (node : left.NodeId)
    (leftItem : Item definitions leftContext.sigs)
    (leftCompiled :
      compileNode? definitions left leftContext node = some leftItem) :
    ∃ rightItem,
      compileNode? definitions right rightContext (iso.nodes node) =
        some rightItem ∧
      (denoteItem pre definitionEnv leftEnv leftItem ↔
        denoteItem pre definitionEnv rightEnv rightItem) := by
  cases nodeData : left.nodes node with
  | atom region args =>
      exact compileAtomNode?_forward_denotation iso leftWellFormed
        rightWellFormed contexts definitionEnv envs nodeData leftItem
        leftCompiled
  | ref region definition args =>
      exact compileRefNode?_forward_denotation iso leftWellFormed
        rightWellFormed contexts definitionEnv envs nodeData leftItem
        leftCompiled
  | identity region sig arity =>
      exact compileIdentityNode?_forward_denotation iso leftWellFormed
        rightWellFormed contexts definitionEnv envs nodeData leftItem
        leftCompiled

/-- Transport one accepted singleton compilation across a concrete isomorphism. -/
theorem compileNodes?_singleton_forward_denotation
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (leftWellFormed : left.WellFormed definitions)
    (rightWellFormed : right.WellFormed definitions)
    {leftContext : WireContext left} {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    {pre : PreModel} (definitionEnv : DefinitionEnv pre definitions)
    {leftEnv : Env pre leftContext.sigs} {rightEnv : Env pre rightContext.sigs}
    (envs : EnvironmentsCorrespond iso leftContext rightContext
      leftEnv rightEnv)
    (node : left.NodeId) (leftItem : Item definitions leftContext.sigs)
    (leftCompiled :
      compileNodes? definitions left leftContext [node] =
        some (.cons leftItem .nil)) :
    ∃ rightItem,
      compileNodes? definitions right rightContext [iso.nodes node] =
          some (.cons rightItem .nil) ∧
        (denoteItem pre definitionEnv leftEnv leftItem ↔
          denoteItem pre definitionEnv rightEnv rightItem) := by
  cases leftEquation : compileNode? definitions left leftContext node with
  | none => simp [compileNodes?, leftEquation] at leftCompiled
  | some actual =>
      have sequenceExact :
          (ItemSeq.cons actual .nil :
            ItemSeq definitions leftContext.sigs) =
          .cons leftItem .nil :=
        Option.some.inj (by
          simpa [compileNodes?, leftEquation] using leftCompiled)
      have actualExact : actual = leftItem :=
        (ItemSeq.cons.inj sequenceExact).1
      subst actual
      obtain ⟨rightItem, rightCompiled, denotation⟩ :=
        compileNode?_forward_denotation iso leftWellFormed rightWellFormed
          contexts definitionEnv envs node leftItem leftEquation
      exact ⟨rightItem, by simp [compileNodes?, rightCompiled], denotation⟩

private theorem reference_signature
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (node : diagram.NodeId) (region : diagram.RegionId)
    (definition : Fin definitions.length) (args : List Sig)
    (nodeData : diagram.nodes node = .ref region definition args) :
    definitions.get definition = args := by
  have checked := wellFormed.references_match
  unfold ConcreteDiagram.ReferencesMatch at checked
  have nodeChecked := (List.all_eq_true.mp checked) node
    (Data.Finite.mem_allFin node)
  rw [nodeData] at nodeChecked
  exact (eq_of_beq nodeChecked).symm

private theorem compileNode?_complete
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (context : WireContext diagram) (region : diagram.RegionId)
    (coverage : context.Covers region)
    (node : diagram.NodeId)
    (nodeRegion : (diagram.nodes node).region = region) :
    ∃ item, compileNode? definitions diagram context node = some item := by
  cases nodeData : diagram.nodes node with
  | atom storedRegion args =>
      obtain ⟨head, headResolved⟩ := resolvePort?_complete
        definitions diagram wellFormed context region coverage node nodeRegion
        .head (.rel args)
        (by simp [ConcreteDiagram.requiredPorts, nodeData])
        (atom_head_typed definitions diagram wellFormed node storedRegion args
          nodeData)
      obtain ⟨arguments, argumentsResolved⟩ :=
        resolveArgs?_complete diagram context node args 0 (by
          intro offset bound
          apply resolvePort?_complete definitions diagram wellFormed
            context region coverage node nodeRegion
          · simp [ConcreteDiagram.requiredPorts, nodeData, bound]
          · simpa using atom_arg_typed definitions diagram wellFormed node
              storedRegion args nodeData offset bound)
      exact ⟨.atom head arguments, by
        unfold compileNode?
        rw [nodeData]
        simp [headResolved, argumentsResolved]⟩
  | ref storedRegion definition args =>
      have signature := reference_signature definitions diagram wellFormed
        node storedRegion definition args nodeData
      have signatureGetElem : definitions[definition.val] = args := by
        change definitions.get definition = args
        exact signature
      obtain ⟨arguments, argumentsResolved⟩ :=
        resolveArgs?_complete diagram context node args 0 (by
          intro offset bound
          apply resolvePort?_complete definitions diagram wellFormed
            context region coverage node nodeRegion
          · simp [ConcreteDiagram.requiredPorts, nodeData, bound]
          · simpa using ref_arg_typed definitions diagram wellFormed node
              storedRegion definition args nodeData offset bound)
      exact ⟨.named (signature ▸ definitionVarAt definitions definition)
        arguments, by
          unfold compileNode?
          rw [nodeData]
          simp [signatureGetElem, argumentsResolved]⟩
  | identity storedRegion sig arity =>
      have arityWitness := ConcreteDiagram.identity_arity definitions diagram
        wellFormed
        node storedRegion sig arity nodeData
      obtain ⟨ports, portsResolved⟩ :=
        resolveIdentityPorts?_complete diagram context node sig arity 0 (by
          intro offset bound
          apply resolvePort?_complete definitions diagram wellFormed
            context region coverage node nodeRegion
          · simp [ConcreteDiagram.requiredPorts, nodeData, bound]
          · simpa using ConcreteDiagram.identity_port_typed definitions diagram
              wellFormed node storedRegion sig arity nodeData offset bound)
      exact ⟨.identity sig ports.val (by
        simpa [ports.property] using arityWitness), by
          unfold compileNode?
          rw [nodeData]
          simp [arityWitness, portsResolved]⟩

theorem compileNodes?_complete
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (context : WireContext diagram) (region : diagram.RegionId)
    (coverage : context.Covers region) :
    (nodes : List diagram.NodeId) →
    (∀ node, node ∈ nodes → (diagram.nodes node).region = region) →
    ∃ items, compileNodes? definitions diagram context nodes = some items
  | [], _ => ⟨.nil, rfl⟩
  | node :: tail, owns => by
      obtain ⟨head, headCompiled⟩ := compileNode?_complete definitions diagram
        wellFormed context region coverage node (owns node (by simp))
      obtain ⟨rest, restCompiled⟩ := compileNodes?_complete definitions diagram
        wellFormed context region coverage tail (by
          intro candidate member
          exact owns candidate (by simp [member]))
      exact ⟨.cons head rest, by
        simp [compileNodes?, headCompiled, restCompiled]⟩

/-- Decompose an accepted nonempty node compilation into its singleton head. -/
theorem compileNodes?_cons_components
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : WireContext diagram) (node : diagram.NodeId)
    (tail : List diagram.NodeId) (items : ItemSeq definitions context.sigs)
    (compiled :
      compileNodes? definitions diagram context (node :: tail) = some items) :
    ∃ head rest,
      compileNodes? definitions diagram context [node] =
          some (.cons head .nil) ∧
        compileNodes? definitions diagram context tail = some rest ∧
        items = .cons head rest := by
  cases headEquation : compileNode? definitions diagram context node with
  | none => simp [compileNodes?, headEquation] at compiled
  | some head =>
      cases tailEquation : compileNodes? definitions diagram context tail with
      | none => simp [compileNodes?, headEquation, tailEquation] at compiled
      | some rest =>
          refine ⟨head, rest, by simp [compileNodes?, headEquation],
            rfl, ?_⟩
          exact Option.some.inj
            (by simpa [compileNodes?, headEquation, tailEquation] using
              compiled) |>.symm

end ConcreteElaboration

end VisualProof
