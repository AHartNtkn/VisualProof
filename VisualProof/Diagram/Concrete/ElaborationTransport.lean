import VisualProof.Diagram.Concrete.ElaborationKernel
namespace VisualProof
universe u

namespace ConcreteElaboration

open Internal

private abbrev wireOfVar (diagram : ConcreteDiagram definitionCount) :
    {ids : List diagram.WireId} → {sig : Sig} →
      Var (ids.map fun id => (diagram.wires id).sig) sig →
      diagram.WireId :=
  fun {ids} {_} value =>
    WireContext.origin diagram ids value

theorem Internal.origin_member
    (diagram : ConcreteDiagram definitionCount)
    {ids : List diagram.WireId} {sig : Sig}
    (value : Var (ids.map fun id => (diagram.wires id).sig) sig) :
    WireContext.origin diagram ids value ∈ ids := by
  induction ids with
  | nil => nomatch value
  | cons head tail ih =>
      cases value with
      | here =>
          simp [WireContext.origin]
      | there value =>
          simpa [wireOfVar, WireContext.origin] using
            List.mem_cons_of_mem head (ih value)

private theorem wireOfVar_signature
    (diagram : ConcreteDiagram definitionCount)
    {ids : List diagram.WireId} {sig : Sig}
    (value : Var (ids.map fun id => (diagram.wires id).sig) sig) :
    (diagram.wires (wireOfVar diagram value)).sig = sig := by
  induction ids with
  | nil => nomatch value
  | cons head tail ih =>
      cases value with
      | here =>
          simp [wireOfVar, WireContext.origin]
      | there value =>
          simpa [wireOfVar, WireContext.origin] using ih value

private theorem cast_var_there
    {left right : Sig} (equality : left = right)
    (value : Var context left) :
    Var.there (equality ▸ value) =
      equality ▸ (Var.there value : Var (head :: context) left) := by
  cases equality
  rfl

private theorem cast_var_cancel
    {left right : Sig} (equality : left = right)
    (value : Var context right) :
    equality ▸ (equality.symm ▸ value) = value := by
  cases equality
  rfl

private theorem wireOfVar_resolveWireIn
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId) (wire : diagram.WireId)
    {resolved :
      Var (ids.map fun id => (diagram.wires id).sig)
        (diagram.wires wire).sig}
    (equation : resolveWireIn? diagram ids wire = some resolved) :
    wireOfVar diagram resolved = wire := by
  induction ids with
  | nil => simp [resolveWireIn?] at equation
  | cons head tail ih =>
      by_cases equality : wire = head
      · subst wire
        simp [resolveWireIn?] at equation
        subst resolved
        simp [wireOfVar, WireContext.origin]
      · cases tailEquation : resolveWireIn? diagram tail wire with
        | none =>
            simp [resolveWireIn?, equality, tailEquation] at equation
        | some tailVar =>
            have resolvedEquality : .there tailVar = resolved := by
              exact Option.some.inj (by
                simpa [resolveWireIn?, equality, tailEquation] using equation)
            subst resolved
            simpa [wireOfVar, WireContext.origin] using
              ih tailEquation

theorem Internal.origin_of_resolvedExpected
    (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram) (wire : diagram.WireId)
    (expected : Sig) {resolved : Var context.sigs expected}
    (equation :
      resolveExpected? diagram context wire expected = some resolved) :
    WireContext.origin diagram context.ids resolved = wire := by
  unfold resolveExpected? at equation
  split at equation
  · rename_i signature
    subst expected
    cases wireEquation : resolveWire? diagram context wire with
    | none => simp [wireEquation] at equation
    | some wireVar =>
        have variableEquality : wireVar = resolved := by
          exact Option.some.inj (by simpa [wireEquation] using equation)
        subst resolved
        exact wireOfVar_resolveWireIn diagram context.ids wire
          wireEquation
  · simp at equation

private theorem resolveWireIn?_wireOfVar
    (diagram : ConcreteDiagram definitionCount)
    {ids : List diagram.WireId} (nodup : ids.Nodup)
    {sig : Sig}
    (value : Var (ids.map fun id => (diagram.wires id).sig) sig) :
    resolveWireIn? diagram ids (wireOfVar diagram value) =
      some ((wireOfVar_signature diagram value).symm ▸ value) := by
  induction ids with
  | nil => nomatch value
  | cons head tail induction =>
      cases value with
      | here =>
          simp [resolveWireIn?, wireOfVar, WireContext.origin]
      | there value =>
          rw [List.nodup_cons] at nodup
          have tailNodup := nodup.2
          have tailMember := origin_member diagram value
          have notHead : wireOfVar diagram value ≠ head := by
            intro equality
            exact nodup.1 (by simpa [equality] using tailMember)
          have tailResolved := induction tailNodup value
          simp only [resolveWireIn?, wireOfVar, WireContext.origin,
            notHead, ↓reduceDIte, tailResolved, Option.map_some]
          congr 1
          exact cast_var_there
            (wireOfVar_signature diagram value).symm value

theorem Internal.resolveExpected?_origin
    (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram) (nodup : context.ids.Nodup)
    {sig : Sig} (value : Var context.sigs sig) :
    resolveExpected? diagram context
        (WireContext.origin diagram context.ids value) sig =
      some value := by
  have signature := wireOfVar_signature diagram value
  unfold resolveExpected?
  rw [dif_pos signature]
  simp only [resolveWire?]
  rw [resolveWireIn?_wireOfVar diagram nodup value]
  change some (signature ▸ (signature.symm ▸ value)) = some value
  rw [cast_var_cancel]

private theorem resolvePort?_map
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (rightWellFormed : right.WellFormed definitions)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (rightContextNodup : rightContext.ids.Nodup)
    (rho : WireRenaming leftContext.sigs rightContext.sigs)
    (wireMap : left.WireId → right.WireId)
    (contextAction : ∀ {sig} (value : Var leftContext.sigs sig),
      WireContext.origin right rightContext.ids (rho value) =
        wireMap
          (WireContext.origin left leftContext.ids value))
    {leftNode : left.NodeId}
    {rightNode : right.NodeId}
    {port : CPort}
    {expected : Sig}
    (targetRequired : port ∈ right.requiredPorts rightNode)
    (forwardIncident : ∀ (wire : left.WireId),
      (⟨leftNode, port⟩ : CEndpoint left.nodeCount) ∈
          (left.wires wire).endpoints →
        (⟨rightNode, port⟩ : CEndpoint right.nodeCount) ∈
          (right.wires (wireMap wire)).endpoints)
    {resolved : Var leftContext.sigs expected}
    (sourceResolved :
      resolvePort? left leftContext leftNode port expected =
        some resolved) :
    resolvePort? right rightContext rightNode port expected =
      some (rho resolved) := by
  unfold resolvePort? at sourceResolved ⊢
  cases sourceOwner :
      left.endpointOwner? ⟨leftNode, port⟩ with
  | none =>
      simp [sourceOwner] at sourceResolved
  | some sourceWire =>
      have sourceExpected :
          resolveExpected? left leftContext sourceWire expected =
            some resolved := by
        simpa [sourceOwner] using sourceResolved
      have sourceIncident :=
        ConcreteDiagram.endpointOwner?_incident left
          ⟨leftNode, port⟩ sourceWire sourceOwner
      have targetIncident :=
        forwardIncident sourceWire sourceIncident
      have targetOwner :=
        ConcreteDiagram.endpointOwner?_eq_of_incident definitions right
          rightWellFormed rightNode port targetRequired
          (wireMap sourceWire) targetIncident
      rw [targetOwner]
      have targetResolved :=
        resolveExpected?_origin right rightContext
          rightContextNodup (rho resolved)
      have sourceOrigin :=
        origin_of_resolvedExpected left leftContext sourceWire expected
          sourceExpected
      have mappedOrigin := contextAction resolved
      rw [mappedOrigin, sourceOrigin] at targetResolved
      exact targetResolved

private theorem resolveArgs?_map
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (rightWellFormed : right.WellFormed definitions)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (rightContextNodup : rightContext.ids.Nodup)
    (rho : WireRenaming leftContext.sigs rightContext.sigs)
    (wireMap : left.WireId → right.WireId)
    (contextAction : ∀ {sig} (value : Var leftContext.sigs sig),
      WireContext.origin right rightContext.ids (rho value) =
        wireMap
          (WireContext.origin left leftContext.ids value))
    {leftNode : left.NodeId}
    {rightNode : right.NodeId}
    (forwardIncident : ∀ (port : CPort) (wire : left.WireId),
      (⟨leftNode, port⟩ : CEndpoint left.nodeCount) ∈
          (left.wires wire).endpoints →
        (⟨rightNode, port⟩ : CEndpoint right.nodeCount) ∈
          (right.wires (wireMap wire)).endpoints)
    (args : List Sig)
    (index : Nat)
    (targetRequired : ∀ offset (_bound : offset < args.length),
      CPort.arg (index + offset) ∈
        right.requiredPorts rightNode)
    {resolved : Vars leftContext.sigs args}
    (sourceResolved :
      resolveArgs? left leftContext leftNode args index =
        some resolved) :
    resolveArgs? right rightContext rightNode args index =
      some (resolved.rename rho) := by
  induction args generalizing index with
  | nil =>
      have resolvedEquality :
          (.nil : Vars leftContext.sigs []) = resolved :=
        Option.some.inj sourceResolved
      subst resolved
      rfl
  | cons sig rest induction =>
      cases headEquation :
          resolvePort? left leftContext leftNode (.arg index) sig with
      | none =>
          simp [resolveArgs?, headEquation] at sourceResolved
      | some head =>
          cases tailEquation :
              resolveArgs? left leftContext leftNode rest (index + 1) with
          | none =>
              simp [resolveArgs?, headEquation, tailEquation]
                at sourceResolved
          | some tail =>
              have resolvedEquality :
                  (Vars.cons head tail :
                    Vars leftContext.sigs (sig :: rest)) =
                    resolved := by
                exact Option.some.inj (by
                  simpa [resolveArgs?, headEquation, tailEquation] using
                    sourceResolved)
              subst resolved
              have targetHead :=
                resolvePort?_map rightWellFormed rightContextNodup
                  rho wireMap contextAction
                  (targetRequired 0 (by simp))
                  (forwardIncident (.arg index))
                  headEquation
              have targetTail :=
                induction (index := index + 1)
                  (resolved := tail)
                  (fun offset bound => by
                    have required :=
                      targetRequired (offset + 1) (by simp; omega)
                    simpa [Nat.add_assoc, Nat.add_comm,
                      Nat.add_left_comm] using required)
                  tailEquation
              have targetHead' :
                  resolvePort? right rightContext rightNode
                      (.arg index) sig =
                    some (rho head) := by
                simpa using targetHead
              simp [resolveArgs?, targetHead', targetTail, Vars.rename]

private theorem resolveIdentityPorts?_map
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (rightWellFormed : right.WellFormed definitions)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (rightContextNodup : rightContext.ids.Nodup)
    (rho : WireRenaming leftContext.sigs rightContext.sigs)
    (wireMap : left.WireId → right.WireId)
    (contextAction : ∀ {sig} (value : Var leftContext.sigs sig),
      WireContext.origin right rightContext.ids (rho value) =
        wireMap
          (WireContext.origin left leftContext.ids value))
    {leftNode : left.NodeId}
    {rightNode : right.NodeId}
    (forwardIncident : ∀ (port : CPort) (wire : left.WireId),
      (⟨leftNode, port⟩ : CEndpoint left.nodeCount) ∈
          (left.wires wire).endpoints →
        (⟨rightNode, port⟩ : CEndpoint right.nodeCount) ∈
          (right.wires (wireMap wire)).endpoints)
    (sig : Sig)
    (remaining index : Nat)
    (targetRequired : ∀ offset (_bound : offset < remaining),
      CPort.identity (index + offset) ∈
        right.requiredPorts rightNode)
    {resolved : { ports : List (Var leftContext.sigs sig) //
      ports.length = remaining }}
    (sourceResolved :
      resolveIdentityPorts? left leftContext leftNode sig remaining index =
        some resolved) :
    resolveIdentityPorts? right rightContext rightNode sig remaining index =
      some
        ⟨resolved.val.map (rho (sig := sig)), by
          simpa [resolved.property]⟩ := by
  induction remaining generalizing index with
  | zero =>
      have portsEmpty : resolved.val = [] :=
        List.length_eq_zero_iff.mp resolved.property
      apply congrArg some
      apply Subtype.ext
      simp [resolveIdentityPorts?, portsEmpty]
  | succ remaining induction =>
      cases headEquation :
          resolvePort? left leftContext leftNode
            (.identity index) sig with
      | none =>
          simp [resolveIdentityPorts?, headEquation] at sourceResolved
      | some head =>
          cases tailEquation :
              resolveIdentityPorts? left leftContext leftNode sig
                remaining (index + 1) with
          | none =>
              simp [resolveIdentityPorts?, headEquation, tailEquation]
                at sourceResolved
          | some tail =>
              have resolvedEquality :
                  (⟨head :: tail.val, by simp [tail.property]⟩ :
                    { ports : List (Var leftContext.sigs sig) //
                      ports.length = remaining + 1 }) =
                    resolved := by
                exact Option.some.inj (by
                  simpa [resolveIdentityPorts?, headEquation,
                    tailEquation] using sourceResolved)
              subst resolved
              have targetHead :=
                resolvePort?_map rightWellFormed rightContextNodup
                  rho wireMap contextAction
                  (targetRequired 0 (by omega))
                  (forwardIncident (.identity index))
                  headEquation
              have targetTail :=
                induction (index := index + 1)
                  (resolved := tail)
                  (fun offset bound => by
                    have required :=
                      targetRequired (offset + 1) (by omega)
                    simpa [Nat.add_assoc, Nat.add_comm,
                      Nat.add_left_comm] using required)
                  tailEquation
              have targetHead' :
                  resolvePort? right rightContext rightNode
                      (.identity index) sig =
                    some (rho head) := by
                simpa using targetHead
              simp [resolveIdentityPorts?, targetHead', targetTail]

/-- Compile one copied node under a context-local wire action.  No global
wire-signature map is required: only variables visible in the supplied
contexts and incidences of the copied node participate in elaboration. -/
theorem compileNode?_natural
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (rightWellFormed : right.WellFormed definitions)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (rightContextNodup : rightContext.ids.Nodup)
    (rho : WireRenaming leftContext.sigs rightContext.sigs)
    (wireMap : left.WireId → right.WireId)
    (contextAction : ∀ {sig} (value : Var leftContext.sigs sig),
      WireContext.origin right rightContext.ids (rho value) =
        wireMap
          (WireContext.origin left leftContext.ids value))
    (regionMap : left.RegionId → right.RegionId)
    {leftNode : left.NodeId}
    {rightNode : right.NodeId}
    (nodeShape :
      right.nodes rightNode =
        match left.nodes leftNode with
        | .atom region args =>
            .atom (regionMap region) args
        | .ref region definition args =>
            .ref (regionMap region) definition args
        | .identity region sig arity =>
            .identity (regionMap region) sig arity)
    (forwardIncident : ∀ (port : CPort) (wire : left.WireId),
      (⟨leftNode, port⟩ : CEndpoint left.nodeCount) ∈
          (left.wires wire).endpoints →
        (⟨rightNode, port⟩ : CEndpoint right.nodeCount) ∈
          (right.wires (wireMap wire)).endpoints)
    {sourceItem : Item definitions leftContext.sigs}
    (sourceCompiled :
      compileNode? definitions left leftContext leftNode =
        some sourceItem) :
    compileNode? definitions right rightContext rightNode =
      some (sourceItem.renameWires rho) := by
  cases sourceNodeData : left.nodes leftNode with
  | atom sourceRegion args =>
      have targetNodeData :
          right.nodes rightNode =
            .atom (regionMap sourceRegion) args := by
        rw [nodeShape, sourceNodeData]
      cases headEquation :
          resolvePort? left leftContext leftNode .head (.rel args) with
      | none =>
          simp [compileNode?_equation, sourceNodeData, headEquation]
            at sourceCompiled
      | some head =>
          cases argsEquation :
              resolveArgs? left leftContext leftNode args 0 with
          | none =>
              simp [compileNode?_equation, sourceNodeData, headEquation,
                argsEquation] at sourceCompiled
          | some arguments =>
              have sourceItemEquality :
                  (Item.atom head arguments :
                    Item definitions leftContext.sigs) =
                    sourceItem := by
                exact Option.some.inj (by
                  simpa [compileNode?_equation, sourceNodeData, headEquation,
                    argsEquation] using sourceCompiled)
              subst sourceItem
              have targetHead :=
                resolvePort?_map rightWellFormed rightContextNodup
                  rho wireMap contextAction
                  (by
                    simp [ConcreteDiagram.requiredPorts,
                      targetNodeData])
                  (forwardIncident .head)
                  headEquation
              have targetArguments :=
                resolveArgs?_map rightWellFormed rightContextNodup
                  rho wireMap contextAction forwardIncident
                  args 0
                  (by
                    intro offset bound
                    simp [ConcreteDiagram.requiredPorts,
                      targetNodeData, bound])
                  argsEquation
              simp [compileNode?_equation, targetNodeData, targetHead,
                targetArguments, Item.renameWires]
  | ref sourceRegion definition args =>
      have targetNodeData :
          right.nodes rightNode =
            .ref (regionMap sourceRegion) definition args := by
        rw [nodeShape, sourceNodeData]
      simp only [compileNode?_equation, sourceNodeData] at sourceCompiled
      split at sourceCompiled
      · rename_i signature
        cases argsEquation :
            resolveArgs? left leftContext leftNode args 0 with
        | none =>
            simp [argsEquation] at sourceCompiled
        | some arguments =>
            let reference : DefVar definitions args :=
              signature ▸ definitionVarAt definitions definition
            have sourceItemEquality :
                (Item.named reference arguments :
                  Item definitions leftContext.sigs) =
                  sourceItem := by
              exact Option.some.inj (by
                simpa [argsEquation, reference] using sourceCompiled)
            subst sourceItem
            have targetArguments :=
              resolveArgs?_map rightWellFormed rightContextNodup
                rho wireMap contextAction forwardIncident
                args 0
                (by
                  intro offset bound
                  simp [ConcreteDiagram.requiredPorts,
                    targetNodeData, bound])
                argsEquation
            simp only [compileNode?_equation, targetNodeData]
            split
            · simp [targetArguments, reference,
                Item.renameWires]
            · contradiction
      · simp at sourceCompiled
  | identity sourceRegion sig arity =>
      have targetNodeData :
          right.nodes rightNode =
            .identity (regionMap sourceRegion) sig arity := by
        rw [nodeShape, sourceNodeData]
      simp only [compileNode?_equation, sourceNodeData] at sourceCompiled
      split at sourceCompiled
      · rename_i arityWitness
        cases portsEquation :
            resolveIdentityPorts? left leftContext leftNode sig arity 0 with
        | none =>
            simp [portsEquation] at sourceCompiled
        | some ports =>
            have sourceItemEquality :
                (Item.identity sig ports.val (by
                  simpa [ports.property] using arityWitness) :
                  Item definitions leftContext.sigs) =
                  sourceItem := by
              exact Option.some.inj (by
                simpa [portsEquation] using sourceCompiled)
            subst sourceItem
            have targetPorts :=
              resolveIdentityPorts?_map rightWellFormed
                rightContextNodup rho wireMap contextAction
                forwardIncident sig arity 0
                (by
                  intro offset bound
                  simp [ConcreteDiagram.requiredPorts,
                    targetNodeData, bound])
                portsEquation
            simp [compileNode?_equation, targetNodeData, arityWitness,
              targetPorts, Item.renameWires]
      · simp at sourceCompiled

/--
Compile one structurally copied node under an exact context renaming.  The
target compilation is generated by this theorem; callers provide only the
wire/node incidence facts that make the copied node visible.
-/
theorem compileNodes?_singleton_natural
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (rightWellFormed : right.WellFormed definitions)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (rightContextNodup : rightContext.ids.Nodup)
    (rho : WireRenaming leftContext.sigs rightContext.sigs)
    (wireMap : left.WireId → right.WireId)
    (_wireSignature : ∀ wire,
      (right.wires (wireMap wire)).sig =
        (left.wires wire).sig)
    (contextAction : ∀ {sig} (value : Var leftContext.sigs sig),
      WireContext.origin right rightContext.ids (rho value) =
        wireMap
          (WireContext.origin left leftContext.ids value))
    (regionMap : left.RegionId → right.RegionId)
    (leftNode : left.NodeId)
    (rightNode : right.NodeId)
    (nodeShape :
      right.nodes rightNode =
        match left.nodes leftNode with
        | .atom region args =>
            .atom (regionMap region) args
        | .ref region definition args =>
            .ref (regionMap region) definition args
        | .identity region sig arity =>
            .identity (regionMap region) sig arity)
    (forwardIncident : ∀ (port : CPort) (wire : left.WireId),
      (⟨leftNode, port⟩ : CEndpoint left.nodeCount) ∈
          (left.wires wire).endpoints →
        (⟨rightNode, port⟩ : CEndpoint right.nodeCount) ∈
          (right.wires (wireMap wire)).endpoints)
    {sourceItems : ItemSeq definitions leftContext.sigs}
    (sourceCompiled :
      compileNodes? definitions left leftContext [leftNode] =
        some sourceItems) :
    ∃ targetItems : ItemSeq definitions rightContext.sigs,
      compileNodes? definitions right rightContext [rightNode] =
          some targetItems ∧
        targetItems = sourceItems.renameWires rho := by
  cases sourceNodeEquation :
      compileNode? definitions left leftContext leftNode with
  | none =>
      simp [compileNodes?_equation, sourceNodeEquation] at sourceCompiled
  | some sourceItem =>
      have sourceItemsEquality :
          (ItemSeq.cons sourceItem .nil :
            ItemSeq definitions leftContext.sigs) =
            sourceItems := by
        exact Option.some.inj (by
          simpa [compileNodes?_equation, sourceNodeEquation] using
            sourceCompiled)
      subst sourceItems
      have targetNodeEquation :=
        compileNode?_natural rightWellFormed rightContextNodup
          rho wireMap contextAction regionMap nodeShape
          forwardIncident sourceNodeEquation
      refine
        ⟨.cons (sourceItem.renameWires rho) .nil, ?_, rfl⟩
      simp [compileNodes?_equation, targetNodeEquation]

private theorem resolvePort?_reflect
    {definitions : List (List Sig)}
    {target source : ConcreteDiagram definitions.length}
    {targetContext : WireContext target}
    {sourceContext : WireContext source}
    (sourceContextNodup : sourceContext.ids.Nodup)
    (rho : WireRenaming targetContext.sigs sourceContext.sigs)
    (wireOrigin : target.WireId → source.WireId)
    (wireSignature : ∀ wire,
      (source.wires (wireOrigin wire)).sig =
        (target.wires wire).sig)
    (contextAction : ∀ {sig} (value : Var targetContext.sigs sig),
      WireContext.origin source sourceContext.ids (rho value) =
        wireOrigin
          (WireContext.origin target targetContext.ids value))
    {targetNode : target.NodeId}
    {sourceNode : source.NodeId}
    {port : CPort}
    {expected : Sig}
    (ownerImage : ∀ (sourceWire : source.WireId),
      source.endpointOwner? ⟨sourceNode, port⟩ = some sourceWire →
      sourceWire ∈ sourceContext.ids →
        ∃ targetWire : target.WireId,
          target.endpointOwner? ⟨targetNode, port⟩ = some targetWire ∧
          wireOrigin targetWire = sourceWire ∧
          targetWire ∈ targetContext.ids)
    {sourceResolved : Var sourceContext.sigs expected}
    (sourceEquation :
      resolvePort? source sourceContext sourceNode port expected =
        some sourceResolved) :
    ∃ targetResolved : Var targetContext.sigs expected,
      resolvePort? target targetContext targetNode port expected =
          some targetResolved ∧
        sourceResolved = rho targetResolved := by
  unfold resolvePort? at sourceEquation
  cases sourceOwner :
      source.endpointOwner? ⟨sourceNode, port⟩ with
  | none =>
      simp [sourceOwner] at sourceEquation
  | some sourceWire =>
      have sourceExpected :
          resolveExpected? source sourceContext sourceWire expected =
            some sourceResolved := by
        simpa [sourceOwner] using sourceEquation
      have sourceMember :=
        resolveExpected?_sound_member source sourceContext sourceWire
          expected sourceExpected
      obtain ⟨targetWire, targetOwner, ownerAction, targetMember⟩ :=
        ownerImage sourceWire sourceOwner sourceMember
      have sourceSignature :
          (source.wires sourceWire).sig = expected :=
        resolveExpected?_sound_signature source sourceContext
          sourceWire expected sourceExpected
      have targetSignature :
          (target.wires targetWire).sig = expected := by
        rw [← wireSignature targetWire, ownerAction, sourceSignature]
      obtain ⟨targetWireVar, targetWireEquation⟩ :=
        resolveWire?_complete target targetContext targetWire targetMember
      let targetResolved : Var targetContext.sigs expected :=
        targetSignature ▸ targetWireVar
      have targetExpected :
          resolveExpected? target targetContext targetWire expected =
            some targetResolved := by
        unfold resolveExpected?
        rw [dif_pos targetSignature, targetWireEquation]
        simp [targetResolved]
      have targetOrigin :
          WireContext.origin target targetContext.ids targetResolved =
            targetWire :=
        origin_of_resolvedExpected target targetContext targetWire expected
          targetExpected
      have mappedOrigin := contextAction targetResolved
      rw [targetOrigin, ownerAction] at mappedOrigin
      have sourceReResolved :=
        resolveExpected?_origin source sourceContext
          sourceContextNodup (rho targetResolved)
      rw [mappedOrigin] at sourceReResolved
      have resolvedEquality : sourceResolved = rho targetResolved :=
        Option.some.inj (sourceExpected.symm.trans sourceReResolved)
      refine ⟨targetResolved, ?_, resolvedEquality⟩
      simpa [resolvePort?, targetOwner] using targetExpected

private theorem resolveArgs?_reflect
    {definitions : List (List Sig)}
    {target source : ConcreteDiagram definitions.length}
    {targetContext : WireContext target}
    {sourceContext : WireContext source}
    (sourceContextNodup : sourceContext.ids.Nodup)
    (rho : WireRenaming targetContext.sigs sourceContext.sigs)
    (wireOrigin : target.WireId → source.WireId)
    (wireSignature : ∀ wire,
      (source.wires (wireOrigin wire)).sig =
        (target.wires wire).sig)
    (contextAction : ∀ {sig} (value : Var targetContext.sigs sig),
      WireContext.origin source sourceContext.ids (rho value) =
        wireOrigin
          (WireContext.origin target targetContext.ids value))
    {targetNode : target.NodeId}
    {sourceNode : source.NodeId}
    (ownerImage : ∀ (port : CPort),
      port ∈ source.requiredPorts sourceNode →
        ∀ (sourceWire : source.WireId),
          source.endpointOwner? ⟨sourceNode, port⟩ = some sourceWire →
          sourceWire ∈ sourceContext.ids →
            ∃ targetWire : target.WireId,
              target.endpointOwner? ⟨targetNode, port⟩ =
                  some targetWire ∧
                wireOrigin targetWire = sourceWire ∧
                targetWire ∈ targetContext.ids)
    (args : List Sig)
    (index : Nat)
    (sourceRequired : ∀ offset (_bound : offset < args.length),
      CPort.arg (index + offset) ∈
        source.requiredPorts sourceNode)
    {sourceResolved : Vars sourceContext.sigs args}
    (sourceEquation :
      resolveArgs? source sourceContext sourceNode args index =
        some sourceResolved) :
    ∃ targetResolved : Vars targetContext.sigs args,
      resolveArgs? target targetContext targetNode args index =
          some targetResolved ∧
        sourceResolved = targetResolved.rename rho := by
  induction args generalizing index with
  | nil =>
      have sourceEquality :
          (.nil : Vars sourceContext.sigs []) = sourceResolved :=
        Option.some.inj sourceEquation
      subst sourceResolved
      exact ⟨.nil, rfl, rfl⟩
  | cons sig rest induction =>
      cases sourceHeadEquation :
          resolvePort? source sourceContext sourceNode
            (.arg index) sig with
      | none =>
          simp [resolveArgs?, sourceHeadEquation] at sourceEquation
      | some sourceHead =>
          cases sourceTailEquation :
              resolveArgs? source sourceContext sourceNode rest
                (index + 1) with
          | none =>
              simp [resolveArgs?, sourceHeadEquation,
                sourceTailEquation] at sourceEquation
          | some sourceTail =>
              have sourceEquality :
                  (Vars.cons sourceHead sourceTail :
                    Vars sourceContext.sigs (sig :: rest)) =
                    sourceResolved := by
                exact Option.some.inj (by
                  simpa [resolveArgs?, sourceHeadEquation,
                    sourceTailEquation] using sourceEquation)
              subst sourceResolved
              obtain
                  ⟨targetHead, targetHeadEquation, sourceHeadEquality⟩ :=
                resolvePort?_reflect sourceContextNodup rho
                  wireOrigin wireSignature contextAction
                  (ownerImage (.arg index)
                    (sourceRequired 0 (by simp)))
                  sourceHeadEquation
              obtain
                  ⟨targetTail, targetTailEquation, sourceTailEquality⟩ :=
                induction (index := index + 1)
                  (sourceResolved := sourceTail)
                  (fun offset bound => by
                    have required :=
                      sourceRequired (offset + 1) (by simp; omega)
                    simpa [Nat.add_assoc, Nat.add_comm,
                      Nat.add_left_comm] using required)
                  sourceTailEquation
              refine ⟨.cons targetHead targetTail, ?_, ?_⟩
              · have targetHeadEquation' :
                    resolvePort? target targetContext targetNode
                        (.arg index) sig =
                      some targetHead := by
                    simpa using targetHeadEquation
                simp [resolveArgs?, targetHeadEquation',
                  targetTailEquation]
              · simp [Vars.rename, sourceHeadEquality,
                  sourceTailEquality]

private theorem resolveIdentityPorts?_reflect
    {definitions : List (List Sig)}
    {target source : ConcreteDiagram definitions.length}
    {targetContext : WireContext target}
    {sourceContext : WireContext source}
    (sourceContextNodup : sourceContext.ids.Nodup)
    (rho : WireRenaming targetContext.sigs sourceContext.sigs)
    (wireOrigin : target.WireId → source.WireId)
    (wireSignature : ∀ wire,
      (source.wires (wireOrigin wire)).sig =
        (target.wires wire).sig)
    (contextAction : ∀ {sig} (value : Var targetContext.sigs sig),
      WireContext.origin source sourceContext.ids (rho value) =
        wireOrigin
          (WireContext.origin target targetContext.ids value))
    {targetNode : target.NodeId}
    {sourceNode : source.NodeId}
    (ownerImage : ∀ (port : CPort),
      port ∈ source.requiredPorts sourceNode →
        ∀ (sourceWire : source.WireId),
          source.endpointOwner? ⟨sourceNode, port⟩ = some sourceWire →
          sourceWire ∈ sourceContext.ids →
            ∃ targetWire : target.WireId,
              target.endpointOwner? ⟨targetNode, port⟩ =
                  some targetWire ∧
                wireOrigin targetWire = sourceWire ∧
                targetWire ∈ targetContext.ids)
    (sig : Sig)
    (remaining index : Nat)
    (sourceRequired : ∀ offset (_bound : offset < remaining),
      CPort.identity (index + offset) ∈
        source.requiredPorts sourceNode)
    {sourceResolved : { ports : List (Var sourceContext.sigs sig) //
      ports.length = remaining }}
    (sourceEquation :
      resolveIdentityPorts? source sourceContext sourceNode sig
          remaining index =
        some sourceResolved) :
    ∃ targetResolved :
        { ports : List (Var targetContext.sigs sig) //
          ports.length = remaining },
      resolveIdentityPorts? target targetContext targetNode sig
          remaining index =
          some targetResolved ∧
        sourceResolved.val =
          targetResolved.val.map (rho (sig := sig)) := by
  induction remaining generalizing index with
  | zero =>
      have sourceEmpty : sourceResolved.val = [] :=
        List.length_eq_zero_iff.mp sourceResolved.property
      refine ⟨⟨[], rfl⟩, rfl, ?_⟩
      simp [sourceEmpty]
  | succ remaining induction =>
      cases sourceHeadEquation :
          resolvePort? source sourceContext sourceNode
            (.identity index) sig with
      | none =>
          simp [resolveIdentityPorts?, sourceHeadEquation]
            at sourceEquation
      | some sourceHead =>
          cases sourceTailEquation :
              resolveIdentityPorts? source sourceContext sourceNode sig
                remaining (index + 1) with
          | none =>
              simp [resolveIdentityPorts?, sourceHeadEquation,
                sourceTailEquation] at sourceEquation
          | some sourceTail =>
              have sourceEquality :
                  (⟨sourceHead :: sourceTail.val,
                    by simp [sourceTail.property]⟩ :
                    { ports : List (Var sourceContext.sigs sig) //
                      ports.length = remaining + 1 }) =
                    sourceResolved := by
                exact Option.some.inj (by
                  simpa [resolveIdentityPorts?, sourceHeadEquation,
                    sourceTailEquation] using sourceEquation)
              subst sourceResolved
              obtain
                  ⟨targetHead, targetHeadEquation, sourceHeadEquality⟩ :=
                resolvePort?_reflect sourceContextNodup rho
                  wireOrigin wireSignature contextAction
                  (ownerImage (.identity index)
                    (sourceRequired 0 (by omega)))
                  sourceHeadEquation
              obtain
                  ⟨targetTail, targetTailEquation, sourceTailEquality⟩ :=
                induction (index := index + 1)
                  (sourceResolved := sourceTail)
                  (fun offset bound => by
                    have required :=
                      sourceRequired (offset + 1) (by omega)
                    simpa [Nat.add_assoc, Nat.add_comm,
                      Nat.add_left_comm] using required)
                  sourceTailEquation
              let targetResolved :
                  { ports : List (Var targetContext.sigs sig) //
                    ports.length = remaining + 1 } :=
                ⟨targetHead :: targetTail.val,
                  by simp [targetTail.property]⟩
              refine ⟨targetResolved, ?_, ?_⟩
              · simp [resolveIdentityPorts?, targetHeadEquation,
                  targetTailEquation, targetResolved]
              · simp [targetResolved, sourceHeadEquality,
                  sourceTailEquality]

private theorem compileNode?_reflect
    {definitions : List (List Sig)}
    {target source : ConcreteDiagram definitions.length}
    {targetContext : WireContext target}
    {sourceContext : WireContext source}
    (sourceContextNodup : sourceContext.ids.Nodup)
    (rho : WireRenaming targetContext.sigs sourceContext.sigs)
    (wireOrigin : target.WireId → source.WireId)
    (wireSignature : ∀ wire,
      (source.wires (wireOrigin wire)).sig =
        (target.wires wire).sig)
    (contextAction : ∀ {sig} (value : Var targetContext.sigs sig),
      WireContext.origin source sourceContext.ids (rho value) =
        wireOrigin
          (WireContext.origin target targetContext.ids value))
    (regionOrigin : target.RegionId → source.RegionId)
    {targetNode : target.NodeId}
    {sourceNode : source.NodeId}
    (nodeShape :
      source.nodes sourceNode =
        match target.nodes targetNode with
        | .atom region args =>
            .atom (regionOrigin region) args
        | .ref region definition args =>
            .ref (regionOrigin region) definition args
        | .identity region sig arity =>
            .identity (regionOrigin region) sig arity)
    (ownerImage : ∀ (port : CPort),
      port ∈ source.requiredPorts sourceNode →
        ∀ (sourceWire : source.WireId),
          source.endpointOwner? ⟨sourceNode, port⟩ = some sourceWire →
          sourceWire ∈ sourceContext.ids →
            ∃ targetWire : target.WireId,
              target.endpointOwner? ⟨targetNode, port⟩ =
                  some targetWire ∧
                wireOrigin targetWire = sourceWire ∧
                targetWire ∈ targetContext.ids)
    {sourceItem : Item definitions sourceContext.sigs}
    (sourceCompiled :
      compileNode? definitions source sourceContext sourceNode =
        some sourceItem) :
    ∃ targetItem : Item definitions targetContext.sigs,
      compileNode? definitions target targetContext targetNode =
          some targetItem ∧
        sourceItem = targetItem.renameWires rho := by
  cases targetNodeData : target.nodes targetNode with
  | atom targetRegion args =>
      have sourceNodeData :
          source.nodes sourceNode =
            .atom (regionOrigin targetRegion) args := by
        rw [nodeShape, targetNodeData]
      cases sourceHeadEquation :
          resolvePort? source sourceContext sourceNode .head
            (.rel args) with
      | none =>
          simp [compileNode?_equation, sourceNodeData, sourceHeadEquation]
            at sourceCompiled
      | some sourceHead =>
          cases sourceArgsEquation :
              resolveArgs? source sourceContext sourceNode args 0 with
          | none =>
              simp [compileNode?_equation, sourceNodeData,
                sourceHeadEquation, sourceArgsEquation]
                at sourceCompiled
          | some sourceArgs =>
              have sourceItemEquality :
                  (Item.atom sourceHead sourceArgs :
                    Item definitions sourceContext.sigs) =
                    sourceItem := by
                exact Option.some.inj (by
                  simpa [compileNode?_equation, sourceNodeData,
                    sourceHeadEquation, sourceArgsEquation] using
                      sourceCompiled)
              subst sourceItem
              obtain
                  ⟨targetHead, targetHeadEquation,
                    sourceHeadEquality⟩ :=
                resolvePort?_reflect sourceContextNodup rho
                  wireOrigin wireSignature contextAction
                  (ownerImage .head (by
                    simp [ConcreteDiagram.requiredPorts,
                      sourceNodeData]))
                  sourceHeadEquation
              obtain
                  ⟨targetArgs, targetArgsEquation,
                    sourceArgsEquality⟩ :=
                resolveArgs?_reflect sourceContextNodup rho
                  wireOrigin wireSignature contextAction
                  ownerImage args 0
                  (by
                    intro offset bound
                    simp [ConcreteDiagram.requiredPorts,
                      sourceNodeData, bound])
                  sourceArgsEquation
              refine ⟨.atom targetHead targetArgs, ?_, ?_⟩
              · simp [compileNode?_equation, targetNodeData,
                  targetHeadEquation, targetArgsEquation]
              · simp [Item.renameWires, sourceHeadEquality,
                  sourceArgsEquality]
  | ref targetRegion definition args =>
      have sourceNodeData :
          source.nodes sourceNode =
            .ref (regionOrigin targetRegion) definition args := by
        rw [nodeShape, targetNodeData]
      simp only [compileNode?_equation, sourceNodeData] at sourceCompiled
      split at sourceCompiled
      · rename_i signature
        cases sourceArgsEquation :
            resolveArgs? source sourceContext sourceNode args 0 with
        | none =>
            simp [sourceArgsEquation] at sourceCompiled
        | some sourceArgs =>
            let reference : DefVar definitions args :=
              signature ▸ definitionVarAt definitions definition
            have sourceItemEquality :
                (Item.named reference sourceArgs :
                  Item definitions sourceContext.sigs) =
                  sourceItem := by
              exact Option.some.inj (by
                simpa [sourceArgsEquation, reference] using
                  sourceCompiled)
            subst sourceItem
            obtain
                ⟨targetArgs, targetArgsEquation,
                  sourceArgsEquality⟩ :=
              resolveArgs?_reflect sourceContextNodup rho
                wireOrigin wireSignature contextAction
                ownerImage args 0
                (by
                  intro offset bound
                  simp [ConcreteDiagram.requiredPorts,
                    sourceNodeData, bound])
                sourceArgsEquation
            refine ⟨.named reference targetArgs, ?_, ?_⟩
            · simp only [compileNode?_equation, targetNodeData]
              split
              · simp [targetArgsEquation, reference]
              · contradiction
            · simp [Item.renameWires, sourceArgsEquality]
      · simp at sourceCompiled
  | identity targetRegion sig arity =>
      have sourceNodeData :
          source.nodes sourceNode =
            .identity (regionOrigin targetRegion) sig arity := by
        rw [nodeShape, targetNodeData]
      simp only [compileNode?_equation, sourceNodeData] at sourceCompiled
      split at sourceCompiled
      · rename_i arityWitness
        cases sourcePortsEquation :
            resolveIdentityPorts? source sourceContext sourceNode
              sig arity 0 with
        | none =>
            simp [sourcePortsEquation] at sourceCompiled
        | some sourcePorts =>
            have sourceItemEquality :
                (Item.identity sig sourcePorts.val (by
                  simpa [sourcePorts.property] using arityWitness) :
                  Item definitions sourceContext.sigs) =
                  sourceItem := by
              exact Option.some.inj (by
                simpa [sourcePortsEquation] using sourceCompiled)
            subst sourceItem
            obtain
                ⟨targetPorts, targetPortsEquation,
                  sourcePortsEquality⟩ :=
              resolveIdentityPorts?_reflect sourceContextNodup rho
                wireOrigin wireSignature contextAction ownerImage
                sig arity 0
                (by
                  intro offset bound
                  simp [ConcreteDiagram.requiredPorts,
                    sourceNodeData, bound])
                sourcePortsEquation
            refine
              ⟨.identity sig targetPorts.val (by
                simpa [targetPorts.property] using arityWitness),
                ?_, ?_⟩
            · simp [compileNode?_equation, targetNodeData, arityWitness,
                targetPortsEquation]
            · simp [Item.renameWires, sourcePortsEquality]
      · simp at sourceCompiled

/--
Reflect an accepted singleton compilation through an exact target-to-source
context embedding.  Endpoint-owner images are required only for ports used by
the copied node shape.
-/
theorem compileNodes?_singleton_reflect
    {definitions : List (List Sig)}
    {target source : ConcreteDiagram definitions.length}
    (_sourceWellFormed : source.WellFormed definitions)
    {targetContext : WireContext target}
    {sourceContext : WireContext source}
    (sourceContextNodup : sourceContext.ids.Nodup)
    (rho : WireRenaming targetContext.sigs sourceContext.sigs)
    (wireOrigin : target.WireId → source.WireId)
    (wireSignature : ∀ wire,
      (source.wires (wireOrigin wire)).sig =
        (target.wires wire).sig)
    (contextAction : ∀ {sig} (value : Var targetContext.sigs sig),
      WireContext.origin source sourceContext.ids (rho value) =
        wireOrigin
          (WireContext.origin target targetContext.ids value))
    (regionOrigin : target.RegionId → source.RegionId)
    (targetNode : target.NodeId)
    (sourceNode : source.NodeId)
    (nodeShape :
      source.nodes sourceNode =
        match target.nodes targetNode with
        | .atom region args =>
            .atom (regionOrigin region) args
        | .ref region definition args =>
            .ref (regionOrigin region) definition args
        | .identity region sig arity =>
            .identity (regionOrigin region) sig arity)
    (ownerImage : ∀ (port : CPort),
      port ∈ source.requiredPorts sourceNode →
        ∀ (sourceWire : source.WireId),
          source.endpointOwner? ⟨sourceNode, port⟩ = some sourceWire →
          sourceWire ∈ sourceContext.ids →
            ∃ targetWire : target.WireId,
              target.endpointOwner? ⟨targetNode, port⟩ =
                  some targetWire ∧
                wireOrigin targetWire = sourceWire ∧
                targetWire ∈ targetContext.ids)
    {sourceItems : ItemSeq definitions sourceContext.sigs}
    (sourceCompiled :
      compileNodes? definitions source sourceContext [sourceNode] =
        some sourceItems) :
    ∃ targetItems : ItemSeq definitions targetContext.sigs,
      compileNodes? definitions target targetContext [targetNode] =
          some targetItems ∧
        sourceItems = targetItems.renameWires rho := by
  cases sourceNodeEquation :
      compileNode? definitions source sourceContext sourceNode with
  | none =>
      simp [compileNodes?_equation, sourceNodeEquation] at sourceCompiled
  | some sourceItem =>
      have sourceItemsEquality :
          (ItemSeq.cons sourceItem .nil :
            ItemSeq definitions sourceContext.sigs) =
            sourceItems := by
        exact Option.some.inj (by
          simpa [compileNodes?_equation, sourceNodeEquation] using
            sourceCompiled)
      subst sourceItems
      obtain ⟨targetItem, targetNodeEquation, sourceItemEquality⟩ :=
        compileNode?_reflect sourceContextNodup rho wireOrigin
          wireSignature contextAction regionOrigin nodeShape ownerImage
          sourceNodeEquation
      refine ⟨.cons targetItem .nil, ?_, ?_⟩
      · simp [compileNodes?_equation, targetNodeEquation]
      · simp [sourceItemEquality, ItemSeq.renameWires]

private def binaryIdentityTemplate (definitionCount : Nat) (sig : Sig) :
    ConcreteDiagram definitionCount where
  regionCount := 1
  nodeCount := 1
  wireCount := 2
  root := ⟨0, by omega⟩
  regions := fun _ => .sheet
  nodes := fun _ => .identity ⟨0, by omega⟩ sig 2
  wires
    | ⟨0, _⟩ =>
        { sig := sig
          scope := ⟨0, by omega⟩
          endpoints := [⟨⟨0, by omega⟩, .identity 0⟩] }
    | ⟨1, _⟩ =>
        { sig := sig
          scope := ⟨0, by omega⟩
          endpoints := [⟨⟨0, by omega⟩, .identity 1⟩] }
private def binaryIdentityTemplateContext
    (definitionCount : Nat) (sig : Sig) :
    WireContext (binaryIdentityTemplate definitionCount sig) :=
  ⟨[⟨0, by simp [binaryIdentityTemplate]⟩,
      ⟨1, by simp [binaryIdentityTemplate]⟩]⟩
private theorem binaryIdentityTemplateContext_sigs
    (definitionCount : Nat) (sig : Sig) :
    (binaryIdentityTemplateContext definitionCount sig).sigs =
      [sig, sig] := by
  rfl
private def binaryIdentityRenaming
    {definitions : List (List Sig)}
    {diagram : ConcreteDiagram definitions.length}
    {context : WireContext diagram}
    {sig : Sig}
    (first second : Var context.sigs sig) :
    WireRenaming [sig, sig] context.sigs :=
  fun {_} value =>
    match value with
    | .here => first
    | .there .here => second
private def binaryIdentityTemplateWireMap
    {definitions : List (List Sig)}
    {diagram : ConcreteDiagram definitions.length}
    (sig : Sig) (first second : diagram.WireId) :
    (binaryIdentityTemplate definitions.length sig).WireId →
      diagram.WireId
  | ⟨0, _⟩ => first
  | ⟨1, _⟩ => second
/--
Compile a binary concrete identity to the exact intrinsic binary identity
between the two supplied context variables. The executable compiler remains
the sole constructor of the result; the premises expose only checked shape,
incidence, and concrete-origin evidence.
-/
theorem compileNodes?_binaryIdentity_singleton
    {definitions : List (List Sig)}
    {diagram : ConcreteDiagram definitions.length}
    (wellFormed : diagram.WellFormed definitions)
    {context : WireContext diagram}
    (contextNodup : context.ids.Nodup)
    {sig : Sig}
    (first second : Var context.sigs sig)
    (firstWire secondWire : diagram.WireId)
    (firstOrigin : WireContext.origin diagram context.ids first = firstWire)
    (secondOrigin : WireContext.origin diagram context.ids second = secondWire)
    (region : diagram.RegionId)
    (node : diagram.NodeId)
    (nodeShape : diagram.nodes node = .identity region sig 2)
    (firstIncident : (⟨node, .identity 0⟩ :
      CEndpoint diagram.nodeCount) ∈ (diagram.wires firstWire).endpoints)
    (secondIncident : (⟨node, .identity 1⟩ :
      CEndpoint diagram.nodeCount) ∈ (diagram.wires secondWire).endpoints) :
    compileNodes? definitions diagram context [node] =
      some
        (.cons (Item.binaryIdentity sig first second) .nil) := by
  let template := binaryIdentityTemplate definitions.length sig
  let templateContext :=
    binaryIdentityTemplateContext definitions.length sig
  let rho : WireRenaming templateContext.sigs context.sigs :=
    fun {_} value =>
      binaryIdentityRenaming
        (definitions := definitions) (diagram := diagram)
        (context := context) (sig := sig) first second
        (binaryIdentityTemplateContext_sigs definitions.length sig ▸ value)
  let wireMap :=
    binaryIdentityTemplateWireMap
      (definitions := definitions) sig firstWire secondWire
  have firstSignature : (diagram.wires firstWire).sig = sig := by
    rw [← firstOrigin]
    exact WireContext.origin_signature diagram context.ids first
  have secondSignature : (diagram.wires secondWire).sig = sig := by
    rw [← secondOrigin]
    exact WireContext.origin_signature diagram context.ids second
  have sourceOwnerFirst : template.endpointOwner?
      ⟨⟨0, by simp [template, binaryIdentityTemplate]⟩, .identity 0⟩ =
        some ⟨0, by simp [template, binaryIdentityTemplate]⟩ := by
    unfold ConcreteDiagram.endpointOwner?
    change
      Option.map Prod.fst
          ([((⟨0, by omega⟩ : Fin 2),
              (⟨⟨0, by omega⟩, .identity 0⟩ : CEndpoint 1)),
            ((⟨1, by omega⟩ : Fin 2),
              (⟨⟨0, by omega⟩, .identity 1⟩ : CEndpoint 1))].find?
            (fun occurrence =>
              occurrence.2 ==
                (⟨⟨0, by omega⟩, .identity 0⟩ : CEndpoint 1))) =
        some (⟨0, by omega⟩ : Fin 2)
    native_decide
  have sourceOwnerSecond : template.endpointOwner?
      ⟨⟨0, by simp [template, binaryIdentityTemplate]⟩, .identity 1⟩ =
        some ⟨1, by simp [template, binaryIdentityTemplate]⟩ := by
    unfold ConcreteDiagram.endpointOwner?
    change
      Option.map Prod.fst
          ([((⟨0, by omega⟩ : Fin 2),
              (⟨⟨0, by omega⟩, .identity 0⟩ : CEndpoint 1)),
            ((⟨1, by omega⟩ : Fin 2),
              (⟨⟨0, by omega⟩, .identity 1⟩ : CEndpoint 1))].find?
            (fun occurrence =>
              occurrence.2 ==
                (⟨⟨0, by omega⟩, .identity 1⟩ : CEndpoint 1))) =
        some (⟨1, by omega⟩ : Fin 2)
    native_decide
  have sourceResolveFirst : resolvePort? template templateContext
      ⟨0, by simp [template, binaryIdentityTemplate]⟩ (.identity 0) sig =
        some (.here : Var templateContext.sigs sig) := by
    unfold resolvePort?
    rw [sourceOwnerFirst]
    simp [resolveExpected?, resolveWire?, resolveWireIn?,
      template, templateContext, binaryIdentityTemplate,
      binaryIdentityTemplateContext]
  have sourceResolveSecond : resolvePort? template templateContext
      ⟨0, by simp [template, binaryIdentityTemplate]⟩ (.identity 1) sig =
        some (.there .here : Var templateContext.sigs sig) := by
    unfold resolvePort?
    rw [sourceOwnerSecond]
    simp [resolveExpected?, resolveWire?, resolveWireIn?,
      template, templateContext, binaryIdentityTemplate,
      binaryIdentityTemplateContext]
  have sourceNodeCompiled : compileNode? definitions template templateContext
      ⟨0, by simp [template, binaryIdentityTemplate]⟩ =
        some (Item.binaryIdentity sig .here (.there .here)) := by
    rw [compileNode?_equation]
    rw [show
      template.nodes
          ⟨0, by simp [template, binaryIdentityTemplate]⟩ =
        .identity ⟨0, by simp [template, binaryIdentityTemplate]⟩ sig 2 by
          rfl]
    simp only [Nat.reduceLeDiff, ↓reduceDIte]
    change
      (resolveIdentityPorts? template templateContext
          ⟨0, by simp [template, binaryIdentityTemplate]⟩ sig 2 0).bind
          (fun ports =>
            some (.identity sig ports.val (by
              exact Nat.le_of_eq ports.property.symm))) =
        some (Item.binaryIdentity sig .here (.there .here))
    simp only [resolveIdentityPorts?, sourceResolveFirst,
      sourceResolveSecond, Option.bind_some]
    unfold Item.binaryIdentity
    congr
  have sourceCompiled : compileNodes? definitions template templateContext
      [⟨0, by simp [template, binaryIdentityTemplate]⟩] =
        some
          (.cons (Item.binaryIdentity sig .here (.there .here)) .nil) := by
    simp [compileNodes?_equation, sourceNodeCompiled]
    rfl
  obtain ⟨targetItems, targetCompiled, targetEquality⟩ :=
    compileNodes?_singleton_natural wellFormed contextNodup rho wireMap
      (by
        intro wire
        rcases wire with ⟨value, bound⟩
        have valueCases : value = 0 ∨ value = 1 := by
          simp [template, binaryIdentityTemplate] at bound
          omega
        rcases valueCases with rfl | rfl <;>
          simp [wireMap, binaryIdentityTemplateWireMap, template,
            binaryIdentityTemplate, firstSignature, secondSignature])
      (by
        intro mappedSig value
        change Var [sig, sig] mappedSig at value
        cases value with
        | here =>
            simpa [rho, binaryIdentityRenaming, wireMap,
              binaryIdentityTemplateWireMap, templateContext,
              binaryIdentityTemplateContext, template,
              binaryIdentityTemplate] using firstOrigin
        | there tail =>
            cases tail with
            | here =>
                simpa [rho, binaryIdentityRenaming, wireMap,
                  binaryIdentityTemplateWireMap, templateContext,
                  binaryIdentityTemplateContext, template,
                  binaryIdentityTemplate] using secondOrigin
            | there impossible => exact nomatch impossible)
      (fun _ => region)
      ⟨0, by simp [template, binaryIdentityTemplate]⟩ node
      (by
        simpa [template, binaryIdentityTemplate] using nodeShape)
      (by
        intro port wire incident
        rcases wire with ⟨value, bound⟩
        have valueCases : value = 0 ∨ value = 1 := by
          simp [template, binaryIdentityTemplate] at bound
          omega
        rcases valueCases with rfl | rfl
        · have portEquality : port = .identity 0 := by
            have endpointEquality :
                (⟨⟨0, by simp [template, binaryIdentityTemplate]⟩, port⟩ :
                    CEndpoint template.nodeCount) =
                  ⟨⟨0, by simp [template, binaryIdentityTemplate]⟩,
                    .identity 0⟩ := by
              change
                (⟨⟨0, by omega⟩, port⟩ : CEndpoint 1) ∈
                  [(⟨⟨0, by omega⟩, .identity 0⟩ : CEndpoint 1)]
                at incident
              exact List.mem_singleton.mp incident
            exact congrArg CEndpoint.port endpointEquality
          subst port
          simpa [wireMap, binaryIdentityTemplateWireMap] using firstIncident
        · have portEquality : port = .identity 1 := by
            have endpointEquality :
                (⟨⟨0, by simp [template, binaryIdentityTemplate]⟩, port⟩ :
                    CEndpoint template.nodeCount) =
                  ⟨⟨0, by simp [template, binaryIdentityTemplate]⟩,
                    .identity 1⟩ := by
              change
                (⟨⟨0, by omega⟩, port⟩ : CEndpoint 1) ∈
                  [(⟨⟨0, by omega⟩, .identity 1⟩ : CEndpoint 1)]
                at incident
              exact List.mem_singleton.mp incident
            exact congrArg CEndpoint.port endpointEquality
          subst port
          simpa [wireMap, binaryIdentityTemplateWireMap] using secondIncident)
      sourceCompiled
  rw [targetCompiled]
  congr 1

/-- A compiled checked identity's variable origins are exactly its incident wires. -/
theorem compileNodes?_identity_origins
    {definitions : List (List Sig)} (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions) (context : WireContext diagram)
    (node : diagram.NodeId) {region : diagram.RegionId} {sig : Sig} {arity : Nat}
    (nodeData : diagram.nodes node = .identity region sig arity) {items : ItemSeq definitions context.sigs}
    (compiled : compileNodes? definitions diagram context [node] = some items) :
    ∃ (ports : List (Var context.sigs sig)) (two : 2 ≤ ports.length),
      items = .cons (.identity sig ports two) .nil ∧
      ∀ wire, wire ∈ diagram.identityIncidentWires node ↔
        ∃ resolvedVar ∈ ports, WireContext.origin diagram context.ids resolvedVar = wire := by
  simp only [compileNodes?_equation, compileNode?_equation, nodeData] at compiled
  split at compiled
  · rename_i arityWitness
    cases portsEquation :
        resolveIdentityPorts? diagram context node sig arity 0 with
    | none => simp [portsEquation] at compiled
    | some ports =>
        have two : 2 ≤ ports.val.length := by
          simpa [ports.property] using arityWitness
        refine ⟨ports.val, two,
          (Option.some.inj (by simpa [portsEquation] using compiled)).symm, ?_⟩
        intro wire
        constructor
        · intro incident
          have ownerMember :=
            (ConcreteDiagram.mem_identityIncidentWires_iff_mem_identityOwners definitions
              diagram wellFormed node region sig arity nodeData wire).mp incident
          rcases List.mem_filterMap.mp ownerMember with ⟨index, bound, owner⟩
          obtain ⟨resolvedVar, resolved, member⟩ :=
            resolveIdentityPorts?_at diagram context node sig arity 0 ports
              portsEquation index (by simpa using bound)
          refine ⟨resolvedVar, member, ?_⟩
          exact origin_of_resolvedExpected diagram context wire sig
            (by simpa [resolvePort?, owner] using resolved)
        · rintro ⟨resolvedVar, member, origin⟩
          obtain ⟨index, _, resolved⟩ := resolveIdentityPorts?_mem diagram
            context node sig arity 0 ports portsEquation resolvedVar member
          cases owner : diagram.endpointOwner? ⟨node, .identity index⟩ with
          | none => simp [resolvePort?, owner] at resolved
          | some ownerWire =>
              have expected : resolveExpected? diagram context ownerWire sig =
                  some resolvedVar := by simpa [resolvePort?, owner] using resolved
              rw [origin_of_resolvedExpected diagram context ownerWire sig
                expected]
                at origin
              subst wire
              exact (ConcreteDiagram.mem_identityIncidentWires diagram node
                ownerWire).mpr ⟨_, ConcreteDiagram.endpointOwner?_incident
                  diagram _ _ owner, rfl⟩
  · simp at compiled

/--
A compiled atom singleton retains its exact typed tuple and concrete endpoint
origins. The receipt exposes observations of the accepted compilation only.
-/
theorem compileNodes?_atom_shape
    {definitions : List (List Sig)}
    (diagram : ConcreteDiagram definitions.length) (context : WireContext diagram)
    (node : diagram.NodeId) {region : diagram.RegionId} {args : List Sig}
    (nodeData : diagram.nodes node = .atom region args)
    {items : ItemSeq definitions context.sigs}
    (compiled : compileNodes? definitions diagram context [node] = some items) :
    ∃ head : Var context.sigs (.rel args), ∃ arguments : Vars context.sigs args,
      items = .cons (.atom head arguments) .nil ∧
        diagram.endpointOwner? ⟨node, .head⟩ =
          some (WireContext.origin diagram context.ids head) ∧
        ArgumentOrigins diagram context node 0 arguments := by
  have portOrigin :
      ∀ (port : CPort) (expected : Sig)
        (value : Var context.sigs expected),
        resolvePort? diagram context node port expected = some value →
          diagram.endpointOwner? ⟨node, port⟩ =
            some (WireContext.origin diagram context.ids value) := by
    intro port expected value resolved
    unfold resolvePort? at resolved
    cases owner : diagram.endpointOwner? ⟨node, port⟩ with
    | none => simp [owner] at resolved
    | some wire =>
        simp only [owner, Option.bind_some] at resolved
        rw [← origin_of_resolvedExpected diagram context wire expected
          resolved]
  have argsOrigins :
      ∀ (remaining : List Sig) (index : Nat)
        (values : Vars context.sigs remaining),
        resolveArgs? diagram context node remaining index = some values →
          ArgumentOrigins diagram context node index values := by
    intro remaining
    induction remaining with
    | nil =>
        intro index values resolved
        cases values
        trivial
    | cons sig rest induction =>
        intro index values resolved
        cases headEquation :
            resolvePort? diagram context node (.arg index) sig with
        | none => simp [resolveArgs?, headEquation] at resolved
        | some head =>
            cases tailEquation :
                resolveArgs? diagram context node rest (index + 1) with
            | none =>
                simp [resolveArgs?, headEquation, tailEquation] at resolved
            | some tail =>
                have valuesExact : Vars.cons head tail = values :=
                  Option.some.inj (by
                    simpa [resolveArgs?, headEquation, tailEquation] using
                      resolved)
                subst values
                exact ⟨portOrigin _ _ _ headEquation,
                  induction (index + 1) tail tailEquation⟩
  simp only [compileNodes?_equation, compileNode?_equation, nodeData] at compiled
  cases headEquation : resolvePort? diagram context node .head (.rel args) with
  | none => simp [headEquation] at compiled
  | some head =>
      cases argumentsEquation : resolveArgs? diagram context node args 0 with
      | none => simp [headEquation, argumentsEquation] at compiled
      | some arguments =>
          exact ⟨head, arguments,
            (Option.some.inj
              (by simpa [headEquation, argumentsEquation] using compiled)).symm,
            portOrigin _ _ _ headEquation,
            argsOrigins args 0 arguments argumentsEquation⟩

end ConcreteElaboration

end VisualProof
