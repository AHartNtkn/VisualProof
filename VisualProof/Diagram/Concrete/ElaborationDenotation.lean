import VisualProof.Diagram.Concrete.ElaborationTransport
namespace VisualProof
universe u

namespace ConcreteElaboration

open Internal
def EnvironmentsCorrespond
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (leftContext : WireContext left)
    (rightContext : WireContext right)
    (leftEnv : Env pre leftContext.sigs)
    (rightEnv : Env pre rightContext.sigs) : Prop :=
  ∀ (wire : left.WireId) (expected : Sig)
    (leftVar : Var leftContext.sigs expected)
    (rightVar : Var rightContext.sigs expected),
    resolveExpected? left leftContext wire expected = some leftVar →
      resolveExpected? right rightContext (iso.wires wire) expected =
        some rightVar →
      leftEnv expected leftVar = rightEnv expected rightVar

private theorem resolveExpected?_pair
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    (wire : left.WireId) (expected : Sig)
    (member : wire ∈ leftContext.ids)
    (signature : (left.wires wire).sig = expected) :
    ∃ leftVar rightVar,
      resolveExpected? left leftContext wire expected = some leftVar ∧
        resolveExpected? right rightContext (iso.wires wire) expected =
          some rightVar := by
  obtain ⟨leftVar, leftResolved⟩ :=
    resolveWire?_complete left leftContext wire member
  obtain ⟨rightVar, rightResolved⟩ :=
    resolveWire?_complete right rightContext (iso.wires wire)
      (contexts.forward wire member)
  have targetSignature :
      (right.wires (iso.wires wire)).sig = expected :=
    (iso.wire_signature wire).trans signature
  refine ⟨signature ▸ leftVar, targetSignature ▸ rightVar, ?_, ?_⟩
  · simp [resolveExpected?, signature, leftResolved]
  · simp [resolveExpected?, targetSignature, rightResolved]

private theorem sourceVar_for_target_exists
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    {sig : Sig} (rightVar : Var rightContext.sigs sig) :
    ∃ leftVar,
      resolveExpected? left leftContext
          (iso.wires.symm
            (WireContext.origin right rightContext.ids rightVar)) sig =
        some leftVar := by
  let targetWire := WireContext.origin right rightContext.ids rightVar
  let sourceWire := iso.wires.symm targetWire
  have targetMember : targetWire ∈ rightContext.ids :=
    origin_member right rightVar
  have sourceMember : sourceWire ∈ leftContext.ids :=
    contexts.backward targetWire targetMember
  have targetSignature : (right.wires targetWire).sig = sig :=
    WireContext.origin_signature right rightContext.ids rightVar
  have mappedWire : iso.wires sourceWire = targetWire :=
    iso.wires.right_inv targetWire
  have signatureTransport := iso.wire_signature sourceWire
  rw [mappedWire] at signatureTransport
  have sourceSignature : (left.wires sourceWire).sig = sig :=
    signatureTransport.symm.trans targetSignature
  obtain ⟨leftVar, _, leftResolved, _⟩ :=
    resolveExpected?_pair iso contexts sourceWire sig sourceMember
      sourceSignature
  exact ⟨leftVar, leftResolved⟩

private noncomputable def pullVar
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    {sig : Sig} (rightVar : Var rightContext.sigs sig) :
    Var leftContext.sigs sig :=
  Classical.choose (sourceVar_for_target_exists iso contexts rightVar)

private theorem pullVar_resolves
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    {sig : Sig} (rightVar : Var rightContext.sigs sig) :
    resolveExpected? left leftContext
        (iso.wires.symm
          (WireContext.origin right rightContext.ids rightVar)) sig =
      some (pullVar iso contexts rightVar) :=
  Classical.choose_spec (sourceVar_for_target_exists iso contexts rightVar)

noncomputable def pullEnvironment
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    {pre : PreModel.{u}}
    (leftEnv : Env pre leftContext.sigs) :
    Env pre rightContext.sigs :=
  fun sig rightVar => leftEnv sig (pullVar iso contexts rightVar)

theorem pull_environments_correspond
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    {pre : PreModel}
    (leftEnv : Env pre leftContext.sigs) :
    EnvironmentsCorrespond iso leftContext rightContext leftEnv
      (pullEnvironment iso contexts leftEnv) := by
  intro wire expected leftVar rightVar leftResolved rightResolved
  have targetWire :
      WireContext.origin right rightContext.ids rightVar = iso.wires wire :=
    origin_of_resolvedExpected right rightContext (iso.wires wire) expected
      rightResolved
  have sourceWire :
      iso.wires.symm
          (WireContext.origin right rightContext.ids rightVar) =
        wire := by
    rw [targetWire]
    exact iso.wires.left_inv wire
  have pulledResolved := pullVar_resolves iso contexts rightVar
  rw [sourceWire] at pulledResolved
  have variableEquality : pullVar iso contexts rightVar = leftVar :=
    Option.some.inj (pulledResolved.symm.trans leftResolved)
  simp only [pullEnvironment]
  exact congrArg (leftEnv expected) variableEquality.symm

theorem pullEnvironment_roundtrip
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    (leftNodup : leftContext.ids.Nodup)
    {pre : PreModel.{u}}
    (leftEnv : Env pre leftContext.sigs) :
    pullEnvironment iso.symm contexts.symm
        (pullEnvironment iso contexts leftEnv) = leftEnv := by
  funext sig leftVar
  let rightVar := pullVar iso.symm contexts.symm leftVar
  have rightResolved := pullVar_resolves iso.symm contexts.symm leftVar
  have rightWire :
      WireContext.origin right rightContext.ids rightVar =
        iso.wires (WireContext.origin left leftContext.ids leftVar) := by
    simpa [ConcreteIso.symm] using
      origin_of_resolvedExpected right rightContext
        (iso.wires (WireContext.origin left leftContext.ids leftVar)) sig
        rightResolved
  have forwardResolved := pullVar_resolves iso contexts rightVar
  have sourceWire :
      iso.wires.symm
          (WireContext.origin right rightContext.ids rightVar) =
        WireContext.origin left leftContext.ids leftVar := by
    rw [rightWire]
    exact iso.wires.left_inv _
  rw [sourceWire] at forwardResolved
  have originalResolved :=
    resolveExpected?_origin left leftContext leftNodup leftVar
  have variableEquality : pullVar iso contexts rightVar = leftVar :=
    Option.some.inj (forwardResolved.symm.trans originalResolved)
  simp only [pullEnvironment]
  exact congrArg (leftEnv sig) variableEquality

theorem pullEnvironment_extend_agrees
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    (region : left.RegionId)
    (leftExtendedNodup : (leftContext.extend region).ids.Nodup)
    {pre : PreModel}
    (leftOuter : Env pre leftContext.sigs)
    (leftValues : WireValues pre
      ((left.wiresAt region).map fun wire => (left.wires wire).sig))
    {sig : Sig} (rightVar : Var rightContext.sigs sig) :
    pullEnvironment iso (extend_contexts_correspond iso contexts region)
        (extendEnvironment left leftContext region leftValues leftOuter) sig
        (appendRightVar right
          (right.wiresAt (iso.regions region)) rightVar) =
      pullEnvironment iso contexts leftOuter sig rightVar := by
  let extendedContexts := extend_contexts_correspond iso contexts region
  let rightExtendedVar :=
    appendRightVar right (right.wiresAt (iso.regions region)) rightVar
  let leftOuterVar := pullVar iso contexts rightVar
  let leftExtendedVar :=
    appendRightVar left (left.wiresAt region) leftOuterVar
  have rightWire :
      WireContext.origin right
          (rightContext.extend (iso.regions region)).ids rightExtendedVar =
        WireContext.origin right rightContext.ids rightVar :=
    origin_appendRightVar right
      (right.wiresAt (iso.regions region)) rightVar
  have leftWire :
      WireContext.origin left (leftContext.extend region).ids leftExtendedVar =
        WireContext.origin left leftContext.ids leftOuterVar :=
    origin_appendRightVar left (left.wiresAt region) leftOuterVar
  have leftOuterResolved := pullVar_resolves iso contexts rightVar
  have leftOuterWire :
      WireContext.origin left leftContext.ids leftOuterVar =
        iso.wires.symm
          (WireContext.origin right rightContext.ids rightVar) :=
    origin_of_resolvedExpected left leftContext
      (iso.wires.symm
        (WireContext.origin right rightContext.ids rightVar))
      sig leftOuterResolved
  have correspondingWire :
      iso.wires.symm
          (WireContext.origin right
            (rightContext.extend (iso.regions region)).ids
            rightExtendedVar) =
        WireContext.origin left (leftContext.extend region).ids
          leftExtendedVar := by
    rw [rightWire, leftWire, leftOuterWire]
  have pulledResolved :=
    pullVar_resolves iso extendedContexts rightExtendedVar
  have appendedResolved :=
    resolveExpected?_origin left (leftContext.extend region)
      leftExtendedNodup leftExtendedVar
  have pulledResolved' :
      resolveExpected? left (leftContext.extend region)
          (WireContext.origin left (leftContext.extend region).ids
            leftExtendedVar) sig =
        some (pullVar iso extendedContexts rightExtendedVar) := by
    calc
      resolveExpected? left (leftContext.extend region)
          (WireContext.origin left (leftContext.extend region).ids
            leftExtendedVar) sig =
          resolveExpected? left (leftContext.extend region)
            (iso.wires.symm
              (WireContext.origin right
                (rightContext.extend (iso.regions region)).ids
                rightExtendedVar)) sig :=
        congrArg
          (fun wire =>
            resolveExpected? left (leftContext.extend region) wire sig)
          correspondingWire.symm
      _ = some (pullVar iso extendedContexts rightExtendedVar) :=
        pulledResolved
  have variableEquality :
      pullVar iso extendedContexts rightExtendedVar = leftExtendedVar :=
    Option.some.inj (pulledResolved'.symm.trans appendedResolved)
  simp only [pullEnvironment]
  rw [variableEquality]
  exact extendEnvironment_appendRightVar left leftContext region leftValues
    leftOuter leftOuterVar

theorem Internal.resolveExpected?_forward_value
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    {pre : PreModel}
    {leftEnv : Env pre leftContext.sigs}
    {rightEnv : Env pre rightContext.sigs}
    (envs : EnvironmentsCorrespond iso leftContext rightContext
      leftEnv rightEnv)
    (wire : left.WireId) (expected : Sig)
    (leftVar : Var leftContext.sigs expected)
    (leftResolved :
      resolveExpected? left leftContext wire expected = some leftVar) :
    ∃ rightVar,
      resolveExpected? right rightContext (iso.wires wire) expected =
        some rightVar ∧
      leftEnv expected leftVar = rightEnv expected rightVar := by
  have member :=
    resolveExpected?_sound_member left leftContext wire expected leftResolved
  have signature :=
    resolveExpected?_sound_signature left leftContext wire expected leftResolved
  obtain ⟨leftVar', rightVar, leftEquation, rightEquation⟩ :=
    resolveExpected?_pair iso contexts wire expected member signature
  have variableEquality : leftVar' = leftVar := by
    exact Option.some.inj (leftEquation.symm.trans leftResolved)
  subst leftVar'
  exact ⟨rightVar, rightEquation,
    envs wire expected leftVar rightVar leftResolved rightEquation⟩

theorem Internal.resolveIdentityPort?_forward_value
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (rightWellFormed : right.WellFormed definitions)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    {pre : PreModel}
    {leftEnv : Env pre leftContext.sigs}
    {rightEnv : Env pre rightContext.sigs}
    (envs : EnvironmentsCorrespond iso leftContext rightContext
      leftEnv rightEnv)
    {node : left.NodeId} {region : left.RegionId} {sig : Sig} {arity : Nat}
    (nodeData : left.nodes node = .identity region sig arity)
    (index : Nat) (leftVar : Var leftContext.sigs sig)
    (leftResolved :
      resolvePort? left leftContext node (.identity index) sig =
        some leftVar) :
    ∃ targetIndex rightVar,
      resolvePort? right rightContext (iso.nodes node)
          (.identity targetIndex) sig = some rightVar ∧
      leftEnv sig leftVar = rightEnv sig rightVar := by
  cases ownerEquation :
      left.endpointOwner? ⟨node, .identity index⟩ with
  | none =>
      simp [resolvePort?, ownerEquation] at leftResolved
  | some wire =>
      have expectedEquation :
          resolveExpected? left leftContext wire sig = some leftVar := by
        simpa [resolvePort?, ownerEquation] using leftResolved
      obtain ⟨targetIndex, targetOwner⟩ :=
        iso.identity_owner_forward rightWellFormed nodeData ownerEquation
      obtain ⟨rightVar, rightResolved, valuesEqual⟩ :=
        resolveExpected?_forward_value iso contexts envs wire sig
          leftVar expectedEquation
      refine ⟨targetIndex, rightVar, ?_, valuesEqual⟩
      simp [resolvePort?, targetOwner, rightResolved]

theorem Internal.resolveIdentityPort?_backward_value
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (leftWellFormed : left.WellFormed definitions)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    {pre : PreModel}
    {leftEnv : Env pre leftContext.sigs}
    {rightEnv : Env pre rightContext.sigs}
    (envs : EnvironmentsCorrespond iso leftContext rightContext
      leftEnv rightEnv)
    {node : left.NodeId} {region : left.RegionId} {sig : Sig} {arity : Nat}
    (nodeData : left.nodes node = .identity region sig arity)
    (targetIndex : Nat) (rightVar : Var rightContext.sigs sig)
    (rightResolved :
      resolvePort? right rightContext (iso.nodes node)
          (.identity targetIndex) sig = some rightVar) :
    ∃ sourceIndex leftVar,
      resolvePort? left leftContext node (.identity sourceIndex) sig =
          some leftVar ∧
      leftEnv sig leftVar = rightEnv sig rightVar := by
  cases targetOwner :
      right.endpointOwner? ⟨iso.nodes node, .identity targetIndex⟩ with
  | none =>
      simp [resolvePort?, targetOwner] at rightResolved
  | some targetWire =>
      have targetExpected :
          resolveExpected? right rightContext targetWire sig =
            some rightVar := by
        simpa [resolvePort?, targetOwner] using rightResolved
      obtain ⟨sourceIndex, sourceOwner⟩ :=
        iso.identity_owner_backward leftWellFormed nodeData targetOwner
      let sourceWire := iso.wires.symm targetWire
      have targetMember :=
        resolveExpected?_sound_member right rightContext targetWire sig
          targetExpected
      have sourceMember : sourceWire ∈ leftContext.ids :=
        contexts.backward targetWire targetMember
      have targetSignature :=
        resolveExpected?_sound_signature right rightContext targetWire sig
          targetExpected
      have sourceSignature : (left.wires sourceWire).sig = sig := by
        have signatureTransport := iso.wire_signature sourceWire
        have mappedWire : iso.wires sourceWire = targetWire :=
          iso.wires.right_inv targetWire
        rw [mappedWire] at signatureTransport
        exact signatureTransport.symm.trans targetSignature
      obtain ⟨leftVar, pairedRightVar, leftExpected, pairedRightExpected⟩ :=
        resolveExpected?_pair iso contexts sourceWire sig
          sourceMember sourceSignature
      have mappedWire : iso.wires sourceWire = targetWire := by
        exact iso.wires.right_inv targetWire
      have pairedEquality : pairedRightVar = rightVar := by
        apply Option.some.inj
        rw [mappedWire] at pairedRightExpected
        exact pairedRightExpected.symm.trans targetExpected
      subst pairedRightVar
      refine ⟨sourceIndex, leftVar, ?_, ?_⟩
      · change left.endpointOwner? ⟨node, .identity sourceIndex⟩ =
          some sourceWire at sourceOwner
        simp [resolvePort?, sourceOwner, leftExpected]
      · exact envs sourceWire sig leftVar rightVar
          leftExpected (by simpa [mappedWire] using targetExpected)

private theorem resolveAtomPort?_forward_value
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (leftWellFormed : left.WellFormed definitions)
    (rightWellFormed : right.WellFormed definitions)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    {pre : PreModel}
    {leftEnv : Env pre leftContext.sigs}
    {rightEnv : Env pre rightContext.sigs}
    (envs : EnvironmentsCorrespond iso leftContext rightContext
      leftEnv rightEnv)
    {node : left.NodeId} {region : left.RegionId} {args : List Sig}
    (nodeData : left.nodes node = .atom region args)
    (port : CPort) (expected : Sig)
    (leftVar : Var leftContext.sigs expected)
    (leftResolved :
      resolvePort? left leftContext node port expected = some leftVar) :
    ∃ rightVar,
      resolvePort? right rightContext (iso.nodes node) port expected =
        some rightVar ∧
      leftEnv expected leftVar = rightEnv expected rightVar := by
  cases ownerEquation :
      left.endpointOwner? ⟨node, port⟩ with
  | none => simp [resolvePort?, ownerEquation] at leftResolved
  | some wire =>
      have expectedEquation :
          resolveExpected? left leftContext wire expected = some leftVar := by
        simpa [resolvePort?, ownerEquation] using leftResolved
      have targetOwner := iso.atom_owner_forward leftWellFormed
        rightWellFormed nodeData ownerEquation
      obtain ⟨rightVar, rightResolved, valuesEqual⟩ :=
        resolveExpected?_forward_value iso contexts envs wire expected
          leftVar expectedEquation
      refine ⟨rightVar, ?_, valuesEqual⟩
      simp [resolvePort?, targetOwner, rightResolved]

private theorem resolveRefPort?_forward_value
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (leftWellFormed : left.WellFormed definitions)
    (rightWellFormed : right.WellFormed definitions)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    {pre : PreModel}
    {leftEnv : Env pre leftContext.sigs}
    {rightEnv : Env pre rightContext.sigs}
    (envs : EnvironmentsCorrespond iso leftContext rightContext
      leftEnv rightEnv)
    {node : left.NodeId} {region : left.RegionId}
    {definition : Fin definitions.length} {args : List Sig}
    (nodeData : left.nodes node = .ref region definition args)
    (port : CPort) (expected : Sig)
    (leftVar : Var leftContext.sigs expected)
    (leftResolved :
      resolvePort? left leftContext node port expected = some leftVar) :
    ∃ rightVar,
      resolvePort? right rightContext (iso.nodes node) port expected =
        some rightVar ∧
      leftEnv expected leftVar = rightEnv expected rightVar := by
  cases ownerEquation :
      left.endpointOwner? ⟨node, port⟩ with
  | none => simp [resolvePort?, ownerEquation] at leftResolved
  | some wire =>
      have expectedEquation :
          resolveExpected? left leftContext wire expected = some leftVar := by
        simpa [resolvePort?, ownerEquation] using leftResolved
      have targetOwner := iso.ref_owner_forward leftWellFormed
        rightWellFormed nodeData ownerEquation
      obtain ⟨rightVar, rightResolved, valuesEqual⟩ :=
        resolveExpected?_forward_value iso contexts envs wire expected
          leftVar expectedEquation
      refine ⟨rightVar, ?_, valuesEqual⟩
      simp [resolvePort?, targetOwner, rightResolved]

private theorem resolveAtomArgs?_forward_denote
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (leftWellFormed : left.WellFormed definitions)
    (rightWellFormed : right.WellFormed definitions)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    {pre : PreModel}
    {leftEnv : Env pre leftContext.sigs}
    {rightEnv : Env pre rightContext.sigs}
    (envs : EnvironmentsCorrespond iso leftContext rightContext
      leftEnv rightEnv)
    {node : left.NodeId} {region : left.RegionId} {nodeArgs : List Sig}
    (nodeData : left.nodes node = .atom region nodeArgs) :
    (args : List Sig) → (index : Nat) →
      (leftVars : Vars leftContext.sigs args) →
      resolveArgs? left leftContext node args index = some leftVars →
      ∃ rightVars,
        resolveArgs? right rightContext (iso.nodes node) args index =
          some rightVars ∧
        Vars.denote leftEnv leftVars = Vars.denote rightEnv rightVars
  | [], _, .nil, _ => ⟨.nil, rfl, rfl⟩
  | sig :: rest, index, .cons leftHead leftTail, equation => by
      cases headEquation :
          resolvePort? left leftContext node (.arg index) sig with
      | none => simp [resolveArgs?, headEquation] at equation
      | some resolvedHead =>
          cases tailEquation :
              resolveArgs? left leftContext node rest (index + 1) with
          | none =>
              simp [resolveArgs?, headEquation, tailEquation] at equation
          | some resolvedTail =>
              have pairEquality :
                  Vars.cons resolvedHead resolvedTail =
                    Vars.cons leftHead leftTail := by
                exact Option.some.inj (by
                  simpa [resolveArgs?, headEquation, tailEquation] using
                    equation)
              cases pairEquality
              obtain ⟨rightHead, rightHeadEquation, headDenotes⟩ :=
                resolveAtomPort?_forward_value iso leftWellFormed
                  rightWellFormed contexts envs nodeData (.arg index) sig
                  leftHead headEquation
              obtain ⟨rightTail, rightTailEquation, tailDenotes⟩ :=
                resolveAtomArgs?_forward_denote iso leftWellFormed
                  rightWellFormed contexts envs nodeData rest (index + 1)
                  leftTail tailEquation
              refine ⟨.cons rightHead rightTail, ?_, ?_⟩
              · simp [resolveArgs?, rightHeadEquation, rightTailEquation]
              · simp only [Vars.denote_cons, headDenotes, tailDenotes]

private theorem resolveRefArgs?_forward_denote
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (leftWellFormed : left.WellFormed definitions)
    (rightWellFormed : right.WellFormed definitions)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    {pre : PreModel}
    {leftEnv : Env pre leftContext.sigs}
    {rightEnv : Env pre rightContext.sigs}
    (envs : EnvironmentsCorrespond iso leftContext rightContext
      leftEnv rightEnv)
    {node : left.NodeId} {region : left.RegionId}
    {definition : Fin definitions.length} {nodeArgs : List Sig}
    (nodeData : left.nodes node = .ref region definition nodeArgs) :
    (args : List Sig) → (index : Nat) →
      (leftVars : Vars leftContext.sigs args) →
      resolveArgs? left leftContext node args index = some leftVars →
      ∃ rightVars,
        resolveArgs? right rightContext (iso.nodes node) args index =
          some rightVars ∧
        Vars.denote leftEnv leftVars = Vars.denote rightEnv rightVars
  | [], _, .nil, _ => ⟨.nil, rfl, rfl⟩
  | sig :: rest, index, .cons leftHead leftTail, equation => by
      cases headEquation :
          resolvePort? left leftContext node (.arg index) sig with
      | none => simp [resolveArgs?, headEquation] at equation
      | some resolvedHead =>
          cases tailEquation :
              resolveArgs? left leftContext node rest (index + 1) with
          | none =>
              simp [resolveArgs?, headEquation, tailEquation] at equation
          | some resolvedTail =>
              have pairEquality :
                  Vars.cons resolvedHead resolvedTail =
                    Vars.cons leftHead leftTail := by
                exact Option.some.inj (by
                  simpa [resolveArgs?, headEquation, tailEquation] using
                    equation)
              cases pairEquality
              obtain ⟨rightHead, rightHeadEquation, headDenotes⟩ :=
                resolveRefPort?_forward_value iso leftWellFormed
                  rightWellFormed contexts envs nodeData (.arg index) sig
                  leftHead headEquation
              obtain ⟨rightTail, rightTailEquation, tailDenotes⟩ :=
                resolveRefArgs?_forward_denote iso leftWellFormed
                  rightWellFormed contexts envs nodeData rest (index + 1)
                  leftTail tailEquation
              refine ⟨.cons rightHead rightTail, ?_, ?_⟩
              · simp [resolveArgs?, rightHeadEquation, rightTailEquation]
              · simp only [Vars.denote_cons, headDenotes, tailDenotes]

theorem Internal.compileAtomNode?_forward_denotation
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
    {node : left.NodeId} {region : left.RegionId} {args : List Sig}
    (nodeData : left.nodes node = .atom region args)
    (leftItem : Item definitions leftContext.sigs)
    (leftCompiled :
      compileNode? definitions left leftContext node = some leftItem) :
    ∃ rightItem,
      compileNode? definitions right rightContext (iso.nodes node) =
        some rightItem ∧
      (denoteItem pre definitionEnv leftEnv leftItem ↔
        denoteItem pre definitionEnv rightEnv rightItem) := by
  cases headEquation :
      resolvePort? left leftContext node .head (.rel args) with
  | none =>
      simp [compileNode?, nodeData, headEquation] at leftCompiled
  | some leftHead =>
      cases argsEquation :
          resolveArgs? left leftContext node args 0 with
      | none =>
          simp [compileNode?, nodeData, headEquation, argsEquation] at leftCompiled
      | some leftArgs =>
          have itemEquality :
              (Item.atom leftHead leftArgs :
                Item definitions leftContext.sigs) = leftItem := by
            exact Option.some.inj (by
              simpa [compileNode?, nodeData, headEquation, argsEquation] using
                leftCompiled)
          subst leftItem
          obtain ⟨rightHead, rightHeadEquation, headDenotes⟩ :=
            resolveAtomPort?_forward_value iso leftWellFormed rightWellFormed
              contexts envs nodeData .head (.rel args) leftHead headEquation
          obtain ⟨rightArgs, rightArgsEquation, argsDenote⟩ :=
            resolveAtomArgs?_forward_denote iso leftWellFormed rightWellFormed
              contexts envs nodeData args 0 leftArgs argsEquation
          refine ⟨.atom rightHead rightArgs, ?_, ?_⟩
          · simp [compileNode?, iso.node_table, nodeData, CNode.rename,
              rightHeadEquation, rightArgsEquation]
          · simp only [denoteItem_atom, headDenotes, argsDenote]

theorem Internal.compileRefNode?_forward_denotation
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
    {definition : Fin definitions.length} {args : List Sig}
    (nodeData : left.nodes node = .ref region definition args)
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
  · rename_i signature
    cases argsEquation :
        resolveArgs? left leftContext node args 0 with
    | none =>
        simp [argsEquation] at leftCompiled
    | some leftArgs =>
        let reference : DefVar definitions args :=
          signature ▸ definitionVarAt definitions definition
        have itemEquality :
              (Item.named reference leftArgs :
              Item definitions leftContext.sigs) = leftItem := by
          exact Option.some.inj (by
            simpa [argsEquation, reference] using leftCompiled)
        subst leftItem
        obtain ⟨rightArgs, rightArgsEquation, argsDenote⟩ :=
          resolveRefArgs?_forward_denote iso leftWellFormed rightWellFormed
            contexts envs nodeData args 0 leftArgs argsEquation
        refine ⟨.named reference rightArgs, ?_, ?_⟩
        · simp only [compileNode?, iso.node_table, nodeData, CNode.rename]
          split
          · simp [rightArgsEquation, reference]
          · contradiction
        · simp only [denoteItem_named, argsDenote]
  · simp at leftCompiled

private theorem endpointOwner?_incident
    (diagram : ConcreteDiagram definitionCount)
    (endpoint : CEndpoint diagram.nodeCount) (wire : diagram.WireId)
    (owner : diagram.endpointOwner? endpoint = some wire) :
    endpoint ∈ (diagram.wires wire).endpoints := by
  unfold ConcreteDiagram.endpointOwner? at owner
  cases found :
      diagram.endpointOccurrences.find? (fun occurrence =>
        occurrence.2 == endpoint) with
  | none => simp [found] at owner
  | some occurrence =>
      have occurrenceMember :=
        List.mem_of_find?_eq_some found
      have endpointEquality :
          occurrence.2 = endpoint :=
        eq_of_beq (List.find?_some
          (p := fun occurrence :
            diagram.WireId × CEndpoint diagram.nodeCount =>
              occurrence.2 == endpoint) found)
      have wireEquality : occurrence.1 = wire := by
        simpa [found] using owner
      subst endpoint
      subst wire
      simp only [ConcreteDiagram.endpointOccurrences,
        List.mem_flatMap] at occurrenceMember
      rcases occurrenceMember with ⟨candidate, _, member⟩
      simp only [List.mem_map] at member
      rcases member with ⟨candidateEndpoint, candidateMember, equality⟩
      cases equality
      exact candidateMember

private theorem endpointOwner?_occurs
    (diagram : ConcreteDiagram definitionCount)
    (endpoint : CEndpoint diagram.nodeCount) (wire : diagram.WireId)
    (owner : diagram.endpointOwner? endpoint = some wire) :
    (wire, endpoint) ∈ diagram.endpointOccurrences := by
  unfold ConcreteDiagram.endpointOwner? at owner
  cases found :
      diagram.endpointOccurrences.find? (fun occurrence =>
        occurrence.2 == endpoint) with
  | none => simp [found] at owner
  | some occurrence =>
      have occurrenceMember :=
        List.mem_of_find?_eq_some found
      have endpointEquality : occurrence.2 = endpoint :=
        eq_of_beq (List.find?_some
          (p := fun occurrence :
            diagram.WireId × CEndpoint diagram.nodeCount =>
              occurrence.2 == endpoint) found)
      have wireEquality : occurrence.1 = wire := by
        simpa [found] using owner
      have pairEquality : occurrence = (wire, endpoint) :=
        Prod.ext wireEquality endpointEquality
      simpa [pairEquality] using occurrenceMember

theorem Internal.endpointOwner?_complete
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (node : diagram.NodeId) (port : CPort)
    (required : port ∈ diagram.requiredPorts node) :
    ∃ wire, diagram.endpointOwner? ⟨node, port⟩ = some wire := by
  have nodeCheck := (List.all_eq_true.mp
    wellFormed.ports_covered_exactly_once) node
    (Data.Finite.mem_allFin node)
  have portCheck := (List.all_eq_true.mp nodeCheck) port required
  rw [Bool.and_eq_true] at portCheck
  exact Option.isSome_iff_exists.mp portCheck.2

theorem Internal.endpoint_scope
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (endpoint : CEndpoint diagram.nodeCount) (wire : diagram.WireId)
    (owner : diagram.endpointOwner? endpoint = some wire) :
    diagram.Encloses (diagram.wires wire).scope
      (diagram.nodes endpoint.node).region := by
  have occurrence := endpointOwner?_occurs diagram endpoint wire owner
  have checked := (List.all_eq_true.mp
    wellFormed.wire_scopes_enclose) (wire, endpoint) occurrence
  exact of_decide_eq_true checked

theorem encloses_iff_exists
    (diagram : ConcreteDiagram definitionCount)
    (ancestor descendant : diagram.RegionId) :
    diagram.Encloses ancestor descendant ↔
      ∃ steps : Fin (diagram.regionCount + 1),
        diagram.climb steps descendant = some ancestor := by
  simp [ConcreteDiagram.Encloses]

/--
Any successful parent-chain traversal in a well-formed diagram fits within
the region table. This supports transport of enclosure witnesses into a
larger region table without exposing a second representation of enclosure.
-/
theorem successfulClimb_le_count
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (steps : Nat) (region ancestor : diagram.RegionId)
    (climbed : diagram.climb steps region = some ancestor) :
    steps ≤ diagram.regionCount := by
  have climbAdd :
      ∀ (first second : Nat) (start : diagram.RegionId),
        diagram.climb (first + second) start =
          (diagram.climb first start).bind (diagram.climb second) := by
    intro first
    induction first with
    | zero =>
        intro second start
        simp
    | succ first induction =>
        intro second start
        cases regionData : diagram.regions start with
        | sheet =>
            simp [Nat.succ_add, ConcreteDiagram.climb, regionData]
        | cut parent =>
            simpa [ConcreteDiagram.climb, regionData, Nat.succ_add] using
              induction second parent
  have climbToRootUnique :
      ∀ {start : diagram.RegionId} {left right : Nat},
        diagram.climb left start = some diagram.root →
        diagram.climb right start = some diagram.root →
        left = right := by
    intro start left right
    induction left generalizing right start with
    | zero =>
        intro leftClimb rightClimb
        have startRoot : start = diagram.root := by
          simpa [ConcreteDiagram.climb] using leftClimb
        subst start
        cases right with
        | zero => rfl
        | succ right =>
            rw [ConcreteDiagram.climb, wellFormed.root_is_sheet] at rightClimb
            contradiction
    | succ left induction =>
        intro leftClimb rightClimb
        cases right with
        | zero =>
            have startRoot : start = diagram.root := by
              simpa [ConcreteDiagram.climb] using rightClimb
            subst start
            rw [ConcreteDiagram.climb, wellFormed.root_is_sheet] at leftClimb
            contradiction
        | succ right =>
            cases regionData : diagram.regions start with
            | sheet =>
                simp [ConcreteDiagram.climb, regionData] at leftClimb
            | cut parent =>
                apply congrArg Nat.succ
                apply induction
                · simpa [ConcreteDiagram.climb, regionData] using leftClimb
                · simpa [ConcreteDiagram.climb, regionData] using rightClimb
  have ancestorReaches :
      diagram.Encloses diagram.root ancestor :=
    of_decide_eq_true
      ((List.all_eq_true.mp wellFormed.all_regions_reach_root)
        ancestor (Data.Finite.mem_allFin ancestor))
  obtain ⟨rootSteps, ancestorRoot⟩ :=
    (encloses_iff_exists diagram diagram.root ancestor).mp ancestorReaches
  have regionRoot :
      diagram.climb (steps + rootSteps.val) region =
        some diagram.root := by
    rw [climbAdd, climbed]
    exact ancestorRoot
  have regionReaches :
      diagram.Encloses diagram.root region :=
    of_decide_eq_true
      ((List.all_eq_true.mp wellFormed.all_regions_reach_root)
        region (Data.Finite.mem_allFin region))
  obtain ⟨bounded, boundedRoot⟩ :=
    (encloses_iff_exists diagram diagram.root region).mp regionReaches
  have same := climbToRootUnique regionRoot boundedRoot
  omega

theorem Internal.root_has_no_strict_ancestor
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (ancestor : diagram.RegionId)
    (encloses : diagram.Encloses ancestor diagram.root) :
    ancestor = diagram.root := by
  rcases (encloses_iff_exists diagram ancestor diagram.root).mp encloses with
    ⟨⟨steps, bound⟩, climbed⟩
  cases steps with
  | zero => simpa using climbed.symm
  | succ steps =>
      have rootData : diagram.regions diagram.root = .sheet :=
        wellFormed.root_is_sheet
      rw [ConcreteDiagram.climb, rootData] at climbed
      simp at climbed

theorem Internal.encloses_child_split
    (diagram : ConcreteDiagram definitionCount)
    (ancestor child parent : diagram.RegionId)
    (childData : diagram.regions child = .cut parent)
    (encloses : diagram.Encloses ancestor child) :
    ancestor = child ∨ diagram.Encloses ancestor parent := by
  rcases (encloses_iff_exists diagram ancestor child).mp encloses with
    ⟨⟨steps, bound⟩, climbed⟩
  cases steps with
  | zero => exact .inl (by simpa using climbed.symm)
  | succ steps =>
      right
      apply (encloses_iff_exists diagram ancestor parent).mpr
      exact ⟨⟨steps, by omega⟩, by
        simpa [ConcreteDiagram.climb, childData] using climbed⟩

end ConcreteElaboration

end VisualProof
