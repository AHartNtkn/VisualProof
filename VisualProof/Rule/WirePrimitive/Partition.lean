import VisualProof.Diagram.Concrete.WirePartitionIsomorphism
import VisualProof.Diagram.Concrete.WirePartitionSemantics
import VisualProof.Rule.Structural

namespace VisualProof

namespace WirePrimitive

namespace Partition

/-- Stable refusal outcomes of generic signature-indexed partition/merge. -/
inductive WirePartitionError
  | duplicateEndpoint
  | endpointNotOnWire
  | severScopeOutsideWire
  | movedEndpointOutsideScope
  | signatureMismatch
  | incomparableScopes
  | severRequiresPositive
  | severBackwardRequiresNegative
  | joinRequiresNegative
  | joinBackwardRequiresPositive
  | scopeCompilationFailed
  | transportMismatch
  | concreteRejected (error : ConcreteWireQuantifier.Error)
  deriving Repr, DecidableEq

/-- Partition one wire, placing the moved endpoints on a wire at `scope`. -/
structure WireSeverInput (source : CheckedDiagram definitions) where
  orientation : Orientation
  wire : source.val.WireId
  keep : List (CEndpoint source.val.nodeCount)
  scope : source.val.RegionId

/-- Merge two distinct equal-signature wires at their outer scope. -/
structure WireJoinInput (source : CheckedDiagram definitions) where
  orientation : Orientation
  left : source.val.WireId
  right : source.val.WireId

private def severPolarityLegal
    (orientation : Orientation) (depth : Nat) : Bool :=
  match orientation with
  | .forward => decide (depth % 2 = 0)
  | .backward => decide (depth % 2 = 1)

private def joinPolarityLegal
    (orientation : Orientation) (depth : Nat) : Bool :=
  match orientation with
  | .forward => decide (depth % 2 = 1)
  | .backward => decide (depth % 2 = 0)

private structure CheckedSeverPolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (scope : source.val.RegionId) where
  compiled : SiteCompilation source scope
  legal :
    severPolarityLegal orientation compiled.frame.context.cutDepth = true

private structure CheckedJoinPolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (scope : source.val.RegionId) where
  compiled : SiteCompilation source scope
  legal :
    joinPolarityLegal orientation compiled.frame.context.cutDepth = true

private structure WireSeverReceipt
    (source : CheckedDiagram definitions)
    (input : WireSeverInput source)
    (target : CheckedDiagram definitions) where
  polarity : CheckedSeverPolarity source input.orientation input.scope
  result :
    ConcreteWireQuantifier.WireSeverResult
      source input.wire input.keep input.scope
  accepted :
    ConcreteWireQuantifier.severWire
      source input.wire input.keep input.scope = .ok result
  targetExact : result.checked = target

private structure WireJoinReceipt
    (source : CheckedDiagram definitions)
    (input : WireJoinInput source)
    (target : CheckedDiagram definitions) where
  outer : source.val.WireId
  inner : source.val.WireId
  side :
    outer = input.left ∧ inner = input.right ∨
      outer = input.right ∧ inner = input.left
  comparable :
    source.val.Encloses
      (source.val.wires outer).scope
      (source.val.wires inner).scope
  polarity :
    CheckedJoinPolarity source input.orientation
      (source.val.wires inner).scope
  result : ConcreteWireQuantifier.WireJoinResult source outer inner
  accepted :
    ConcreteWireQuantifier.joinWires source outer inner = .ok result
  targetExact : result.checked = target

/-- Opaque checker-owned receipt for one accepted wire partition. -/
structure AppliedWireSever
    (source : CheckedDiagram definitions)
    (input : WireSeverInput source) where
  private mk ::
  target : CheckedDiagram definitions
  private checked : WireSeverReceipt source input target

/-- Opaque checker-owned receipt for one accepted wire merge. -/
structure AppliedWireJoin
    (source : CheckedDiagram definitions)
    (input : WireJoinInput source) where
  private mk ::
  target : CheckedDiagram definitions
  private checked : WireJoinReceipt source input target

private def requireSeverPolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (scope : source.val.RegionId) :
    Except WirePartitionError
      (CheckedSeverPolarity source orientation scope) := by
  match compileSite? source scope with
  | none => exact .error .scopeCompilationFailed
  | some compiled =>
      if legal :
          severPolarityLegal orientation compiled.frame.context.cutDepth then
        exact .ok ⟨compiled, legal⟩
      else
        exact .error <|
          match orientation with
          | .forward => .severRequiresPositive
          | .backward => .severBackwardRequiresNegative

private def requireJoinPolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (scope : source.val.RegionId) :
    Except WirePartitionError
      (CheckedJoinPolarity source orientation scope) := by
  match compileSite? source scope with
  | none => exact .error .scopeCompilationFailed
  | some compiled =>
      if legal :
          joinPolarityLegal orientation compiled.frame.context.cutDepth then
        exact .ok ⟨compiled, legal⟩
      else
        exact .error <|
          match orientation with
          | .forward => .joinRequiresNegative
          | .backward => .joinBackwardRequiresPositive

private def endpointMember
    (endpoint : CEndpoint nodeCount)
    (endpoints : List (CEndpoint nodeCount)) : Bool :=
  decide (endpoint ∈ endpoints)

private def movedEndpointsEnclosed
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (keep : List (CEndpoint source.val.nodeCount))
    (scope : source.val.RegionId) : Bool :=
  (source.val.wires wire).endpoints.all fun endpoint =>
    decide (endpoint ∈ keep) ||
      decide
        (source.val.Encloses scope
          (source.val.nodes endpoint.node).region)

/-- Validate and apply one signature-indexed endpoint partition. -/
def applyWireSever
    (source : CheckedDiagram definitions)
    (input : WireSeverInput source) :
    Except WirePartitionError (AppliedWireSever source input) := by
  let data := source.val.wires input.wire
  if !input.keep.Nodup then
    exact .error .duplicateEndpoint
  else if !(input.keep.all
      (fun endpoint => endpointMember endpoint data.endpoints)) then
    exact .error .endpointNotOnWire
  else if !source.val.Encloses data.scope input.scope then
    exact .error .severScopeOutsideWire
  else if !(movedEndpointsEnclosed
      source input.wire input.keep input.scope) then
    exact .error .movedEndpointOutsideScope
  else
    match requireSeverPolarity source input.orientation input.scope with
    | .error error => exact .error error
    | .ok polarity =>
        match accepted :
            ConcreteWireQuantifier.severWire
              source input.wire input.keep input.scope with
        | .error error => exact .error (.concreteRejected error)
        | .ok result =>
            exact .ok
              (AppliedWireSever.mk result.checked
                { polarity := polarity
                  result := result
                  accepted := accepted
                  targetExact := rfl })

/-- Validate and apply one equal-signature comparable-scope wire merge. -/
def applyWireJoin
    (source : CheckedDiagram definitions)
    (input : WireJoinInput source) :
    Except WirePartitionError (AppliedWireJoin source input) := by
  if input.left = input.right then
    exact .error .incomparableScopes
  else if (source.val.wires input.left).sig !=
      (source.val.wires input.right).sig then
    exact .error .signatureMismatch
  else if leftOuter :
      source.val.Encloses (source.val.wires input.left).scope
        (source.val.wires input.right).scope then
    match requireJoinPolarity source input.orientation
        (source.val.wires input.right).scope with
    | .error error => exact .error error
    | .ok polarity =>
        match accepted :
            ConcreteWireQuantifier.joinWires
              source input.left input.right with
        | .error error => exact .error (.concreteRejected error)
        | .ok result =>
            exact .ok
              (AppliedWireJoin.mk result.checked
                { outer := input.left
                  inner := input.right
                  side := Or.inl ⟨rfl, rfl⟩
                  comparable := leftOuter
                  polarity := polarity
                  result := result
                  accepted := accepted
                  targetExact := rfl })
  else if rightOuter :
      source.val.Encloses (source.val.wires input.right).scope
        (source.val.wires input.left).scope then
    match requireJoinPolarity source input.orientation
        (source.val.wires input.left).scope with
    | .error error => exact .error error
    | .ok polarity =>
        match accepted :
            ConcreteWireQuantifier.joinWires
              source input.right input.left with
        | .error error => exact .error (.concreteRejected error)
        | .ok result =>
            exact .ok
              (AppliedWireJoin.mk result.checked
                { outer := input.right
                  inner := input.left
                  side := Or.inr ⟨rfl, rfl⟩
                  comparable := rightOuter
                  polarity := polarity
                  result := result
                  accepted := accepted
                  targetExact := rfl })
  else
    exact .error .incomparableScopes

/-- Deterministic checked inverse of one accepted sever, owned by the sever
receipt rather than rediscovered from the target graph. -/
structure WireSeverInverse
    {source : CheckedDiagram definitions}
    {input : WireSeverInput source}
    (applied : AppliedWireSever source input)
    (orientation : Orientation) where
  input : WireJoinInput applied.checked.result.checked
  applied : AppliedWireJoin applied.checked.result.checked input
  targetIso : ConcreteIso applied.target.val source.val

/-- Build the canonical inverse join named by the sever construction.  The
only executable refusal left is the inverse orientation's polarity gate. -/
def invertWireSever
    {source : CheckedDiagram definitions}
    {input : WireSeverInput source}
    (applied : AppliedWireSever source input)
    (orientation : Orientation) :
    Except WirePartitionError (WireSeverInverse applied orientation) := by
  let result := applied.checked.result
  let left := result.wireImage input.wire
  let right := result.freshWire
  let inverseInput : WireJoinInput result.checked :=
    { orientation := orientation
      left := left
      right := right }
  match polarityAccepted :
      requireJoinPolarity result.checked orientation
        (result.checked.val.wires right).scope with
  | .error error => exact .error error
  | .ok polarity =>
      have comparable :
          result.checked.val.Encloses
            (result.checked.val.wires left).scope
            (result.checked.val.wires right).scope := by
        dsimp [left, right, result]
        rw [result.wireImage_scope, result.freshWire_scope]
        exact result.encloses_regionImage result.sourceScope_encloses_scope
      match accepted :
          ConcreteWireQuantifier.joinWires result.checked left right with
      | .error error => exact .error (.concreteRejected error)
      | .ok inverseResult =>
          have targetExact :
              inverseResult.checked = result.inverseJoin.checked := by
            apply Subtype.ext
            exact inverseResult.checked_generated.trans
              result.inverseJoin.checked_generated.symm
          let inverseApplied :
              AppliedWireJoin result.checked inverseInput :=
            AppliedWireJoin.mk inverseResult.checked
              { outer := left
                inner := right
                side := Or.inl ⟨rfl, rfl⟩
                comparable := comparable
                polarity := polarity
                result := inverseResult
                accepted := accepted
                targetExact := rfl }
          exact .ok
            { input := inverseInput
              applied := inverseApplied
              targetIso := by
                change ConcreteIso inverseResult.checked.val source.val
                rw [targetExact]
                exact result.inverseIso.symm }

/-- Deterministic inverse of an accepted sever after a suffix has renamed its
checked target.  The supplied isomorphism transports the two canonical join
parameters; no wire pair or target isomorphism is searched for. -/
structure TransportedWireSeverInverse
    {source : CheckedDiagram definitions}
    {input : WireSeverInput source}
    (sever : AppliedWireSever source input)
    (real : CheckedDiagram definitions)
    (targetIso : ConcreteIso real.val sever.target.val)
    (orientation : Orientation) where
  input : WireJoinInput real
  applied : AppliedWireJoin real input
  targetIso : ConcreteIso applied.target.val source.val

/-- Construct the inverse join from the canonical sever receipt after pulling
its parameters through the supplied suffix isomorphism. -/
def invertWireSeverTransported
    {source : CheckedDiagram definitions}
    {input : WireSeverInput source}
    (sever : AppliedWireSever source input)
    (real : CheckedDiagram definitions)
    (targetIso : ConcreteIso real.val sever.target.val)
    (orientation : Orientation) :
    Except WirePartitionError
      (TransportedWireSeverInverse sever real targetIso orientation) := by
  let canonical := sever.checked.result
  have realToCanonical : ConcreteIso real.val canonical.checked.val := by
    rw [sever.checked.targetExact]
    exact targetIso
  let left := realToCanonical.wires.symm
    (canonical.wireImage input.wire)
  let right := realToCanonical.wires.symm canonical.freshWire
  let inverseInput : WireJoinInput real :=
    { orientation := orientation
      left := left
      right := right }
  match polarityAccepted :
      requireJoinPolarity real orientation
        (real.val.wires right).scope with
  | .error error => exact .error error
  | .ok polarity =>
      have different : left ≠ right := by
        intro same
        have mapped := congrArg realToCanonical.wires same
        have leftExact : realToCanonical.wires left =
            canonical.wireImage input.wire := by
          change realToCanonical.wires.toFun
            (realToCanonical.wires.invFun
              (canonical.wireImage input.wire)) = _
          exact realToCanonical.wires.right_inv _
        have rightExact : realToCanonical.wires right =
            canonical.freshWire := by
          change realToCanonical.wires.toFun
            (realToCanonical.wires.invFun canonical.freshWire) = _
          exact realToCanonical.wires.right_inv _
        rw [leftExact, rightExact] at mapped
        exact canonical.inverseJoin.outer_ne_inner mapped
      have signaturesEqual :
          (real.val.wires left).sig = (real.val.wires right).sig := by
        have leftSig := realToCanonical.wire_signature left
        have rightSig := realToCanonical.wire_signature right
        have leftExact : realToCanonical.wires left =
            canonical.wireImage input.wire := by
          change realToCanonical.wires.toFun
            (realToCanonical.wires.invFun
              (canonical.wireImage input.wire)) = _
          exact realToCanonical.wires.right_inv _
        have rightExact : realToCanonical.wires right =
            canonical.freshWire := by
          change realToCanonical.wires.toFun
            (realToCanonical.wires.invFun canonical.freshWire) = _
          exact realToCanonical.wires.right_inv _
        rw [leftExact] at leftSig
        rw [rightExact] at rightSig
        exact leftSig.symm.trans
          (canonical.inverseJoin.source_signatures_equal.trans rightSig)
      have comparable :
          real.val.Encloses
            (real.val.wires left).scope
            (real.val.wires right).scope := by
        have canonicalComparable :
            canonical.checked.val.Encloses
              (canonical.checked.val.wires
                (canonical.wireImage input.wire)).scope
              (canonical.checked.val.wires canonical.freshWire).scope := by
          rw [canonical.wireImage_scope, canonical.freshWire_scope]
          exact canonical.encloses_regionImage
            canonical.sourceScope_encloses_scope
        have pulled := realToCanonical.symm.encloses_transport
          canonicalComparable
        have leftScope :
            (real.val.wires left).scope =
              realToCanonical.regions.symm
                (canonical.checked.val.wires
                  (canonical.wireImage input.wire)).scope := by
          simpa [left] using
            realToCanonical.symm.wire_scope
              (canonical.wireImage input.wire)
        have rightScope :
            (real.val.wires right).scope =
              realToCanonical.regions.symm
                (canonical.checked.val.wires canonical.freshWire).scope := by
          simpa [right] using
            realToCanonical.symm.wire_scope canonical.freshWire
        rw [leftScope, rightScope]
        exact pulled
      match accepted : ConcreteWireQuantifier.joinWires real left right with
      | .error error => exact .error (.concreteRejected error)
      | .ok actual =>
          let inverseApplied : AppliedWireJoin real inverseInput :=
            AppliedWireJoin.mk actual.checked
              { outer := left
                inner := right
                side := Or.inl ⟨rfl, rfl⟩
                comparable := comparable
                polarity := polarity
                result := actual
                accepted := accepted
                targetExact := rfl }
          match natural : actual.transportedIso? realToCanonical
              canonical.inverseJoin
              (by
                change realToCanonical.wires.toFun
                  (realToCanonical.wires.invFun
                    (canonical.wireImage input.wire)) = _
                exact realToCanonical.wires.right_inv _)
              (by
                change realToCanonical.wires.toFun
                  (realToCanonical.wires.invFun canonical.freshWire) = _
                exact realToCanonical.wires.right_inv _) with
          | none => exact .error .transportMismatch
          | some outputIso =>
              match composed : outputIso.checkedTrans?
                  canonical.inverseIso.symm with
              | none => exact .error .transportMismatch
              | some sourceIso =>
                  exact .ok
                    { input := inverseInput
                      applied := inverseApplied
                      targetIso := sourceIso }

/-- Generic signature-indexed wire partition is sound over every premodel. -/
theorem wire_sever_sound
    {source : CheckedDiagram definitions}
    (input : WireSeverInput source)
    (applied : AppliedWireSever source input)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    Directed input.orientation
      (denoteChecked pre definitionEnv source)
      (denoteChecked pre definitionEnv applied.target) := by
  rcases input with ⟨orientation, wire, keep, scope⟩
  let checked := applied.checked
  have sound :=
    checked.result.denotes checked.polarity.compiled pre definitionEnv
  rw [checked.targetExact] at sound
  cases orientation with
  | forward =>
      have even :
          checked.polarity.compiled.frame.context.cutDepth % 2 = 0 :=
        of_decide_eq_true (by
          simpa [severPolarityLegal] using checked.polarity.legal)
      exact sound.1 even
  | backward =>
      have odd :
          checked.polarity.compiled.frame.context.cutDepth % 2 = 1 :=
        of_decide_eq_true (by
          simpa [severPolarityLegal] using checked.polarity.legal)
      exact sound.2 odd

/-- Generic equal-signature wire merge is sound over every premodel. -/
theorem wire_join_sound
    {source : CheckedDiagram definitions}
    (input : WireJoinInput source)
    (applied : AppliedWireJoin source input)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    Directed input.orientation
      (denoteChecked pre definitionEnv source)
      (denoteChecked pre definitionEnv applied.target) := by
  rcases input with ⟨orientation, left, right⟩
  let checked := applied.checked
  have sound :=
    checked.result.denotes checked.comparable checked.polarity.compiled
      pre definitionEnv
  rw [checked.targetExact] at sound
  cases orientation with
  | forward =>
      have odd :
          checked.polarity.compiled.frame.context.cutDepth % 2 = 1 :=
        of_decide_eq_true (by
          simpa [joinPolarityLegal] using checked.polarity.legal)
      exact sound.2 odd
  | backward =>
      have even :
          checked.polarity.compiled.frame.context.cutDepth % 2 = 0 :=
        of_decide_eq_true (by
          simpa [joinPolarityLegal] using checked.polarity.legal)
      exact sound.1 even

end Partition

export Partition
  (WireSeverInput WireJoinInput WirePartitionError
    AppliedWireSever AppliedWireJoin applyWireSever applyWireJoin
    wire_sever_sound wire_join_sound)

end WirePrimitive

export WirePrimitive
  (WireSeverInput WireJoinInput WirePartitionError
    AppliedWireSever AppliedWireJoin applyWireSever applyWireJoin
    wire_sever_sound wire_join_sound)

end VisualProof
