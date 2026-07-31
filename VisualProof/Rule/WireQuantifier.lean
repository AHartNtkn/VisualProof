import VisualProof.Diagram.Concrete.WireQuantifierIotaSemantics
import VisualProof.Rule.Structural

namespace VisualProof

namespace WireQuantifier

/-- Stable refusal outcomes of the temporary iota partition/merge facade. -/
inductive WireQuantifierError
  | expectedIota
  | duplicateEndpoint
  | endpointNotOnWire
  | incomparableScopes
  | severRequiresPositive
  | severBackwardRequiresNegative
  | joinRequiresNegative
  | joinBackwardRequiresPositive
  | scopeCompilationFailed
  | concreteRejected (error : ConcreteWireQuantifier.Error)
  deriving Repr, DecidableEq

/-- Temporary iota-only sever input, replaced by generic partition in Task 3. -/
inductive WireSeverInput (source : CheckedDiagram definitions)
  | iota
      (orientation : Orientation)
      (wire : source.val.WireId)
      (keep : List (CEndpoint source.val.nodeCount))

/-- Temporary iota-only join input, replaced by generic merge in Task 3. -/
inductive WireJoinInput (source : CheckedDiagram definitions)
  | iota
      (orientation : Orientation)
      (left right : source.val.WireId)

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

private structure IotaSeverReceipt
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId)
    (keep : List (CEndpoint source.val.nodeCount))
    (target : CheckedDiagram definitions) where
  polarity :
    CheckedSeverPolarity source orientation (source.val.wires wire).scope
  result : ConcreteWireQuantifier.IotaSeverResult source wire keep
  accepted :
    ConcreteWireQuantifier.severIota source wire keep = .ok result
  targetExact : result.checked = target

private structure IotaJoinReceipt
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (left right : source.val.WireId)
    (target : CheckedDiagram definitions) where
  outer : source.val.WireId
  inner : source.val.WireId
  side :
    outer = left ∧ inner = right ∨
      outer = right ∧ inner = left
  comparable :
    source.val.Encloses
      (source.val.wires outer).scope
      (source.val.wires inner).scope
  polarity :
    CheckedJoinPolarity source orientation (source.val.wires inner).scope
  result : ConcreteWireQuantifier.IotaJoinResult source outer inner
  accepted :
    ConcreteWireQuantifier.joinIota source outer inner = .ok result
  targetExact : result.checked = target

/-- Opaque accepted temporary iota sever. -/
structure AppliedWireSever
    (source : CheckedDiagram definitions)
    (input : WireSeverInput source) where
  private mk ::
  target : CheckedDiagram definitions
  private checked :
    match input with
    | .iota orientation wire keep =>
        IotaSeverReceipt source orientation wire keep target

/-- Opaque accepted temporary iota join. -/
structure AppliedWireJoin
    (source : CheckedDiagram definitions)
    (input : WireJoinInput source) where
  private mk ::
  target : CheckedDiagram definitions
  private checked :
    match input with
    | .iota orientation left right =>
        IotaJoinReceipt source orientation left right target

private def requireSeverPolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (scope : source.val.RegionId) :
    Except WireQuantifierError
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
    Except WireQuantifierError
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

/-- Validate and apply one temporary iota partition. -/
def applyWireSever
    (source : CheckedDiagram definitions)
    (input : WireSeverInput source) :
    Except WireQuantifierError (AppliedWireSever source input) := by
  cases input with
  | iota orientation wire keep =>
      let data := source.val.wires wire
      if data.sig != .iota then
        exact .error .expectedIota
      else if !keep.Nodup then
        exact .error .duplicateEndpoint
      else if !keep.all (fun endpoint => endpointMember endpoint data.endpoints) then
        exact .error .endpointNotOnWire
      else
        match requireSeverPolarity source orientation data.scope with
        | .error error => exact .error error
        | .ok polarity =>
            match accepted :
                ConcreteWireQuantifier.severIota source wire keep with
            | .error error => exact .error (.concreteRejected error)
            | .ok result =>
                exact .ok
                  (AppliedWireSever.mk result.checked
                    { polarity := polarity
                      result := result
                      accepted := accepted
                      targetExact := rfl })

/-- Validate and apply one temporary comparable-scope iota merge. -/
def applyWireJoin
    (source : CheckedDiagram definitions)
    (input : WireJoinInput source) :
    Except WireQuantifierError (AppliedWireJoin source input) := by
  cases input with
  | iota orientation left right =>
      if left = right then
        exact .error .incomparableScopes
      else if (source.val.wires left).sig != .iota ||
          (source.val.wires right).sig != .iota then
        exact .error .expectedIota
      else if leftOuter :
          source.val.Encloses (source.val.wires left).scope
            (source.val.wires right).scope then
        match requireJoinPolarity source orientation
            (source.val.wires right).scope with
        | .error error => exact .error error
        | .ok polarity =>
            match accepted :
                ConcreteWireQuantifier.joinIota source left right with
            | .error error => exact .error (.concreteRejected error)
            | .ok result =>
                exact .ok
                  (AppliedWireJoin.mk result.checked
                    { outer := left
                      inner := right
                      side := Or.inl ⟨rfl, rfl⟩
                      comparable := leftOuter
                      polarity := polarity
                      result := result
                      accepted := accepted
                      targetExact := rfl })
      else if rightOuter :
          source.val.Encloses (source.val.wires right).scope
            (source.val.wires left).scope then
        match requireJoinPolarity source orientation
            (source.val.wires left).scope with
        | .error error => exact .error error
        | .ok polarity =>
            match accepted :
                ConcreteWireQuantifier.joinIota source right left with
            | .error error => exact .error (.concreteRejected error)
            | .ok result =>
                exact .ok
                  (AppliedWireJoin.mk result.checked
                    { outer := right
                      inner := left
                      side := Or.inr ⟨rfl, rfl⟩
                      comparable := rightOuter
                      polarity := polarity
                      result := result
                      accepted := accepted
                      targetExact := rfl })
      else
        exact .error .incomparableScopes

/-- Temporary iota partition is sound over every premodel. -/
theorem iota_sever_sound
    {source : CheckedDiagram definitions}
    (orientation : Orientation)
    (wire : source.val.WireId)
    (keep : List (CEndpoint source.val.nodeCount))
    (applied :
      AppliedWireSever source (.iota orientation wire keep))
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    Directed orientation
      (denoteChecked pre definitionEnv source)
      (denoteChecked pre definitionEnv applied.target) := by
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

/-- Temporary iota merge is sound over every premodel. -/
theorem iota_join_sound
    {source : CheckedDiagram definitions}
    (orientation : Orientation)
    (left right : source.val.WireId)
    (applied :
      AppliedWireJoin source (.iota orientation left right))
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    Directed orientation
      (denoteChecked pre definitionEnv source)
      (denoteChecked pre definitionEnv applied.target) := by
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

end WireQuantifier

export WireQuantifier
  (WireSeverInput WireJoinInput WireQuantifierError
    AppliedWireSever AppliedWireJoin applyWireSever applyWireJoin
    iota_sever_sound iota_join_sound)

end VisualProof
