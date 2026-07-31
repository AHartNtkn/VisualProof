import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsCylindrificationFactorization
import VisualProof.Rule.Tag
import VisualProof.Rule.Structural

namespace VisualProof

namespace WirePrimitive

namespace Arguments

open ConcreteWirePrimitive

/-- Stable public refusal outcomes for argument-plumbing primitives. -/
inductive WireArgumentError
  | dropRequiresNegative
  | dropBackwardRequiresPositive
  | extendRequiresPositive
  | extendBackwardRequiresNegative
  | scopeCompilationFailed
  | semanticLedgerRejected
  | concreteRejected (error : ConcreteWirePrimitive.ArgumentError)
  deriving Repr, DecidableEq

private def optionToExcept
    (error : WireArgumentError) : Option α → Except WireArgumentError α
  | none => .error error
  | some value => .ok value

private def joinPolarityLegal
    (orientation : Orientation) (depth : Nat) : Bool :=
  match orientation with
  | .forward => decide (depth % 2 = 1)
  | .backward => decide (depth % 2 = 0)

private def severPolarityLegal
    (orientation : Orientation) (depth : Nat) : Bool :=
  match orientation with
  | .forward => decide (depth % 2 = 0)
  | .backward => decide (depth % 2 = 1)

private structure CheckedDropPolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId) where
  compiled :
    SiteCompilation source (source.val.wires wire).scope
  legal :
    joinPolarityLegal orientation compiled.frame.context.cutDepth = true

private structure CheckedExtendPolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId) where
  compiled :
    SiteCompilation source (source.val.wires wire).scope
  legal :
    severPolarityLegal orientation compiled.frame.context.cutDepth = true

private def requireDropPolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId) :
    Except WireArgumentError
      (CheckedDropPolarity source orientation wire) := by
  match compileSite? source (source.val.wires wire).scope with
  | none => exact .error .scopeCompilationFailed
  | some compiled =>
      if legal :
          joinPolarityLegal orientation
            compiled.frame.context.cutDepth then
        exact .ok ⟨compiled, legal⟩
      else
        exact .error <|
          match orientation with
          | .forward => .dropRequiresNegative
          | .backward => .dropBackwardRequiresPositive

private def requireExtendPolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId) :
    Except WireArgumentError
      (CheckedExtendPolarity source orientation wire) := by
  match compileSite? source (source.val.wires wire).scope with
  | none => exact .error .scopeCompilationFailed
  | some compiled =>
      if legal :
          severPolarityLegal orientation
            compiled.frame.context.cutDepth then
        exact .ok ⟨compiled, legal⟩
      else
        exact .error <|
          match orientation with
          | .forward => .extendRequiresPositive
          | .backward => .extendBackwardRequiresNegative

/--
The merged checker exempts exactly one shared attachment visible at the acted
wire's scope.  Empty site families have no such attachment and use the
ordinary polarity gate.
-/
private def uniformVisibleAttachment
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (attachments : List source.val.WireId) : Bool :=
  match attachments with
  | [] => false
  | first :: rest =>
      rest.all (· == first) &&
        decide
          (source.val.Encloses
            (source.val.wires first).scope
            (source.val.wires wire).scope)

private inductive DropGate
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId)
    (attachments : List source.val.WireId)
  | uniform :
      uniformVisibleAttachment source wire attachments = true →
      DropGate source orientation wire attachments
  | gated :
      uniformVisibleAttachment source wire attachments = false →
      CheckedDropPolarity source orientation wire →
      DropGate source orientation wire attachments

private inductive ExtendGate
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId)
    (attachments : List source.val.WireId)
  | uniform :
      uniformVisibleAttachment source wire attachments = true →
      ExtendGate source orientation wire attachments
  | gated :
      uniformVisibleAttachment source wire attachments = false →
      CheckedExtendPolarity source orientation wire →
      ExtendGate source orientation wire attachments

private def checkDropGate
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId)
    (attachments : List source.val.WireId) :
    Except WireArgumentError
      (DropGate source orientation wire attachments) := by
  if uniform :
      uniformVisibleAttachment source wire attachments = true then
    exact .ok (.uniform uniform)
  else
    match requireDropPolarity source orientation wire with
    | .error error => exact .error error
    | .ok polarity =>
        have notUniform :
            uniformVisibleAttachment source wire attachments = false := by
          cases value :
              uniformVisibleAttachment source wire attachments <;>
            simp_all
        exact .ok
          (.gated notUniform polarity)

private def checkExtendGate
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId)
    (attachments : List source.val.WireId) :
    Except WireArgumentError
      (ExtendGate source orientation wire attachments) := by
  if uniform :
      uniformVisibleAttachment source wire attachments = true then
    exact .ok (.uniform uniform)
  else
    match requireExtendPolarity source orientation wire with
    | .error error => exact .error error
    | .ok polarity =>
        have notUniform :
            uniformVisibleAttachment source wire attachments = false := by
          cases value :
              uniformVisibleAttachment source wire attachments <;>
            simp_all
        exact .ok
          (.gated notUniform polarity)

private inductive DropSemanticReceipt
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (ledger :
      ArgumentsSemantics.DropLedger result sourceArguments)
  | uniform
      (fixed : ArgumentsSemantics.FixedDropLedger ledger)
  | gated
      (polarity : CheckedDropPolarity source orientation wire)

private inductive ExtendSemanticReceipt
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {result : ArgumentResult source wire}
    {sourceArguments : List Sig}
    (ledger :
      ArgumentsSemantics.ExtendLedger result sourceArguments)
  | uniform
      (fixed : ArgumentsSemantics.FixedExtendLedger ledger)
  | gated
      (polarity : CheckedExtendPolarity source orientation wire)

structure AppliedArityShift
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (newArgument : Sig) where
  private mk ::
  private result : ArgumentResult source wire
  private sourceArguments : List Sig
  private sourceSignature :
    (source.val.wires wire).sig = .rel sourceArguments
  private ledger :
    ArgumentsSemantics.ScopedArityShiftLedger result sourceArguments
      newArgument

structure AppliedArityUnshift
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat) where
  private mk ::
  private result : ArgumentResult source wire
  private sourceArguments : List Sig
  private sourceSignature :
    (source.val.wires wire).sig = .rel sourceArguments
  private fixedSignature : Sig
  private ledger :
    ArgumentsSemantics.ScopedArityUnshiftLedger result sourceArguments
      fixedSignature

structure AppliedArgPermute
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (permutation : List Nat) where
  private mk ::
  private result : ArgumentResult source wire
  private sourceArguments : List Sig
  private sourceSignature :
    (source.val.wires wire).sig = .rel sourceArguments
  private ledger :
    ArgumentsSemantics.PermutationLedger result sourceArguments

structure AppliedArgDuplicate
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat) where
  private mk ::
  private result : ArgumentResult source wire
  private sourceArguments : List Sig
  private sourceSignature :
    (source.val.wires wire).sig = .rel sourceArguments
  private ledger :
    ArgumentsSemantics.DuplicateLedger result sourceArguments

structure AppliedArgContract
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat) where
  private mk ::
  private result : ArgumentResult source wire
  private sourceArguments : List Sig
  private sourceSignature :
    (source.val.wires wire).sig = .rel sourceArguments
  private ledger :
    ArgumentsSemantics.ContractLedger result sourceArguments

structure AppliedArgDrop
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId)
    (position : Nat) where
  private mk ::
  private attachments : List source.val.WireId
  private gate : DropGate source orientation wire attachments
  private result : ArgumentResult source wire
  private sourceArguments : List Sig
  private sourceSignature :
    (source.val.wires wire).sig = .rel sourceArguments
  private ledger :
    ArgumentsSemantics.DropLedger result sourceArguments
  private semantics :
    DropSemanticReceipt (orientation := orientation) (position := position)
      ledger

structure AppliedArgExtend
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId)
    (position : Nat)
    (newArgument : Sig)
    (attachments : List source.val.WireId) where
  private mk ::
  private gate : ExtendGate source orientation wire attachments
  private result : ArgumentResult source wire
  private sourceArguments : List Sig
  private sourceSignature :
    (source.val.wires wire).sig = .rel sourceArguments
  private ledger :
    ArgumentsSemantics.ExtendLedger result sourceArguments
  private semantics :
    ExtendSemanticReceipt (orientation := orientation) (position := position)
      ledger

namespace AppliedArityShift

def source
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {newArgument : Sig}
    (_ : AppliedArityShift source wire newArgument) := source

def target
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {newArgument : Sig}
    (applied : AppliedArityShift source wire newArgument) :=
  applied.result.target

/-- The replacement relation wire allocated by this checked rewrite. -/
def targetWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {newArgument : Sig}
    (applied : AppliedArityShift source wire newArgument) :
    applied.target.val.WireId :=
  applied.result.targetWire

/-- Exhaustive applied sites on the replacement relation wire. -/
def targetSites
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {newArgument : Sig}
    (applied : AppliedArityShift source wire newArgument) :
    AllAppliedSites applied.target applied.targetWire :=
  applied.ledger.frame.targetSites

def tag
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {newArgument : Sig}
    (_ : AppliedArityShift source wire newArgument) : StepTag :=
  .arityShift

end AppliedArityShift

namespace AppliedArityUnshift

def source
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (_ : AppliedArityUnshift source wire position) := source

def target
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArityUnshift source wire position) :=
  applied.result.target

def targetWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArityUnshift source wire position) :
    applied.target.val.WireId :=
  applied.result.targetWire

def targetSites
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArityUnshift source wire position) :
    AllAppliedSites applied.target applied.targetWire :=
  applied.ledger.frame.targetSites

def tag
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (_ : AppliedArityUnshift source wire position) : StepTag :=
  .arityUnshift

end AppliedArityUnshift

namespace AppliedArgPermute

def source
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (_ : AppliedArgPermute source wire permutation) := source

def target
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (applied : AppliedArgPermute source wire permutation) :=
  applied.result.target

def targetWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (applied : AppliedArgPermute source wire permutation) :
    applied.target.val.WireId :=
  applied.result.targetWire

def targetSites
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (applied : AppliedArgPermute source wire permutation) :
    AllAppliedSites applied.target applied.targetWire :=
  applied.ledger.factorization.targetSites

def tag
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (_ : AppliedArgPermute source wire permutation) : StepTag :=
  .argPermute

end AppliedArgPermute

namespace AppliedArgDuplicate

def source
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (_ : AppliedArgDuplicate source wire position) := source

def target
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position) :=
  applied.result.target

def targetWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position) :
    applied.target.val.WireId :=
  applied.result.targetWire

def targetSites
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDuplicate source wire position) :
    AllAppliedSites applied.target applied.targetWire :=
  applied.ledger.factorization.targetSites

def tag
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (_ : AppliedArgDuplicate source wire position) : StepTag :=
  .argDuplicate

end AppliedArgDuplicate

namespace AppliedArgContract

def source
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (_ : AppliedArgContract source wire position) := source

def target
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgContract source wire position) :=
  applied.result.target

def targetWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgContract source wire position) :
    applied.target.val.WireId :=
  applied.result.targetWire

def targetSites
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgContract source wire position) :
    AllAppliedSites applied.target applied.targetWire :=
  applied.ledger.factorization.targetSites

def tag
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {position : Nat}
    (_ : AppliedArgContract source wire position) : StepTag :=
  .argContract

end AppliedArgContract

namespace AppliedArgDrop

def source
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (_ : AppliedArgDrop source orientation wire position) := source

def target
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position) :=
  applied.result.target

def targetWire
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position) :
    applied.target.val.WireId :=
  applied.result.targetWire

def targetSites
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position) :
    AllAppliedSites applied.target applied.targetWire :=
  applied.ledger.factorization.targetSites

def tag
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (_ : AppliedArgDrop source orientation wire position) : StepTag :=
  .argDrop

end AppliedArgDrop

namespace AppliedArgExtend

def source
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (_ :
      AppliedArgExtend source orientation wire position newArgument
        attachments) := source

def target
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied :
      AppliedArgExtend source orientation wire position newArgument
        attachments) :=
  applied.result.target

def targetWire
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied :
      AppliedArgExtend source orientation wire position newArgument
        attachments) : applied.target.val.WireId :=
  applied.result.targetWire

def targetSites
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (applied :
      AppliedArgExtend source orientation wire position newArgument
        attachments) :
    AllAppliedSites applied.target applied.targetWire :=
  applied.ledger.factorization.targetSites

def tag
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    {newArgument : Sig}
    {attachments : List source.val.WireId}
    (_ :
      AppliedArgExtend source orientation wire position newArgument
        attachments) : StepTag :=
  .argExtend

end AppliedArgExtend

def applyArityShift
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (newArgument : Sig) :
    Except WireArgumentError
      (AppliedArityShift source wire newArgument) := do
  let result ←
    (ConcreteWirePrimitive.arityShift source wire newArgument).mapError
      .concreteRejected
  match sourceSignature : (source.val.wires wire).sig with
  | .iota => throw .semanticLedgerRejected
  | .rel sourceArguments =>
      let ledger ←
        optionToExcept .semanticLedgerRejected <|
          ArgumentsSemantics.checkScopedArityShiftLedger result
            sourceArguments sourceSignature newArgument
      pure ⟨result, sourceArguments, sourceSignature, ledger⟩

def applyArityUnshift
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat) :
    Except WireArgumentError
      (AppliedArityUnshift source wire position) := do
  let result ←
    (ConcreteWirePrimitive.arityUnshift source wire position).mapError
      .concreteRejected
  match sourceSignature : (source.val.wires wire).sig with
  | .iota => throw .semanticLedgerRejected
  | .rel sourceArguments =>
      match _fixedExact : sourceArguments[position]? with
      | none => throw .semanticLedgerRejected
      | some fixedSignature =>
          let ledger ←
            optionToExcept .semanticLedgerRejected <|
              ArgumentsSemantics.checkScopedArityUnshiftLedger result
                sourceArguments sourceSignature position fixedSignature
          pure
            ⟨result, sourceArguments, sourceSignature, fixedSignature,
              ledger⟩

def applyArgPermute
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (permutation : List Nat) :
    Except WireArgumentError
      (AppliedArgPermute source wire permutation) := do
  let result ←
    (ConcreteWirePrimitive.argPermute source wire permutation).mapError
      .concreteRejected
  match sourceSignature : (source.val.wires wire).sig with
  | .iota => throw .semanticLedgerRejected
  | .rel sourceArguments =>
      let ledger ←
        optionToExcept .semanticLedgerRejected <|
          ArgumentsSemantics.checkPermutationLedger result sourceArguments
            sourceSignature permutation
      pure ⟨result, sourceArguments, sourceSignature, ledger⟩

def applyArgDuplicate
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat) :
    Except WireArgumentError
      (AppliedArgDuplicate source wire position) := do
  let result ←
    (ConcreteWirePrimitive.argDuplicate source wire position).mapError
      .concreteRejected
  match sourceSignature : (source.val.wires wire).sig with
  | .iota => throw .semanticLedgerRejected
  | .rel sourceArguments =>
      let ledger ←
        optionToExcept .semanticLedgerRejected <|
          ArgumentsSemantics.checkDuplicateLedger result sourceArguments
            sourceSignature position
      pure ⟨result, sourceArguments, sourceSignature, ledger⟩

def applyArgContract
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat) :
    Except WireArgumentError
      (AppliedArgContract source wire position) := do
  let result ←
    (ConcreteWirePrimitive.argContract source wire position).mapError
      .concreteRejected
  match sourceSignature : (source.val.wires wire).sig with
  | .iota => throw .semanticLedgerRejected
  | .rel sourceArguments =>
      let ledger ←
        optionToExcept .semanticLedgerRejected <|
          ArgumentsSemantics.checkContractLedger result sourceArguments
            sourceSignature position
      pure ⟨result, sourceArguments, sourceSignature, ledger⟩

def applyArgDrop
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat)
    (orientation : Orientation) :
    Except WireArgumentError
      (AppliedArgDrop source orientation wire position) := do
  let result ←
    (ConcreteWirePrimitive.argDrop source wire position).mapError
      .concreteRejected
  let attachments :=
    result.sites.sites.filterMap fun site => site.arguments[position]?
  let gate ← checkDropGate source orientation wire attachments
  match sourceSignature : (source.val.wires wire).sig with
  | .iota => throw .semanticLedgerRejected
  | .rel sourceArguments =>
      let ledger ←
        optionToExcept .semanticLedgerRejected <|
          ArgumentsSemantics.checkDropLedger result sourceArguments
            sourceSignature position
      let semanticCheck :
          Except WireArgumentError
            (DropSemanticReceipt (orientation := orientation)
              (position := position) ledger) :=
        match gate with
        | .uniform _ =>
            match attachments with
            | [] => throw .semanticLedgerRejected
            | attachment :: _ => do
                let fixed ←
                  optionToExcept .semanticLedgerRejected <|
                    ArgumentsSemantics.checkFixedDropLedger ledger
                      attachment position
                pure (DropSemanticReceipt.uniform fixed)
        | .gated _ polarity =>
            pure (DropSemanticReceipt.gated polarity)
      let semantics ← semanticCheck
      pure
        ⟨attachments, gate, result, sourceArguments, sourceSignature,
          ledger, semantics⟩

def applyArgExtend
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat)
    (newArgument : Sig)
    (attachments : List source.val.WireId)
    (orientation : Orientation) :
    Except WireArgumentError
      (AppliedArgExtend source orientation wire position newArgument
        attachments) := do
  let result ←
    (ConcreteWirePrimitive.argExtend source wire position newArgument
      attachments).mapError .concreteRejected
  let gate ← checkExtendGate source orientation wire attachments
  match sourceSignature : (source.val.wires wire).sig with
  | .iota => throw .semanticLedgerRejected
  | .rel sourceArguments =>
      let ledger ←
        optionToExcept .semanticLedgerRejected <|
          ArgumentsSemantics.checkExtendLedger result sourceArguments
            sourceSignature position
      let semanticCheck :
          Except WireArgumentError
            (ExtendSemanticReceipt (orientation := orientation)
              (position := position) ledger) :=
        match gate with
        | .uniform _ =>
            match attachments with
            | [] => throw .semanticLedgerRejected
            | attachment :: _ => do
                let fixed ←
                  optionToExcept .semanticLedgerRejected <|
                    ArgumentsSemantics.checkFixedExtendLedger ledger
                      attachment position
                pure (ExtendSemanticReceipt.uniform fixed)
        | .gated _ polarity =>
            pure (ExtendSemanticReceipt.gated polarity)
      let semantics ← semanticCheck
      pure
        ⟨gate, result, sourceArguments, sourceSignature, ledger,
          semantics⟩

/-- Checked arity shift is a full-model cylindrification equivalence. -/
theorem arity_shift_sound
    {source : CheckedDiagram definitions}
    (wire : source.val.WireId)
    (newArgument : Sig)
    (applied : AppliedArityShift source wire newArgument)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    denoteChecked model.toPreModel definitionEnv applied.source ↔
      denoteChecked model.toPreModel definitionEnv applied.target :=
  applied.ledger.denotes model definitionEnv

/-- Checked arity unshift is the inverse full-model cylindrification. -/
theorem arity_unshift_sound
    {source : CheckedDiagram definitions}
    (wire : source.val.WireId)
    (position : Nat)
    (applied : AppliedArityUnshift source wire position)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    denoteChecked model.toPreModel definitionEnv applied.source ↔
      denoteChecked model.toPreModel definitionEnv applied.target :=
  applied.ledger.denotes model definitionEnv

/-- Checked argument permutation is a full-model equivalence. -/
theorem arg_permute_sound
    {source : CheckedDiagram definitions}
    (wire : source.val.WireId)
    (permutation : List Nat)
    (applied : AppliedArgPermute source wire permutation)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    denoteChecked model.toPreModel definitionEnv applied.source ↔
      denoteChecked model.toPreModel definitionEnv applied.target :=
  applied.ledger.denotes model definitionEnv

/-- Checked adjacent duplication is a full-model equivalence. -/
theorem arg_duplicate_sound
    {source : CheckedDiagram definitions}
    (wire : source.val.WireId)
    (position : Nat)
    (applied : AppliedArgDuplicate source wire position)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    denoteChecked model.toPreModel definitionEnv applied.source ↔
      denoteChecked model.toPreModel definitionEnv applied.target :=
  applied.ledger.denotes model definitionEnv

/-- Checked equal-adjacent contraction is a full-model equivalence. -/
theorem arg_contract_sound
    {source : CheckedDiagram definitions}
    (wire : source.val.WireId)
    (position : Nat)
    (applied : AppliedArgContract source wire position)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    denoteChecked model.toPreModel definitionEnv applied.source ↔
      denoteChecked model.toPreModel definitionEnv applied.target :=
  applied.ledger.denotes model definitionEnv

/--
Checked argument drop is either an ungated fixed-parameter equivalence or the
join-family implication selected by the checked orientation and cut parity.
-/
theorem arg_drop_sound
    {source : CheckedDiagram definitions}
    (wire : source.val.WireId)
    (position : Nat)
    (orientation : Orientation)
    (applied : AppliedArgDrop source orientation wire position)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    Directed orientation
      (denoteChecked model.toPreModel definitionEnv applied.source)
      (denoteChecked model.toPreModel definitionEnv applied.target) := by
  cases applied.semantics with
  | uniform fixed =>
      cases orientation with
      | forward =>
          exact (fixed.denotes model definitionEnv).mp
      | backward =>
          exact (fixed.denotes model definitionEnv).mpr
  | gated polarity =>
      have compiledExact :
          polarity.compiled =
            applied.ledger.factorization.sourceScope :=
        SiteCompilation.unique polarity.compiled
          applied.ledger.factorization.sourceScope
      cases orientation with
      | forward =>
          have legal :
              polarity.compiled.frame.context.cutDepth % 2 = 1 :=
            of_decide_eq_true (by
              simpa [joinPolarityLegal] using polarity.legal)
          rw [compiledExact] at legal
          exact
            (applied.ledger.directions model definitionEnv).2 legal
      | backward =>
          have legal :
              polarity.compiled.frame.context.cutDepth % 2 = 0 :=
            of_decide_eq_true (by
              simpa [joinPolarityLegal] using polarity.legal)
          rw [compiledExact] at legal
          exact
            (applied.ledger.directions model definitionEnv).1 legal

/--
Checked argument extension is either an ungated fixed-parameter equivalence
or the sever-family implication selected by orientation and cut parity.
-/
theorem arg_extend_sound
    {source : CheckedDiagram definitions}
    (wire : source.val.WireId)
    (position : Nat)
    (newArgument : Sig)
    (attachments : List source.val.WireId)
    (orientation : Orientation)
    (applied :
      AppliedArgExtend source orientation wire position newArgument
        attachments)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    Directed orientation
      (denoteChecked model.toPreModel definitionEnv applied.source)
      (denoteChecked model.toPreModel definitionEnv applied.target) := by
  cases applied.semantics with
  | uniform fixed =>
      cases orientation with
      | forward =>
          exact (fixed.denotes model definitionEnv).mp
      | backward =>
          exact (fixed.denotes model definitionEnv).mpr
  | gated polarity =>
      have compiledExact :
          polarity.compiled =
            applied.ledger.factorization.sourceScope :=
        SiteCompilation.unique polarity.compiled
          applied.ledger.factorization.sourceScope
      cases orientation with
      | forward =>
          have legal :
              polarity.compiled.frame.context.cutDepth % 2 = 0 :=
            of_decide_eq_true (by
              simpa [severPolarityLegal] using polarity.legal)
          rw [compiledExact] at legal
          exact
            (applied.ledger.directions model definitionEnv).1 legal
      | backward =>
          have legal :
              polarity.compiled.frame.context.cutDepth % 2 = 1 :=
            of_decide_eq_true (by
              simpa [severPolarityLegal] using polarity.legal)
          rw [compiledExact] at legal
          exact
            (applied.ledger.directions model definitionEnv).2 legal

end Arguments

export Arguments
  (WireArgumentError AppliedArityShift AppliedArityUnshift
    AppliedArgPermute AppliedArgDuplicate AppliedArgContract AppliedArgDrop
    AppliedArgExtend applyArityShift applyArityUnshift applyArgPermute
    applyArgDuplicate applyArgContract applyArgDrop applyArgExtend
    arity_shift_sound arity_unshift_sound arg_permute_sound
    arg_duplicate_sound arg_contract_sound arg_drop_sound arg_extend_sound)

end WirePrimitive

export WirePrimitive
  (WireArgumentError AppliedArityShift AppliedArityUnshift
    AppliedArgPermute AppliedArgDuplicate AppliedArgContract AppliedArgDrop
    AppliedArgExtend applyArityShift applyArityUnshift applyArgPermute
    applyArgDuplicate applyArgContract applyArgDrop applyArgExtend
    arity_shift_sound arity_unshift_sound arg_permute_sound
    arg_duplicate_sound arg_contract_sound arg_drop_sound arg_extend_sound)

end VisualProof
