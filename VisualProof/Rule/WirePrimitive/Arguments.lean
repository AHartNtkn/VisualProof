import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsCylindrificationRecursiveComplete
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
  private source_removed_exact : result.sourceRemovedWires = [wire]

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
  private source_removed_exact : result.sourceRemovedWires = [wire]
  private local_count_exact : result.spec.localCount = 0
  private permutation_receipt :
    ValidPermutationReceipt sourceArguments.length permutation
  private target_arguments_exact :
    result.targetArguments = permute sourceArguments permutation
  private arguments_exact :
    ∀ site : Fin result.sites.sites.length,
      result.spec.arguments site =
        existingReferences
          (permute (result.sites.sites.get site).arguments permutation)
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
  private source_removed_exact : result.sourceRemovedWires = [wire]
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

/-- The exact source relation argument vector selected by the checker. -/
def sourceArgumentList
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {newArgument : Sig}
    (applied : AppliedArityShift source wire newArgument) : List Sig :=
  applied.sourceArguments

/-- Exact relation signature of the live source wire. -/
theorem sourceWire_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {newArgument : Sig}
    (applied : AppliedArityShift source wire newArgument) :
    (source.val.wires wire).sig = .rel applied.sourceArgumentList :=
  applied.sourceSignature

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

/-- Arity shift appends exactly one argument signature. -/
theorem targetArguments_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {newArgument : Sig}
    (applied : AppliedArityShift source wire newArgument) :
    applied.result.targetArguments =
      applied.sourceArgumentList ++ [newArgument] := by
  unfold sourceArgumentList
  calc
    applied.result.targetArguments =
        ConcreteWirePrimitive.insertAt applied.sourceArguments
          applied.ledger.insertion.position newArgument :=
      applied.ledger.insertion.largerExact.symm
    _ = ConcreteWirePrimitive.insertAt applied.sourceArguments
          applied.sourceArguments.length newArgument := by
      rw [applied.ledger.position_exact]
    _ = applied.sourceArguments ++ [newArgument] := by
      induction applied.sourceArguments with
      | nil => rfl
      | cons head tail induction =>
          simp [ConcreteWirePrimitive.insertAt, induction]

/-- Exact relation signature of the fresh live wire. -/
theorem targetWire_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {newArgument : Sig}
    (applied : AppliedArityShift source wire newArgument) :
    (applied.target.val.wires applied.targetWire).sig =
      .rel (applied.sourceArgumentList ++ [newArgument]) := by
  change
    (applied.result.checked.val.wires applied.result.targetWire).sig =
      .rel (applied.sourceArgumentList ++ [newArgument])
  rw [applied.result.targetWire_signature,
    applied.targetArguments_exact]

/-- Exact target image of a retained source wire. -/
def transportRetainedWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {newArgument : Sig}
    (applied : AppliedArityShift source wire newArgument)
    (sourceWire : source.val.WireId)
    (different : sourceWire ≠ wire) :
    applied.target.val.WireId :=
  applied.result.retainedWire sourceWire (by
    unfold ConcreteWireQuantifier.Internal.retainedWires
    apply List.mem_filter.mpr
    refine ⟨Data.Finite.mem_allFin sourceWire, ?_⟩
    rw [applied.source_removed_exact]
    simp [different])

/-- Arity-shift ambient transport preserves the exact wire signature. -/
theorem transportRetainedWire_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {newArgument : Sig}
    (applied : AppliedArityShift source wire newArgument)
    (sourceWire : source.val.WireId)
    (different : sourceWire ≠ wire) :
    (applied.target.val.wires
        (applied.transportRetainedWire sourceWire different)).sig =
      (source.val.wires sourceWire).sig :=
  applied.result.retainedWire_signature sourceWire _

/-- The image of a retained ambient wire cannot be the fresh live head. -/
theorem transportRetainedWire_ne_targetWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {newArgument : Sig}
    (applied : AppliedArityShift source wire newArgument)
    (sourceWire : source.val.WireId)
    (different : sourceWire ≠ wire) :
    applied.transportRetainedWire sourceWire different ≠
      applied.targetWire :=
  applied.result.retainedWire_ne_targetWire sourceWire _

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

/-- The exact source relation argument vector selected by the permutation
checker. -/
def sourceArgumentList
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (applied : AppliedArgPermute source wire permutation) : List Sig :=
  applied.sourceArguments

/-- Exact relation signature of the live permutation source wire. -/
theorem sourceWire_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (applied : AppliedArgPermute source wire permutation) :
    (source.val.wires wire).sig = .rel applied.sourceArgumentList :=
  applied.sourceSignature

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

/-- Construction-owned node carrier for the accepted permutation. -/
def nodeEquiv
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (applied : AppliedArgPermute source wire permutation) :
    Data.Finite.FiniteEquiv source.val.NodeId applied.target.val.NodeId :=
  applied.result.nodeEquiv applied.targetSites

/-- Construction-owned wire carrier for the head-only accepted
permutation. -/
def wireEquiv
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (applied : AppliedArgPermute source wire permutation) :
    Data.Finite.FiniteEquiv source.val.WireId applied.target.val.WireId :=
  applied.result.wireEquivHeadOnly applied.source_removed_exact
    applied.local_count_exact

/-- Construction-owned inverse permutation with no missing-index
fallback. -/
def inversePermutation
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (applied : AppliedArgPermute source wire permutation) : List Nat :=
  applied.permutation_receipt.inverse

/-- The executable checker accepts the construction-owned inverse. -/
theorem inversePermutation_valid
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (applied : AppliedArgPermute source wire permutation) :
    validPermutation applied.sourceArguments.length
      applied.inversePermutation = true :=
  applied.permutation_receipt.inverse_valid

/-- The checked target relation signature is exactly the receipt-owned
forward permutation. -/
theorem targetArguments_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (applied : AppliedArgPermute source wire permutation) :
    applied.result.targetArguments =
      permute applied.sourceArguments permutation :=
  applied.target_arguments_exact

/-- Exact signature of the checked permutation target wire. -/
theorem targetWire_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (applied : AppliedArgPermute source wire permutation) :
    (applied.target.val.wires applied.targetWire).sig =
      .rel (permute applied.sourceArgumentList permutation) := by
  change (applied.result.checked.val.wires applied.result.targetWire).sig = _
  rw [applied.result.targetWire_signature,
    applied.targetArguments_exact]
  rfl

/-- A transported application of the receipt-owned inverse restores the
original relation argument vector exactly. -/
theorem inverseTargetArguments_exact
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {permutation : List Nat}
    (forward : AppliedArgPermute planned forwardWire permutation)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgPermute real backwardWire
      forward.inversePermutation)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire) :
    backward.result.targetArguments = forward.sourceArgumentList := by
  have signatureExact := targetIso.wire_signature backwardWire
  rw [wireExact, forward.targetWire_signature,
    backward.sourceWire_signature] at signatureExact
  have argumentsExact : backward.sourceArgumentList =
      permute forward.sourceArgumentList permutation := by
    exact Sig.rel.inj signatureExact.symm
  unfold sourceArgumentList at argumentsExact ⊢
  rw [backward.targetArguments_exact, argumentsExact]
  exact forward.permutation_receipt.permute_inverse
    forward.sourceArgumentList rfl

/-- Region carrier of the transported inverse permutation run. -/
def inverseTransportRegionEquiv
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {permutation : List Nat}
    (forward : AppliedArgPermute planned forwardWire permutation)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgPermute real backwardWire
      forward.inversePermutation)
    (targetIso : ConcreteIso real.val forward.target.val) :
    Data.Finite.FiniteEquiv backward.target.val.RegionId
      planned.val.RegionId :=
  forward.result.inverseTransportRegionEquiv backward.result targetIso

/-- Node carrier of the transported inverse permutation run. -/
def inverseTransportNodeEquiv
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {permutation : List Nat}
    (forward : AppliedArgPermute planned forwardWire permutation)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgPermute real backwardWire
      forward.inversePermutation)
    (targetIso : ConcreteIso real.val forward.target.val) :
    Data.Finite.FiniteEquiv backward.target.val.NodeId planned.val.NodeId :=
  forward.result.inverseTransportNodeEquiv backward.result
    forward.targetSites backward.targetSites targetIso

/-- Wire carrier of the transported inverse permutation run. -/
def inverseTransportWireEquiv
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {permutation : List Nat}
    (forward : AppliedArgPermute planned forwardWire permutation)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgPermute real backwardWire
      forward.inversePermutation)
    (targetIso : ConcreteIso real.val forward.target.val) :
    Data.Finite.FiniteEquiv backward.target.val.WireId planned.val.WireId :=
  forward.result.inverseTransportWireEquivHeadOnly backward.result
    forward.source_removed_exact forward.local_count_exact
    backward.source_removed_exact backward.local_count_exact targetIso

/-- The transported inverse region carrier sends the rebuilt root exactly
back to the planned root. -/
theorem inverseTransport_root
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {permutation : List Nat}
    (forward : AppliedArgPermute planned forwardWire permutation)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgPermute real backwardWire
      forward.inversePermutation)
    (targetIso : ConcreteIso real.val forward.target.val) :
    forward.inverseTransportRegionEquiv backward targetIso
        backward.target.val.root = planned.val.root := by
  unfold inverseTransportRegionEquiv
  change forward.result.regionEquiv.symm
    (targetIso.regions
      (backward.result.regionEquiv.symm backward.target.val.root)) = _
  have backwardRoot : backward.target.val.root =
      backward.result.regionEquiv real.val.root := by
    exact backward.result.targetRoot_exact.trans
      (backward.result.regionImage_exact real.val.root)
  rw [backwardRoot]
  have backwardCancel :=
    backward.result.regionEquiv.left_inv real.val.root
  change backward.result.regionEquiv.invFun
      (backward.result.regionEquiv real.val.root) = real.val.root
    at backwardCancel
  calc
    forward.result.regionEquiv.symm
        (targetIso.regions
          (backward.result.regionEquiv.symm
            (backward.result.regionEquiv real.val.root))) =
        forward.result.regionEquiv.symm
          (targetIso.regions real.val.root) :=
      congrArg (fun value => forward.result.regionEquiv.symm
        (targetIso.regions value)) backwardCancel
    _ = forward.result.regionEquiv.symm forward.target.val.root := by
      rw [targetIso.root]
    _ = forward.result.regionEquiv.symm
        (forward.result.regionEquiv planned.val.root) := by
      congr 1
      exact forward.result.targetRoot_exact.trans
        (forward.result.regionImage_exact planned.val.root)
    _ = planned.val.root := forward.result.regionEquiv.left_inv _

/-- Region tables commute with the transported inverse carrier. -/
theorem inverseTransport_region_table
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {permutation : List Nat}
    (forward : AppliedArgPermute planned forwardWire permutation)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgPermute real backwardWire
      forward.inversePermutation)
    (targetIso : ConcreteIso real.val forward.target.val)
    (region : backward.target.val.RegionId) :
    planned.val.regions
        (forward.inverseTransportRegionEquiv backward targetIso region) =
      (backward.target.val.regions region).rename
        (forward.inverseTransportRegionEquiv backward targetIso) := by
  let realRegion := backward.result.regionEquiv.symm region
  have backwardData := backward.result.regionImage_data realRegion
  have backwardRegionExact : backward.result.regionEquiv realRegion = region :=
    backward.result.regionEquiv.right_inv region
  rw [backwardRegionExact] at backwardData
  have backwardDataPublic : backward.target.val.regions region =
      (real.val.regions realRegion).rename backward.result.regionEquiv := by
    exact backwardData
  have middleData := targetIso.region_table realRegion
  have plannedData := forward.result.regionImage_data
    (forward.result.regionEquiv.symm (targetIso.regions realRegion))
  have plannedRegionExact :
      forward.result.regionEquiv
          (forward.result.regionEquiv.symm (targetIso.regions realRegion)) =
        targetIso.regions realRegion :=
    forward.result.regionEquiv.right_inv _
  rw [plannedRegionExact] at plannedData
  unfold inverseTransportRegionEquiv
  change planned.val.regions
      (forward.result.regionEquiv.symm (targetIso.regions realRegion)) = _
  rw [backwardDataPublic]
  have middleRelation :
      (real.val.regions realRegion).rename targetIso.regions =
        (planned.val.regions
          (forward.result.regionEquiv.symm
            (targetIso.regions realRegion))).rename
          forward.result.regionEquiv :=
    middleData.symm.trans plannedData
  cases realData : real.val.regions realRegion with
  | sheet =>
      cases plannedDataExact : planned.val.regions
          (forward.result.regionEquiv.symm
            (targetIso.regions realRegion)) with
      | sheet => rfl
      | cut parent =>
          rw [realData, plannedDataExact] at middleRelation
          contradiction
  | cut realParent =>
      cases plannedDataExact : planned.val.regions
          (forward.result.regionEquiv.symm
            (targetIso.regions realRegion)) with
      | sheet =>
          rw [realData, plannedDataExact] at middleRelation
          contradiction
      | cut plannedParent =>
          rw [realData, plannedDataExact] at middleRelation
          simp only [CRegion.rename] at middleRelation
          have parentRelation : targetIso.regions realParent =
              forward.result.regionEquiv plannedParent :=
            CRegion.cut.inj middleRelation
          congr 1
          unfold ConcreteWirePrimitive.ArgumentResult.inverseTransportRegionEquiv
          change plannedParent = forward.result.regionEquiv.symm
            (targetIso.regions
              (backward.result.regionEquiv.symm
                (backward.result.regionEquiv realParent)))
          have backwardParentCancel :=
            backward.result.regionEquiv.left_inv realParent
          change backward.result.regionEquiv.invFun
              (backward.result.regionEquiv realParent) = realParent
            at backwardParentCancel
          calc
            plannedParent = forward.result.regionEquiv.symm
                (targetIso.regions realParent) :=
              (forward.result.regionEquiv.left_inv plannedParent).symm.trans
                (congrArg forward.result.regionEquiv.symm
                  parentRelation).symm
            _ = forward.result.regionEquiv.symm
                (targetIso.regions
                  (backward.result.regionEquiv.symm
                    (backward.result.regionEquiv realParent))) :=
              congrArg (fun value => forward.result.regionEquiv.symm
                (targetIso.regions value)) backwardParentCancel.symm

/-- Every generated application uses the receipt-owned permuted attachment
tuple at its exact source-site position. -/
theorem siteArguments_exact
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (applied : AppliedArgPermute source wire permutation)
    (site : Fin applied.result.sites.sites.length) :
    applied.result.spec.arguments site =
      existingReferences
        (permute (applied.result.sites.sites.get site).arguments
          permutation) :=
  applied.arguments_exact site

/-- Every source site has the exact relation arity stored by the accepted
permutation receipt. -/
theorem sourceSiteArgumentLength
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (applied : AppliedArgPermute source wire permutation)
    (site : Fin applied.result.sites.sites.length) :
    (applied.result.sites.sites.get site).arguments.length =
      applied.sourceArguments.length := by
  exact (applied.result.sites.sites.get site).arguments_length.trans
    (congrArg List.length
      (ConcreteWirePrimitive.appliedSite_arguments_eq_relationArguments
        applied.sourceArguments applied.sourceSignature
        (applied.result.sites.sites.get site)))

/-- Exact ambient source wire selected at one generated permutation output
position. -/
def sourceArgumentWire
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (applied : AppliedArgPermute source wire permutation)
    (site : Fin applied.result.sites.sites.length)
    (position : Fin applied.sourceArguments.length) : source.val.WireId :=
  (applied.result.sites.sites.get site).arguments.get
    (Fin.cast (applied.sourceSiteArgumentLength site).symm
      (applied.permutation_receipt.forwardPosition position))

/-- Generated permutation argument endpoints are owned by the canonical
checked image of their exact proof-indexed source attachment. -/
theorem generatedArgument_endpointOwner
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (applied : AppliedArgPermute source wire permutation)
    (site : Fin applied.result.sites.sites.length)
    (position : Fin applied.sourceArguments.length) :
    applied.target.val.endpointOwner?
        ⟨applied.result.targetNode site, .arg position.val⟩ =
      some (applied.wireEquiv
        (applied.sourceArgumentWire site position)) := by
  let sourceSite := applied.result.sites.sites.get site
  have siteLength : sourceSite.arguments.length =
      applied.sourceArguments.length :=
    applied.sourceSiteArgumentLength site
  have targetBound : position.val <
      applied.result.targetArguments.length := by
    rw [applied.target_arguments_exact,
      applied.permutation_receipt.permute_length applied.sourceArguments rfl]
    exact position.isLt
  have outputBound : position.val <
      (permute sourceSite.arguments permutation).length := by
    rw [applied.permutation_receipt.permute_length sourceSite.arguments
      siteLength]
    exact position.isLt
  have selected :
      (applied.result.spec.arguments site)[position.val]? =
        some (.existing (applied.sourceArgumentWire site position)) := by
    rw [applied.arguments_exact site]
    unfold existingReferences
    change
      (List.map ArgumentReference.existing
        (permute sourceSite.arguments permutation))[position.val]? = _
    have mappedBound : position.val <
        (List.map
          (ArgumentReference.existing
            (localCount := applied.result.spec.localCount))
          (permute sourceSite.arguments permutation)).length := by
      simpa using outputBound
    rw [List.getElem?_eq_getElem mappedBound]
    simp only [List.getElem_map, Option.some.injEq,
      ArgumentReference.existing.injEq]
    simpa [AppliedArgPermute.sourceArgumentWire,
      List.get_eq_getElem] using
        (applied.permutation_receipt.permute_get sourceSite.arguments
          siteLength position)
  have sourceBound :
      (Fin.cast siteLength.symm
        (applied.permutation_receipt.forwardPosition position)).val <
          sourceSite.arguments.length :=
    (Fin.cast siteLength.symm
      (applied.permutation_receipt.forwardPosition position)).isLt
  have different : applied.sourceArgumentWire site position ≠ wire := by
    exact sourceSite.argument_ne_head _ sourceBound
  have retained : applied.sourceArgumentWire site position ∉
      applied.result.sourceRemovedWires := by
    rw [applied.source_removed_exact]
    simpa [different]
  have owner := applied.result.generatedArgument_endpointOwner site
    position.val targetBound (applied.sourceArgumentWire site position)
    selected retained
  simpa [AppliedArgPermute.wireEquiv,
    ConcreteWirePrimitive.ArgumentResult.wireEquivHeadOnly,
    ConcreteWirePrimitive.ArgumentResult.wireImageHeadOnly, different]
    using owner

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

/-- Exact target image of any source wire through argument drop.  The acted
head is replaced by the checked target head; every other wire is transported
by the replacement receipt's retained-wire map. -/
def transportWire
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position)
    (sourceWire : source.val.WireId) :
    applied.target.val.WireId :=
  if same : sourceWire = wire then
    applied.targetWire
  else
    applied.result.retainedWireImage sourceWire (by
      rw [applied.source_removed_exact]
      simpa [same])

/-- The exact ordered attachment tuple erased by drop, transported into the
checked target.  Positions and repeated aliases are preserved. -/
def targetAttachments
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedArgDrop source orientation wire position) :
    List applied.target.val.WireId :=
  applied.attachments.map applied.transportWire

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
      (AppliedArityShift source wire newArgument) := by
  match accepted :
      ConcreteWirePrimitive.arityShift source wire newArgument with
  | .error error => exact .error (.concreteRejected error)
  | .ok result =>
      match sourceSignature : (source.val.wires wire).sig with
      | .iota => exact .error .semanticLedgerRejected
      | .rel sourceArguments =>
          match ledgerAccepted :
              ArgumentsSemantics.checkScopedArityShiftLedger result
                sourceArguments sourceSignature newArgument with
          | none =>
              have complete :=
                ArgumentsSemantics.checkScopedArityShiftLedger_complete_of_accepted
                  sourceArguments sourceSignature newArgument result accepted
              simp [ledgerAccepted] at complete
          | some ledger =>
              exact .ok
                ⟨result, sourceArguments, sourceSignature, ledger,
                  ConcreteWirePrimitive.arityShift_sourceRemovedWires_exact
                    source wire newArgument result accepted⟩

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
      (AppliedArgPermute source wire permutation) :=
  match accepted :
      ConcreteWirePrimitive.argPermute source wire permutation with
  | .error error => .error (.concreteRejected error)
  | .ok result =>
      match sourceSignature : (source.val.wires wire).sig with
      | .iota => .error .semanticLedgerRejected
      | .rel sourceArguments =>
          match ArgumentsSemantics.checkPermutationLedger result
              sourceArguments sourceSignature permutation with
          | none => .error .semanticLedgerRejected
          | some ledger =>
              .ok
                ⟨result, sourceArguments, sourceSignature,
                  ConcreteWirePrimitive.argPermute_sourceRemovedWires_exact
                    source wire permutation result accepted,
                  ConcreteWirePrimitive.argPermute_localCount_exact source
                    wire permutation result accepted,
                  validPermutation_receipt sourceArguments.length permutation
                    (ConcreteWirePrimitive.argPermute_valid_exact source wire
                      sourceArguments sourceSignature permutation result
                      accepted),
                  ConcreteWirePrimitive.argPermute_targetArguments_exact
                    source wire sourceArguments sourceSignature permutation
                    result accepted,
                  ConcreteWirePrimitive.argPermute_arguments_exact source
                    wire sourceArguments sourceSignature permutation result
                    accepted,
                  ledger⟩

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
  match accepted : ConcreteWirePrimitive.argDrop source wire position with
  | .error error => throw (.concreteRejected error)
  | .ok result =>
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
          let sourceRemovedExact :=
            ConcreteWirePrimitive.argDrop_sourceRemovedWires_exact
              source wire position result accepted
          pure
            ⟨attachments, gate, result, sourceArguments, sourceSignature,
              sourceRemovedExact, ledger, semantics⟩

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
