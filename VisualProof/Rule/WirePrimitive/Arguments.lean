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

/-- Port image on a generated application node.  Source argument positions
are sent to the unique output positions selected by the accepted permutation
receipt; non-argument ports are fixed. -/
def generatedPortImage
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (applied : AppliedArgPermute source wire permutation) : CPort → CPort
  | .arg index =>
      if bound : index < applied.sourceArguments.length then
        .arg (applied.permutation_receipt.inversePosition
          ⟨index, bound⟩).val
      else
        .arg index
  | .head => .head
  | .identity index => .identity index

/-- Inverse port image on a generated application node. -/
def generatedPortInverse
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (applied : AppliedArgPermute source wire permutation) : CPort → CPort
  | .arg index =>
      if bound : index < applied.sourceArguments.length then
        .arg (applied.permutation_receipt.forwardPosition
          ⟨index, bound⟩).val
      else
        .arg index
  | .head => .head
  | .identity index => .identity index

/-- The generated port maps cancel on every source argument position. -/
theorem generatedPortInverse_image
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (applied : AppliedArgPermute source wire permutation)
    (position : Fin applied.sourceArguments.length) :
    applied.generatedPortInverse
        (applied.generatedPortImage (.arg position.val)) =
      .arg position.val := by
  unfold generatedPortImage generatedPortInverse
  simp only [position.isLt, dite_true]
  split
  · congr 1
    exact congrArg Fin.val
      (applied.permutation_receipt.forward_inversePosition position)
  · rename_i impossible
    exact (impossible
      (applied.permutation_receipt.inversePosition position).isLt).elim

/-- The generated port maps cancel on every target argument position. -/
theorem generatedPortImage_inverse
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (applied : AppliedArgPermute source wire permutation)
    (position : Fin applied.sourceArguments.length) :
    applied.generatedPortImage
        (applied.generatedPortInverse (.arg position.val)) =
      .arg position.val := by
  unfold generatedPortImage generatedPortInverse
  simp only [position.isLt, dite_true]
  split
  · congr 1
    exact congrArg Fin.val
      (applied.permutation_receipt.inverse_forwardPosition position)
  · rename_i impossible
    exact (impossible
      (applied.permutation_receipt.forwardPosition position).isLt).elim

/-- Generated port transport is a total left inverse, including irrelevant
out-of-arity ports on which both maps are the identity. -/
theorem generatedPortInverse_image_all
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (applied : AppliedArgPermute source wire permutation)
    (port : CPort) :
    applied.generatedPortInverse (applied.generatedPortImage port) =
      port := by
  cases port with
  | head => rfl
  | identity index => rfl
  | arg index =>
      by_cases bound : index < applied.sourceArguments.length
      · exact applied.generatedPortInverse_image ⟨index, bound⟩
      · simp [generatedPortImage, generatedPortInverse, bound]

/-- Generated port transport is a total right inverse. -/
theorem generatedPortImage_inverse_all
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (applied : AppliedArgPermute source wire permutation)
    (port : CPort) :
    applied.generatedPortImage (applied.generatedPortInverse port) =
      port := by
  cases port with
  | head => rfl
  | identity index => rfl
  | arg index =>
      by_cases bound : index < applied.sourceArguments.length
      · exact applied.generatedPortImage_inverse ⟨index, bound⟩
      · simp [generatedPortImage, generatedPortInverse, bound]

/-- Total endpoint image of an accepted argument permutation.  Generated
application nodes use the receipt-indexed port permutation; retained nodes
preserve their constructor-derived port. -/
def endpointImage
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (applied : AppliedArgPermute source wire permutation)
    (endpoint : CEndpoint source.val.nodeCount) :
    CEndpoint applied.target.val.nodeCount :=
  ⟨applied.nodeEquiv endpoint.node,
    if endpoint.node ∈
        ConcreteWirePrimitive.argumentSiteNodes applied.result.sites then
      applied.generatedPortImage endpoint.port
    else
      endpoint.port⟩

/-- Total inverse endpoint image of an accepted argument permutation. -/
def endpointInverse
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (applied : AppliedArgPermute source wire permutation)
    (endpoint : CEndpoint applied.target.val.nodeCount) :
    CEndpoint source.val.nodeCount :=
  let sourceNode := applied.nodeEquiv.symm endpoint.node
  ⟨sourceNode,
    if sourceNode ∈
        ConcreteWirePrimitive.argumentSiteNodes applied.result.sites then
      applied.generatedPortInverse endpoint.port
    else
      endpoint.port⟩

/-- Construction endpoint transport is left-invertible on every endpoint. -/
theorem endpointInverse_image
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (applied : AppliedArgPermute source wire permutation)
    (endpoint : CEndpoint source.val.nodeCount) :
    applied.endpointInverse (applied.endpointImage endpoint) = endpoint := by
  unfold endpointInverse endpointImage
  have nodeCancel := applied.nodeEquiv.left_inv endpoint.node
  change applied.nodeEquiv.symm (applied.nodeEquiv endpoint.node) =
    endpoint.node at nodeCancel
  change
    ⟨applied.nodeEquiv.symm (applied.nodeEquiv endpoint.node),
      (if applied.nodeEquiv.symm (applied.nodeEquiv endpoint.node) ∈
          ConcreteWirePrimitive.argumentSiteNodes applied.result.sites then
        applied.generatedPortInverse
          (if endpoint.node ∈
              ConcreteWirePrimitive.argumentSiteNodes applied.result.sites then
            applied.generatedPortImage endpoint.port
          else endpoint.port)
      else
        if endpoint.node ∈
            ConcreteWirePrimitive.argumentSiteNodes applied.result.sites then
          applied.generatedPortImage endpoint.port
        else endpoint.port)⟩ = endpoint
  rw [nodeCancel]
  by_cases generated : endpoint.node ∈
      ConcreteWirePrimitive.argumentSiteNodes applied.result.sites
  · simp only [generated, if_pos]
    rw [applied.generatedPortInverse_image_all]
  · simp only [generated, if_neg]
    rfl

/-- Construction endpoint transport is right-invertible on every endpoint. -/
theorem endpointImage_inverse
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (applied : AppliedArgPermute source wire permutation)
    (endpoint : CEndpoint applied.target.val.nodeCount) :
    applied.endpointImage (applied.endpointInverse endpoint) = endpoint := by
  unfold endpointInverse endpointImage
  let sourceNode := applied.nodeEquiv.symm endpoint.node
  have nodeCancel : applied.nodeEquiv sourceNode = endpoint.node :=
    applied.nodeEquiv.right_inv endpoint.node
  change
    ⟨applied.nodeEquiv sourceNode,
      (if sourceNode ∈
          ConcreteWirePrimitive.argumentSiteNodes applied.result.sites then
        applied.generatedPortImage
          (if sourceNode ∈
              ConcreteWirePrimitive.argumentSiteNodes applied.result.sites then
            applied.generatedPortInverse endpoint.port
          else endpoint.port)
      else
        if sourceNode ∈
            ConcreteWirePrimitive.argumentSiteNodes applied.result.sites then
          applied.generatedPortInverse endpoint.port
        else endpoint.port)⟩ = endpoint
  rw [nodeCancel]
  by_cases generated : sourceNode ∈
      ConcreteWirePrimitive.argumentSiteNodes applied.result.sites
  · simp only [generated, if_pos]
    rw [applied.generatedPortImage_inverse_all]
  · simp only [generated, if_neg]
    rfl

/-- Generated source application nodes land at their exact ordered target
nodes under the construction carrier. -/
theorem nodeEquiv_generated
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (applied : AppliedArgPermute source wire permutation)
    (site : Fin applied.result.sites.sites.length) :
    applied.nodeEquiv (applied.result.sites.sites.get site).node =
      applied.result.targetNode site := by
  have generated : (applied.result.sites.sites.get site).node ∈
      ConcreteWirePrimitive.argumentSiteNodes applied.result.sites := by
    unfold ConcreteWirePrimitive.argumentSiteNodes
    exact List.mem_map.mpr
      ⟨applied.result.sites.sites.get site, List.get_mem _ _, rfl⟩
  unfold nodeEquiv ConcreteWirePrimitive.ArgumentResult.nodeEquiv
  change applied.result.nodeImage
      (applied.result.sites.sites.get site).node = _
  rw [ConcreteWirePrimitive.ArgumentResult.nodeImage, dif_pos generated]
  rw [ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_get
    applied.result.sites site generated]

/-- Retained source nodes land at their exact retained construction images. -/
theorem nodeEquiv_retained
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (applied : AppliedArgPermute source wire permutation)
    (node : source.val.NodeId)
    (retained : node ∉
      ConcreteWirePrimitive.argumentSiteNodes applied.result.sites) :
    applied.nodeEquiv node =
      applied.result.retainedNodeImage node retained := by
  unfold nodeEquiv ConcreteWirePrimitive.ArgumentResult.nodeEquiv
  change applied.result.nodeImage node = _
  rw [ConcreteWirePrimitive.ArgumentResult.nodeImage, dif_neg retained]

/-- The head-only construction carrier sends the acted wire to the fresh
target head exactly. -/
@[simp] theorem wireEquiv_head
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (applied : AppliedArgPermute source wire permutation) :
    applied.wireEquiv wire = applied.targetWire := by
  unfold wireEquiv ConcreteWirePrimitive.ArgumentResult.wireEquivHeadOnly
    ConcreteWirePrimitive.ArgumentResult.wireImageHeadOnly
  simp
  rfl

/-- The head-only carrier image of a different source wire is its canonical
retained construction image. -/
theorem wireEquiv_retained
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (applied : AppliedArgPermute source wire permutation)
    (sourceWire : source.val.WireId)
    (different : sourceWire ≠ wire) :
    applied.wireEquiv sourceWire =
      applied.result.retainedWireImage sourceWire (by
        rw [applied.source_removed_exact]
        simpa [different]) := by
  unfold wireEquiv ConcreteWirePrimitive.ArgumentResult.wireEquivHeadOnly
  change (if same : sourceWire = wire then applied.result.targetWire
    else applied.result.retainedWireImage sourceWire _) = _
  rw [dif_neg different]

/-- Retained wire signatures are preserved by the permutation carrier. -/
theorem wireEquiv_retained_signature
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (applied : AppliedArgPermute source wire permutation)
    (sourceWire : source.val.WireId)
    (different : sourceWire ≠ wire) :
    (applied.target.val.wires (applied.wireEquiv sourceWire)).sig =
      (source.val.wires sourceWire).sig := by
  rw [applied.wireEquiv_retained sourceWire different]
  exact applied.result.retainedWireImage_signature sourceWire _

/-- Retained wire scopes are transported by the permutation region carrier. -/
theorem wireEquiv_retained_scope
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (applied : AppliedArgPermute source wire permutation)
    (sourceWire : source.val.WireId)
    (different : sourceWire ≠ wire) :
    (applied.target.val.wires (applied.wireEquiv sourceWire)).scope =
      applied.result.regionEquiv (source.val.wires sourceWire).scope := by
  rw [applied.wireEquiv_retained sourceWire different,
    show
      (applied.target.val.wires
          (applied.result.retainedWireImage sourceWire _)).scope =
        applied.result.regionImage (source.val.wires sourceWire).scope by
      exact applied.result.retainedWireImage_scope sourceWire _]
  exact applied.result.regionImage_exact _

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

/-- Planned source-site position represented by one real source site after
transport through the supplied target isomorphism. -/
def inverseTransportSitePosition
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {permutation : List Nat}
    (forward : AppliedArgPermute planned forwardWire permutation)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgPermute real backwardWire
      forward.inversePermutation)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (site : Fin backward.result.sites.sites.length) :
    Fin forward.result.sites.sites.length :=
  let sourceEndpoint := (backward.result.sites.sites.get site).endpoint
  have sourceMember : sourceEndpoint ∈
      (real.val.wires backwardWire).endpoints := by
    rw [← backward.result.sites.exhaustive]
    exact List.mem_map.mpr
      ⟨backward.result.sites.sites.get site, List.get_mem _ _, rfl⟩
  let middleEndpoint :=
    targetIso.endpointMap backwardWire sourceEndpoint
  have middleMember : middleEndpoint ∈
      (forward.target.val.wires forward.targetWire).endpoints := by
    rw [← wireExact]
    exact targetIso.endpointMap_mem backwardWire sourceEndpoint sourceMember
  let middleEndpointPosition := DenseList.index
    (forward.target.val.wires forward.targetWire).endpoints
    middleEndpoint middleMember
  let middlePosition := Fin.cast forward.targetSites.length.symm
    middleEndpointPosition
  let middleNode := (forward.targetSites.sites.get middlePosition).node
  have generated : middleNode ∈
      ConcreteWirePrimitive.argumentSiteNodes forward.targetSites := by
    unfold ConcreteWirePrimitive.argumentSiteNodes
    exact List.mem_map.mpr
      ⟨forward.targetSites.sites.get middlePosition,
        List.get_mem _ _, rfl⟩
  forward.result.sourcePositionOfTargetNode forward.targetSites
    middleNode generated

/-- The transported inverse node carrier sends each backward generated node
to the exact planned source site selected by endpoint transport. -/
theorem inverseTransport_targetNode
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {permutation : List Nat}
    (forward : AppliedArgPermute planned forwardWire permutation)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgPermute real backwardWire
      forward.inversePermutation)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (site : Fin backward.result.sites.sites.length) :
    forward.inverseTransportNodeEquiv backward targetIso
        (backward.result.targetNode site) =
      (forward.result.sites.sites.get
        (forward.inverseTransportSitePosition backward targetIso
          wireExact site)).node := by
  let backwardNode := (backward.result.sites.sites.get site).node
  have backwardMember : backwardNode ∈
      ConcreteWirePrimitive.argumentSiteNodes backward.result.sites := by
    unfold ConcreteWirePrimitive.argumentSiteNodes
    exact List.mem_map.mpr
      ⟨backward.result.sites.sites.get site, List.get_mem _ _, rfl⟩
  have backwardImage : backward.nodeEquiv backwardNode =
      backward.result.targetNode site := by
    unfold nodeEquiv ConcreteWirePrimitive.ArgumentResult.nodeEquiv
    change backward.result.nodeImage backwardNode = _
    rw [ConcreteWirePrimitive.ArgumentResult.nodeImage,
      dif_pos backwardMember,
      ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_get]
  have backwardInverse : backward.nodeEquiv.symm
      (backward.result.targetNode site) = backwardNode := by
    rw [← backwardImage]
    exact backward.nodeEquiv.left_inv backwardNode
  let sourceEndpoint := (backward.result.sites.sites.get site).endpoint
  have sourceMember : sourceEndpoint ∈
      (real.val.wires backwardWire).endpoints := by
    rw [← backward.result.sites.exhaustive]
    exact List.mem_map.mpr
      ⟨backward.result.sites.sites.get site, List.get_mem _ _, rfl⟩
  let middleEndpoint := targetIso.endpointMap backwardWire sourceEndpoint
  have middleMember : middleEndpoint ∈
      (forward.target.val.wires forward.targetWire).endpoints := by
    rw [← wireExact]
    exact targetIso.endpointMap_mem backwardWire sourceEndpoint sourceMember
  let middleEndpointPosition := DenseList.index
    (forward.target.val.wires forward.targetWire).endpoints
    middleEndpoint middleMember
  let middlePosition := Fin.cast forward.targetSites.length.symm
    middleEndpointPosition
  let middleSite := forward.targetSites.sites.get middlePosition
  have middleNodeExact : middleSite.node = targetIso.nodes backwardNode := by
    have selected := get_of_list_eq forward.targetSites.exhaustive
      middleEndpointPosition
    have endpointExact := DenseList.get_index
      (forward.target.val.wires forward.targetWire).endpoints
      middleEndpoint middleMember
    rw [endpointExact] at selected
    have selectedPosition :
        Fin.cast (congrArg List.length
          forward.targetSites.exhaustive).symm middleEndpointPosition =
          Fin.cast (by simp) middlePosition := by
      apply Fin.ext
      rfl
    rw [selectedPosition] at selected
    have corresponds := targetIso.endpointMap_corresponds backwardWire
      sourceEndpoint sourceMember
    simpa [middleSite, sourceEndpoint, backwardNode, AppliedSite.endpoint]
      using (congrArg CEndpoint.node selected).trans corresponds.1
  have middleGenerated : middleSite.node ∈
      ConcreteWirePrimitive.argumentSiteNodes forward.targetSites := by
    unfold ConcreteWirePrimitive.argumentSiteNodes
    exact List.mem_map.mpr
      ⟨middleSite, List.get_mem _ _, rfl⟩
  let plannedPosition := forward.result.sourcePositionOfTargetNode
    forward.targetSites middleSite.node middleGenerated
  have forwardTarget : forward.result.targetNode plannedPosition =
      middleSite.node :=
    forward.result.targetNode_sourcePositionOfTargetNode
      forward.targetSites middleSite.node middleGenerated
  let plannedNode :=
    (forward.result.sites.sites.get plannedPosition).node
  have plannedMember : plannedNode ∈
      ConcreteWirePrimitive.argumentSiteNodes forward.result.sites := by
    unfold ConcreteWirePrimitive.argumentSiteNodes
    exact List.mem_map.mpr
      ⟨forward.result.sites.sites.get plannedPosition,
        List.get_mem _ _, rfl⟩
  have forwardImage : forward.nodeEquiv plannedNode =
      forward.result.targetNode plannedPosition := by
    unfold nodeEquiv ConcreteWirePrimitive.ArgumentResult.nodeEquiv
    change forward.result.nodeImage plannedNode = _
    rw [ConcreteWirePrimitive.ArgumentResult.nodeImage,
      dif_pos plannedMember,
      ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_get]
  unfold inverseTransportNodeEquiv
  change forward.nodeEquiv.symm
      (targetIso.nodes
        (backward.nodeEquiv.symm (backward.result.targetNode site))) = _
  rw [backwardInverse, ← middleNodeExact,
    ← forwardTarget, ← forwardImage]
  change forward.nodeEquiv.symm (forward.nodeEquiv plannedNode) = plannedNode
  exact forward.nodeEquiv.left_inv plannedNode

/-- The exact forward target node underlying a transported backward site. -/
theorem inverseTransport_middleNode
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {permutation : List Nat}
    (forward : AppliedArgPermute planned forwardWire permutation)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgPermute real backwardWire
      forward.inversePermutation)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (site : Fin backward.result.sites.sites.length) :
    targetIso.nodes (backward.result.sites.sites.get site).node =
      forward.result.targetNode
        (forward.inverseTransportSitePosition backward targetIso
          wireExact site) := by
  let backwardNode := (backward.result.sites.sites.get site).node
  have backwardMember : backwardNode ∈
      ConcreteWirePrimitive.argumentSiteNodes backward.result.sites := by
    unfold ConcreteWirePrimitive.argumentSiteNodes
    exact List.mem_map.mpr
      ⟨backward.result.sites.sites.get site, List.get_mem _ _, rfl⟩
  have backwardImage : backward.nodeEquiv backwardNode =
      backward.result.targetNode site := by
    unfold nodeEquiv ConcreteWirePrimitive.ArgumentResult.nodeEquiv
    change backward.result.nodeImage backwardNode = _
    rw [ConcreteWirePrimitive.ArgumentResult.nodeImage,
      dif_pos backwardMember,
      ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_get]
  have backwardInverse : backward.nodeEquiv.symm
      (backward.result.targetNode site) = backwardNode := by
    rw [← backwardImage]
    exact backward.nodeEquiv.left_inv backwardNode
  let plannedPosition := forward.inverseTransportSitePosition backward
    targetIso wireExact site
  let plannedNode :=
    (forward.result.sites.sites.get plannedPosition).node
  have plannedMember : plannedNode ∈
      ConcreteWirePrimitive.argumentSiteNodes forward.result.sites := by
    unfold ConcreteWirePrimitive.argumentSiteNodes
    exact List.mem_map.mpr
      ⟨forward.result.sites.sites.get plannedPosition,
        List.get_mem _ _, rfl⟩
  have forwardImage : forward.nodeEquiv plannedNode =
      forward.result.targetNode plannedPosition := by
    unfold nodeEquiv ConcreteWirePrimitive.ArgumentResult.nodeEquiv
    change forward.result.nodeImage plannedNode = _
    rw [ConcreteWirePrimitive.ArgumentResult.nodeImage,
      dif_pos plannedMember,
      ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode_get]
  have carrierExact := forward.inverseTransport_targetNode backward
    targetIso wireExact site
  unfold inverseTransportNodeEquiv at carrierExact
  change forward.nodeEquiv.symm
      (targetIso.nodes
        (backward.nodeEquiv.symm (backward.result.targetNode site))) =
      plannedNode at carrierExact
  rw [backwardInverse] at carrierExact
  have lifted := congrArg forward.nodeEquiv carrierExact
  have forwardCancel := forward.nodeEquiv.right_inv
    (targetIso.nodes backwardNode)
  change forward.nodeEquiv
      (forward.nodeEquiv.symm (targetIso.nodes backwardNode)) =
    targetIso.nodes backwardNode at forwardCancel
  have exactMiddle : targetIso.nodes backwardNode =
      forward.nodeEquiv plannedNode :=
    forwardCancel.symm.trans lifted
  rw [forwardImage] at exactMiddle
  exact exactMiddle

/-- Generated backward nodes satisfy the complete transported node-table
law, including cancellation of the inverse permutation payload. -/
theorem inverseTransport_generated_node_table
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {permutation : List Nat}
    (forward : AppliedArgPermute planned forwardWire permutation)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgPermute real backwardWire
      forward.inversePermutation)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (site : Fin backward.result.sites.sites.length) :
    planned.val.nodes
        (forward.inverseTransportNodeEquiv backward targetIso
          (backward.result.targetNode site)) =
      (backward.target.val.nodes
        (backward.result.targetNode site)).rename
          (forward.inverseTransportRegionEquiv backward targetIso) := by
  let backwardSite := backward.result.sites.sites.get site
  let plannedPosition := forward.inverseTransportSitePosition backward
    targetIso wireExact site
  let plannedSite := forward.result.sites.sites.get plannedPosition
  have nodeExact := forward.inverseTransport_targetNode backward
    targetIso wireExact site
  have backwardTargetData : backward.target.val.nodes
      (backward.result.targetNode site) =
    .atom (backward.result.regionImage backwardSite.region)
      backward.result.targetArguments := by
    exact backward.result.targetNode_data site
  rw [nodeExact, plannedSite.node_data, backwardTargetData]
  have targetNodeExact := forward.inverseTransport_middleNode backward
    targetIso wireExact site
  have mappedData := targetIso.node_table backwardSite.node
  rw [backwardSite.node_data, targetNodeExact] at mappedData
  have forwardTargetData : forward.target.val.nodes
      (forward.result.targetNode plannedPosition) =
    .atom (forward.result.regionImage plannedSite.region)
      forward.result.targetArguments := by
    exact forward.result.targetNode_data plannedPosition
  rw [forwardTargetData] at mappedData
  have regionExact : forward.result.regionImage plannedSite.region =
      targetIso.regions backwardSite.region := by
    exact (CNode.atom.inj mappedData).1
  have targetArguments := forward.inverseTargetArguments_exact backward
    targetIso wireExact
  rw [targetArguments]
  have plannedArguments : plannedSite.argumentSignatures =
      forward.sourceArgumentList :=
    ConcreteWirePrimitive.appliedSite_arguments_eq_relationArguments
      forward.sourceArgumentList forward.sourceWire_signature plannedSite
  rw [plannedArguments]
  congr 2
  unfold inverseTransportRegionEquiv
  change plannedSite.region = forward.result.regionEquiv.symm
    (targetIso.regions
      (backward.result.regionEquiv.symm
        (backward.result.regionImage backwardSite.region)))
  rw [backward.result.regionImage_exact]
  have backwardCancel :=
    backward.result.regionEquiv.left_inv backwardSite.region
  change backward.result.regionEquiv.invFun
      (backward.result.regionEquiv backwardSite.region) =
    backwardSite.region at backwardCancel
  have forwardRegionExact :=
    forward.result.regionImage_exact plannedSite.region
  calc
    plannedSite.region = forward.result.regionEquiv.symm
        (forward.result.regionEquiv plannedSite.region) :=
      (forward.result.regionEquiv.left_inv plannedSite.region).symm
    _ = forward.result.regionEquiv.symm
        (forward.result.regionImage plannedSite.region) := by
      rw [forwardRegionExact]
    _ = forward.result.regionEquiv.symm
        (targetIso.regions backwardSite.region) :=
      congrArg forward.result.regionEquiv.symm regionExact
    _ = forward.result.regionEquiv.symm
        (targetIso.regions
          (backward.result.regionEquiv.symm
            (backward.result.regionEquiv backwardSite.region))) :=
      congrArg (fun value => forward.result.regionEquiv.symm
        (targetIso.regions value)) backwardCancel.symm

/-- A real node retained by the backward replacement cannot be transported
to a generated forward target site. -/
theorem inverseTransport_middleNode_retained
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {permutation : List Nat}
    (forward : AppliedArgPermute planned forwardWire permutation)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgPermute real backwardWire
      forward.inversePermutation)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (realNode : real.val.NodeId)
    (retained : realNode ∉
      ConcreteWirePrimitive.argumentSiteNodes backward.result.sites) :
    targetIso.nodes realNode ∉
      ConcreteWirePrimitive.argumentSiteNodes forward.targetSites := by
  intro generated
  unfold ConcreteWirePrimitive.argumentSiteNodes at generated
  rcases List.mem_map.mp generated with
    ⟨middleSite, middleMember, middleNodeExact⟩
  have targetOwner : forward.target.val.endpointOwner?
      ⟨targetIso.nodes realNode, .head⟩ = some forward.targetWire := by
    rw [← middleNodeExact]
    exact middleSite.endpoint_owner
  have mappedData := targetIso.node_table realNode
  have middleData : forward.target.val.nodes (targetIso.nodes realNode) =
      .atom middleSite.region middleSite.argumentSignatures := by
    rw [← middleNodeExact]
    exact middleSite.node_data
  cases sourceData : real.val.nodes realNode with
  | atom region arguments =>
      have sourceOwner := targetIso.atom_owner_backward real.property
        sourceData targetOwner
      have inverseWireExact : targetIso.wires.symm forward.targetWire =
          backwardWire := by
        calc
          targetIso.wires.symm forward.targetWire =
              targetIso.wires.symm (targetIso.wires backwardWire) := by
            rw [wireExact]
          _ = backwardWire := targetIso.wires.left_inv backwardWire
      rw [inverseWireExact] at sourceOwner
      have incident := ConcreteDiagram.endpointOwner?_incident real.val
        ⟨realNode, .head⟩ backwardWire sourceOwner
      rw [← backward.result.sites.exhaustive] at incident
      rcases List.mem_map.mp incident with
        ⟨sourceSite, sourceMember, endpointExact⟩
      apply retained
      unfold ConcreteWirePrimitive.argumentSiteNodes
      exact List.mem_map.mpr
        ⟨sourceSite, sourceMember,
          congrArg CEndpoint.node endpointExact⟩
  | ref region definition arguments =>
      rw [middleData, sourceData] at mappedData
      contradiction
  | identity region signature arity =>
      rw [middleData, sourceData] at mappedData
      contradiction

/-- Retained backward nodes satisfy the complete transported node-table law. -/
theorem inverseTransport_retained_node_table
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {permutation : List Nat}
    (forward : AppliedArgPermute planned forwardWire permutation)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgPermute real backwardWire
      forward.inversePermutation)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (realNode : real.val.NodeId)
    (retained : realNode ∉
      ConcreteWirePrimitive.argumentSiteNodes backward.result.sites) :
    planned.val.nodes
        (forward.inverseTransportNodeEquiv backward targetIso
          (backward.result.retainedNodeImage realNode retained)) =
      (backward.target.val.nodes
        (backward.result.retainedNodeImage realNode retained)).rename
          (forward.inverseTransportRegionEquiv backward targetIso) := by
  have middleRetained := forward.inverseTransport_middleNode_retained
    backward targetIso wireExact realNode retained
  let plannedNode := forward.result.sourceNodeOfRetainedTarget
    forward.targetSites (targetIso.nodes realNode) middleRetained
  have plannedRetained : plannedNode ∉
      ConcreteWirePrimitive.argumentSiteNodes forward.result.sites :=
    ConcreteWirePrimitive.sourceRetainedNode_not_removed
      forward.result.sites
      (forward.result.retainedBaseNodeOfTarget forward.targetSites
        (targetIso.nodes realNode) middleRetained)
  have backwardImage : backward.nodeEquiv realNode =
      backward.result.retainedNodeImage realNode retained := by
    unfold nodeEquiv ConcreteWirePrimitive.ArgumentResult.nodeEquiv
    change backward.result.nodeImage realNode = _
    rw [ConcreteWirePrimitive.ArgumentResult.nodeImage, dif_neg retained]
  have backwardInverse : backward.nodeEquiv.symm
      (backward.result.retainedNodeImage realNode retained) = realNode := by
    rw [← backwardImage]
    exact backward.nodeEquiv.left_inv realNode
  have forwardInverse : forward.nodeEquiv.symm
      (targetIso.nodes realNode) = plannedNode := by
    unfold nodeEquiv ConcreteWirePrimitive.ArgumentResult.nodeEquiv
    change forward.result.sourceNode forward.targetSites
      (targetIso.nodes realNode) = plannedNode
    unfold ConcreteWirePrimitive.ArgumentResult.sourceNode
    split
    next generated => exact (middleRetained generated).elim
    next _ => rfl
  have carrierExact : forward.inverseTransportNodeEquiv backward targetIso
      (backward.result.retainedNodeImage realNode retained) =
        plannedNode := by
    unfold inverseTransportNodeEquiv
    change forward.nodeEquiv.symm
      (targetIso.nodes
        (backward.nodeEquiv.symm
          (backward.result.retainedNodeImage realNode retained))) = _
    rw [backwardInverse, forwardInverse]
  rw [carrierExact]
  have backwardData : backward.target.val.nodes
      (backward.result.retainedNodeImage realNode retained) =
        (real.val.nodes realNode).rename backward.result.regionEquiv := by
    exact backward.result.retainedNodeImage_data realNode retained
  rw [backwardData]
  have forwardImage : forward.result.retainedNodeImage plannedNode
      plannedRetained = targetIso.nodes realNode :=
    forward.result.retainedNodeImage_sourceNodeOfRetainedTarget
      forward.targetSites (targetIso.nodes realNode) middleRetained
  have forwardData : forward.target.val.nodes (targetIso.nodes realNode) =
      (planned.val.nodes plannedNode).rename forward.result.regionEquiv := by
    rw [← forwardImage]
    exact forward.result.retainedNodeImage_data plannedNode plannedRetained
  have middleData := targetIso.node_table realNode
  rw [forwardData] at middleData
  cases realData : real.val.nodes realNode with
  | atom realRegion realArguments =>
      cases plannedData : planned.val.nodes plannedNode with
      | atom plannedRegion plannedArguments =>
          rw [realData, plannedData] at middleData
          simp only [CNode.rename] at middleData ⊢
          have parts := CNode.atom.inj middleData
          cases parts.2
          congr 1
          have regionRelation := parts.1
          unfold inverseTransportRegionEquiv
          have backwardCancel :=
            backward.result.regionEquiv.left_inv realRegion
          change backward.result.regionEquiv.invFun
              (backward.result.regionEquiv realRegion) = realRegion
            at backwardCancel
          exact (forward.result.regionEquiv.left_inv plannedRegion).symm.trans
            ((congrArg forward.result.regionEquiv.symm
              regionRelation).trans
              (congrArg (fun value => forward.result.regionEquiv.symm
                (targetIso.regions value)) backwardCancel.symm))

      | ref plannedRegion definition plannedArguments =>
          rw [realData, plannedData] at middleData
          contradiction
      | identity plannedRegion signature arity =>
          rw [realData, plannedData] at middleData
          contradiction
  | ref realRegion realDefinition realArguments =>
      cases plannedData : planned.val.nodes plannedNode with
      | atom plannedRegion plannedArguments =>
          rw [realData, plannedData] at middleData
          contradiction
      | ref plannedRegion plannedDefinition plannedArguments =>
          rw [realData, plannedData] at middleData
          simp only [CNode.rename] at middleData ⊢
          have parts := CNode.ref.inj middleData
          cases parts.2.1
          cases parts.2.2
          congr 1
          have regionRelation := parts.1
          unfold inverseTransportRegionEquiv
          have backwardCancel :=
            backward.result.regionEquiv.left_inv realRegion
          change backward.result.regionEquiv.invFun
              (backward.result.regionEquiv realRegion) = realRegion
            at backwardCancel
          exact (forward.result.regionEquiv.left_inv plannedRegion).symm.trans
            ((congrArg forward.result.regionEquiv.symm
              regionRelation).trans
              (congrArg (fun value => forward.result.regionEquiv.symm
                (targetIso.regions value)) backwardCancel.symm))
      | identity plannedRegion signature arity =>
          rw [realData, plannedData] at middleData
          contradiction
  | identity realRegion realSignature realArity =>
      cases plannedData : planned.val.nodes plannedNode with
      | atom plannedRegion plannedArguments =>
          rw [realData, plannedData] at middleData
          contradiction
      | ref plannedRegion definition plannedArguments =>
          rw [realData, plannedData] at middleData
          contradiction
      | identity plannedRegion plannedSignature plannedArity =>
          rw [realData, plannedData] at middleData
          simp only [CNode.rename] at middleData ⊢
          have parts := CNode.identity.inj middleData
          cases parts.2.1
          cases parts.2.2
          congr 1
          have regionRelation := parts.1
          unfold inverseTransportRegionEquiv
          have backwardCancel :=
            backward.result.regionEquiv.left_inv realRegion
          change backward.result.regionEquiv.invFun
              (backward.result.regionEquiv realRegion) = realRegion
            at backwardCancel
          exact (forward.result.regionEquiv.left_inv plannedRegion).symm.trans
            ((congrArg forward.result.regionEquiv.symm
              regionRelation).trans
              (congrArg (fun value => forward.result.regionEquiv.symm
                (targetIso.regions value)) backwardCancel.symm))
/-- Complete node-table law for the transported inverse permutation carrier. -/
theorem inverseTransport_node_table
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {permutation : List Nat}
    (forward : AppliedArgPermute planned forwardWire permutation)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgPermute real backwardWire
      forward.inversePermutation)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (node : backward.target.val.NodeId) :
    planned.val.nodes
        (forward.inverseTransportNodeEquiv backward targetIso node) =
      (backward.target.val.nodes node).rename
        (forward.inverseTransportRegionEquiv backward targetIso) := by
  let realNode := backward.nodeEquiv.symm node
  have nodeRecover : backward.nodeEquiv realNode = node :=
    backward.nodeEquiv.right_inv node
  by_cases generated : realNode ∈
      ConcreteWirePrimitive.argumentSiteNodes backward.result.sites
  · let site := ConcreteWirePrimitive.ArgumentResult.sourcePositionOfNode
      backward.result.sites realNode generated
    have imageExact : backward.nodeEquiv realNode =
        backward.result.targetNode site := by
      unfold nodeEquiv ConcreteWirePrimitive.ArgumentResult.nodeEquiv
      change backward.result.nodeImage realNode = _
      rw [ConcreteWirePrimitive.ArgumentResult.nodeImage,
        dif_pos generated]
    have nodeExact : node = backward.result.targetNode site :=
      nodeRecover.symm.trans imageExact
    rw [nodeExact]
    exact forward.inverseTransport_generated_node_table backward
      targetIso wireExact site
  · have imageExact : backward.nodeEquiv realNode =
        backward.result.retainedNodeImage realNode generated := by
      unfold nodeEquiv ConcreteWirePrimitive.ArgumentResult.nodeEquiv
      change backward.result.nodeImage realNode = _
      rw [ConcreteWirePrimitive.ArgumentResult.nodeImage,
        dif_neg generated]
    have nodeExact : node =
        backward.result.retainedNodeImage realNode generated :=
      nodeRecover.symm.trans imageExact
    rw [nodeExact]
    exact forward.inverseTransport_retained_node_table backward
      targetIso wireExact realNode generated

/-- The transported inverse wire carrier acts on every backward construction
image by pulling through the supplied target isomorphism and the forward
construction inverse. -/
theorem inverseTransport_wireEquiv_image
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {permutation : List Nat}
    (forward : AppliedArgPermute planned forwardWire permutation)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgPermute real backwardWire
      forward.inversePermutation)
    (targetIso : ConcreteIso real.val forward.target.val)
    (realWire : real.val.WireId) :
    forward.inverseTransportWireEquiv backward targetIso
        (backward.wireEquiv realWire) =
      forward.wireEquiv.symm (targetIso.wires realWire) := by
  unfold inverseTransportWireEquiv
  change forward.wireEquiv.symm
    (targetIso.wires
      (backward.wireEquiv.symm (backward.wireEquiv realWire))) = _
  have backwardCancel := backward.wireEquiv.left_inv realWire
  change backward.wireEquiv.invFun (backward.wireEquiv realWire) =
    realWire at backwardCancel
  exact congrArg (fun value => forward.wireEquiv.symm
    (targetIso.wires value)) backwardCancel

/-- Complete wire-signature law for the transported inverse carrier. -/
theorem inverseTransport_wire_signature
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {permutation : List Nat}
    (forward : AppliedArgPermute planned forwardWire permutation)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgPermute real backwardWire
      forward.inversePermutation)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (targetWire : backward.target.val.WireId) :
    (planned.val.wires
      (forward.inverseTransportWireEquiv backward targetIso targetWire)).sig =
      (backward.target.val.wires targetWire).sig := by
  let realWire := backward.wireEquiv.symm targetWire
  have targetExact : backward.wireEquiv realWire = targetWire :=
    backward.wireEquiv.right_inv targetWire
  rw [← targetExact, forward.inverseTransport_wireEquiv_image]
  by_cases head : realWire = backwardWire
  · rw [head]
    have forwardInverseHead : forward.wireEquiv.symm forward.targetWire =
        forwardWire := by
      rw [← forward.wireEquiv_head]
      exact forward.wireEquiv.left_inv forwardWire
    rw [wireExact, forwardInverseHead, backward.wireEquiv_head,
      forward.sourceWire_signature, backward.targetWire_signature]
    have restored := forward.inverseTargetArguments_exact backward
      targetIso wireExact
    rw [backward.targetArguments_exact] at restored
    exact congrArg Sig.rel restored.symm
  · let plannedWire := forward.wireEquiv.symm (targetIso.wires realWire)
    have plannedImage : forward.wireEquiv plannedWire =
        targetIso.wires realWire :=
      forward.wireEquiv.right_inv (targetIso.wires realWire)
    have plannedDifferent : plannedWire ≠ forwardWire := by
      intro same
      have mapped := congrArg forward.wireEquiv same
      rw [plannedImage, forward.wireEquiv_head] at mapped
      have realExact := targetIso.wires.injective
        (mapped.trans wireExact.symm)
      exact head realExact
    calc
      (planned.val.wires plannedWire).sig =
          (forward.target.val.wires (targetIso.wires realWire)).sig := by
        rw [← plannedImage]
        exact (forward.wireEquiv_retained_signature plannedWire
          plannedDifferent).symm
      _ = (real.val.wires realWire).sig :=
        targetIso.wire_signature realWire
      _ = (backward.target.val.wires
          (backward.wireEquiv realWire)).sig :=
        (backward.wireEquiv_retained_signature realWire head).symm

/-- Complete wire-scope law for the transported inverse carrier. -/
theorem inverseTransport_wire_scope
    {planned real : CheckedDiagram definitions}
    {forwardWire : planned.val.WireId}
    {permutation : List Nat}
    (forward : AppliedArgPermute planned forwardWire permutation)
    {backwardWire : real.val.WireId}
    (backward : AppliedArgPermute real backwardWire
      forward.inversePermutation)
    (targetIso : ConcreteIso real.val forward.target.val)
    (wireExact : targetIso.wires backwardWire = forward.targetWire)
    (targetWire : backward.target.val.WireId) :
    (planned.val.wires
      (forward.inverseTransportWireEquiv backward targetIso targetWire)).scope =
      forward.inverseTransportRegionEquiv backward targetIso
        (backward.target.val.wires targetWire).scope := by
  let realWire := backward.wireEquiv.symm targetWire
  have targetExact : backward.wireEquiv realWire = targetWire :=
    backward.wireEquiv.right_inv targetWire
  rw [← targetExact, forward.inverseTransport_wireEquiv_image]
  by_cases head : realWire = backwardWire
  · rw [head]
    have forwardInverseHead : forward.wireEquiv.symm forward.targetWire =
        forwardWire := by
      rw [← forward.wireEquiv_head]
      exact forward.wireEquiv.left_inv forwardWire
    rw [wireExact, forwardInverseHead, backward.wireEquiv_head]
    have backwardScope :=
      backward.result.targetWire_scope_regionImage
    change (backward.target.val.wires backward.targetWire).scope =
        backward.result.regionImage
          (real.val.wires backwardWire).scope at backwardScope
    have forwardScope := forward.result.targetWire_scope_regionImage
    change (forward.target.val.wires forward.targetWire).scope =
        forward.result.regionImage
          (planned.val.wires forwardWire).scope at forwardScope
    have middleScope := targetIso.wire_scope backwardWire
    rw [wireExact] at middleScope
    unfold inverseTransportRegionEquiv
    rw [backwardScope, backward.result.regionImage_exact]
    have backwardCancel := backward.result.regionEquiv.left_inv
      (real.val.wires backwardWire).scope
    change backward.result.regionEquiv.invFun
        (backward.result.regionEquiv
          (real.val.wires backwardWire).scope) =
      (real.val.wires backwardWire).scope at backwardCancel
    calc
      (planned.val.wires forwardWire).scope =
          forward.result.regionEquiv.symm
            (forward.result.regionEquiv
              (planned.val.wires forwardWire).scope) :=
        (forward.result.regionEquiv.left_inv _).symm
      _ = forward.result.regionEquiv.symm
          (forward.target.val.wires forward.targetWire).scope := by
        rw [forwardScope, forward.result.regionImage_exact]
      _ = forward.result.regionEquiv.symm
          (targetIso.regions (real.val.wires backwardWire).scope) := by
        rw [middleScope]
      _ = forward.result.regionEquiv.symm
          (targetIso.regions
            (backward.result.regionEquiv.symm
              (backward.result.regionEquiv
                (real.val.wires backwardWire).scope))) :=
        congrArg (fun value => forward.result.regionEquiv.symm
          (targetIso.regions value)) backwardCancel.symm
  · let plannedWire := forward.wireEquiv.symm (targetIso.wires realWire)
    have plannedImage : forward.wireEquiv plannedWire =
        targetIso.wires realWire :=
      forward.wireEquiv.right_inv (targetIso.wires realWire)
    have plannedDifferent : plannedWire ≠ forwardWire := by
      intro same
      have mapped := congrArg forward.wireEquiv same
      rw [plannedImage, forward.wireEquiv_head] at mapped
      have realExact := targetIso.wires.injective
        (mapped.trans wireExact.symm)
      exact head realExact
    have forwardScope := forward.wireEquiv_retained_scope plannedWire
      plannedDifferent
    rw [plannedImage] at forwardScope
    have backwardScope := backward.wireEquiv_retained_scope realWire head
    have middleScope := targetIso.wire_scope realWire
    unfold inverseTransportRegionEquiv
    rw [backwardScope]
    have backwardCancel := backward.result.regionEquiv.left_inv
      (real.val.wires realWire).scope
    change backward.result.regionEquiv.invFun
        (backward.result.regionEquiv (real.val.wires realWire).scope) =
      (real.val.wires realWire).scope at backwardCancel
    calc
      (planned.val.wires plannedWire).scope =
          forward.result.regionEquiv.symm
            (forward.result.regionEquiv
              (planned.val.wires plannedWire).scope) :=
        (forward.result.regionEquiv.left_inv _).symm
      _ = forward.result.regionEquiv.symm
          (forward.target.val.wires (targetIso.wires realWire)).scope := by
        rw [forwardScope]
      _ = forward.result.regionEquiv.symm
          (targetIso.regions (real.val.wires realWire).scope) := by
        rw [middleScope]
      _ = forward.result.regionEquiv.symm
          (targetIso.regions
            (backward.result.regionEquiv.symm
              (backward.result.regionEquiv
                (real.val.wires realWire).scope))) :=
        congrArg (fun value => forward.result.regionEquiv.symm
          (targetIso.regions value)) backwardCancel.symm

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

/-- Pulling a source position through the inverse output position selects
that exact source attachment. -/
theorem sourceArgumentWire_inversePosition
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    {permutation : List Nat}
    (applied : AppliedArgPermute source wire permutation)
    (site : Fin applied.result.sites.sites.length)
    (position : Fin applied.sourceArguments.length) :
    applied.sourceArgumentWire site
        (applied.permutation_receipt.inversePosition position) =
      (applied.result.sites.sites.get site).arguments.get
        (Fin.cast (applied.sourceSiteArgumentLength site).symm position) := by
  unfold sourceArgumentWire
  apply congrArg (applied.result.sites.sites.get site).arguments.get
  exact congrArg
    (Fin.cast (applied.sourceSiteArgumentLength site).symm)
    (applied.permutation_receipt.forward_inversePosition position)

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
