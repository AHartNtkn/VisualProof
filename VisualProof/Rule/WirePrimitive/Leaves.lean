import VisualProof.Diagram.Concrete.WirePrimitive.LeavesSemantics
import VisualProof.Rule.Tag
import VisualProof.Rule.Orientation

namespace VisualProof

namespace WirePrimitive

namespace Leaves

open ConcreteWirePrimitive

/-- Stable public refusal outcomes for formal, identity, and reference leaves. -/
inductive WireLeafError
  | leafRequiresNegative
  | leafBackwardRequiresPositive
  | abstractRequiresPositive
  | abstractBackwardRequiresNegative
  | scopeCompilationFailed
  | semanticLedgerRejected
  | concreteRejected (error : ConcreteWirePrimitive.LeafError)
  deriving Repr, DecidableEq

private def optionToExcept
    (error : WireLeafError) : Option α → Except WireLeafError α
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

private structure CheckedLeafPolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId) where
  compiled :
    SiteCompilation source (source.val.wires wire).scope
  legal :
    joinPolarityLegal orientation compiled.frame.context.cutDepth = true

private structure CheckedAbstractPolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (scope : source.val.RegionId) where
  compiled : SiteCompilation source scope
  legal :
    severPolarityLegal orientation compiled.frame.context.cutDepth = true

private def requireLeafPolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId) :
    Except WireLeafError
      (CheckedLeafPolarity source orientation wire) := by
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
          | .forward => .leafRequiresNegative
          | .backward => .leafBackwardRequiresPositive

private def requireAbstractPolarity
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (scope : source.val.RegionId) :
    Except WireLeafError
      (CheckedAbstractPolarity source orientation scope) := by
  match compileSite? source scope with
  | none => exact .error .scopeCompilationFailed
  | some compiled =>
      if legal :
          severPolarityLegal orientation
            compiled.frame.context.cutDepth then
        exact .ok ⟨compiled, legal⟩
      else
        exact .error <|
          match orientation with
          | .forward => .abstractRequiresPositive
          | .backward => .abstractBackwardRequiresNegative

private structure AbstractLedger
    (source : CheckedDiagram definitions)
    (scope : source.val.RegionId)
    (result : LeafAbstractResult source) where
  reverse :
    ConcreteWirePrimitive.LeafResult result.checked result.targetWire
  sourceArguments : List Sig
  sourceSignature :
    (result.checked.val.wires result.targetWire).sig =
      .rel sourceArguments
  kind : LeavesSemantics.LeafKind definitions sourceArguments
  factorization :
    LeavesSemantics.LeafFactorization reverse sourceArguments kind
  inverseIso : ConcreteIso reverse.checked.val source.val
  sourceScope : SiteCompilation source scope
  cutDepthExact :
    factorization.sourceScope.frame.context.cutDepth =
      sourceScope.frame.context.cutDepth

/-- Internal decidable acceptance for the fixed carriers supplied by an
abstraction and its checked reconstruction.  Accepted public receipts retain
the resulting isomorphism as total data. -/
private def checkReverseIso?
    {source : CheckedDiagram definitions}
    (result : LeafAbstractResult source)
    (reverse : ConcreteWirePrimitive.LeafResult result.checked
      result.targetWire) :
    Option (ConcreteIso reverse.checked.val source.val) :=
  ConcreteIso.checkEquivs? reverse.checked.val source.val
    (reverse.regionOriginEquiv.trans result.regionOriginEquiv)
    (reverse.nodeOriginEquiv.trans result.nodeOriginEquiv)
    (finEquivOfEq (by
      have reverseCount : reverse.checked.val.wireCount + 1 =
          result.checked.val.wireCount :=
        LeafConstruction.finCount_eq reverse.extendedWireOriginEquiv
      have abstractCount : result.checked.val.wireCount =
          source.val.wireCount + 1 :=
        LeafConstruction.finCount_eq result.wireSplitEquiv
      omega))

private def checkAbstractLedger
    (source : CheckedDiagram definitions)
    (scope : source.val.RegionId)
    (result : LeafAbstractResult source)
    (reverse :
      ConcreteWirePrimitive.LeafResult result.checked result.targetWire)
    (sourceArguments : List Sig)
    (sourceSignature :
      (result.checked.val.wires result.targetWire).sig =
        .rel sourceArguments)
    (kind : LeavesSemantics.LeafKind definitions sourceArguments) :
    Option (AbstractLedger source scope result) := do
  let factorization ←
    LeavesSemantics.checkLeafFactorization reverse sourceArguments
      sourceSignature kind
  let inverseIso ← checkReverseIso? result reverse
  let sourceScope ← compileSite? source scope
  if cutDepthExact :
      factorization.sourceScope.frame.context.cutDepth =
        sourceScope.frame.context.cutDepth then
    pure
      ⟨reverse, sourceArguments, sourceSignature, kind, factorization,
        inverseIso, sourceScope, cutDepthExact⟩
  else none

structure AppliedApplyFormal
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId)
    (position : Nat) where
  private mk ::
  private result : ConcreteWirePrimitive.LeafResult source wire
  private sourceArguments : List Sig
  private sourceSignature :
    (source.val.wires wire).sig = .rel sourceArguments
  private kind :
    LeavesSemantics.LeafKind definitions sourceArguments
  private factorization :
    LeavesSemantics.LeafFactorization result sourceArguments kind
  private polarity : CheckedLeafPolarity source orientation wire

structure AppliedIdentityLeaf
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId) where
  private mk ::
  private result : ConcreteWirePrimitive.LeafResult source wire
  private sourceArguments : List Sig
  private sourceSignature :
    (source.val.wires wire).sig = .rel sourceArguments
  private kind :
    LeavesSemantics.LeafKind definitions sourceArguments
  private factorization :
    LeavesSemantics.LeafFactorization result sourceArguments kind
  private polarity : CheckedLeafPolarity source orientation wire

structure AppliedRefLeaf
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (wire : source.val.WireId)
    (definition : Fin definitions.length) where
  private mk ::
  private result : ConcreteWirePrimitive.LeafResult source wire
  private sourceArguments : List Sig
  private sourceSignature :
    (source.val.wires wire).sig = .rel sourceArguments
  private kind :
    LeavesSemantics.LeafKind definitions sourceArguments
  private factorization :
    LeavesSemantics.LeafFactorization result sourceArguments kind
  private polarity : CheckedLeafPolarity source orientation wire

structure AppliedAbstractFormal
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (nodes : List source.val.NodeId)
    (scope : source.val.RegionId) where
  private mk ::
  private result : LeafAbstractResult source
  private ledger : AbstractLedger source scope result
  private polarity : CheckedAbstractPolarity source orientation scope

structure AppliedIdentityAbstract
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (nodes : List source.val.NodeId)
    (scope : source.val.RegionId) where
  private mk ::
  private result : LeafAbstractResult source
  private ledger : AbstractLedger source scope result
  private polarity : CheckedAbstractPolarity source orientation scope

structure AppliedRefAbstract
    (source : CheckedDiagram definitions)
    (orientation : Orientation)
    (nodes : List source.val.NodeId)
    (scope : source.val.RegionId) where
  private mk ::
  private result : LeafAbstractResult source
  private ledger : AbstractLedger source scope result
  private polarity : CheckedAbstractPolarity source orientation scope

/-- Accepted pair-owned inverse landing.  Once this receipt exists, its
landing isomorphism is total and no further matching or validation occurs. -/
structure InverseLanding
    (target planned : CheckedDiagram definitions) where
  private mk ::
  iso : ConcreteIso target.val planned.val

/-- Pair-owned inverse carrier validation for a checked leaf construction and
an abstraction applied after transporting its exact replacement nodes.  Every
carrier is supplied by the two construction receipts and the intervening
isomorphism; no carrier permutation is enumerated. -/
private def checkInverseTransportIso?
    {planned real : CheckedDiagram definitions}
    {wire : planned.val.WireId}
    (forward : ConcreteWirePrimitive.LeafResult planned wire)
    (backward : LeafAbstractResult real)
    (targetIso : ConcreteIso real.val forward.checked.val) :
    Option (ConcreteIso backward.checked.val planned.val) :=
  ConcreteIso.checkEquivs? backward.checked.val planned.val
    (backward.regionOriginEquiv.trans <|
      targetIso.regions.trans forward.regionOriginEquiv)
    (backward.nodeOriginEquiv.trans <|
      targetIso.nodes.trans forward.nodeOriginEquiv)
    (backward.wireSplitEquiv.trans <|
      (LeafConstruction.addLastEquiv targetIso.wires).trans
        forward.extendedWireOriginEquiv)

private def acceptInverseLanding
    {planned real : CheckedDiagram definitions}
    {wire : planned.val.WireId}
    (forward : ConcreteWirePrimitive.LeafResult planned wire)
    (backward : LeafAbstractResult real)
    (targetIso : ConcreteIso real.val forward.checked.val) :
    Except WireLeafError (InverseLanding backward.checked planned) := do
  let iso ← optionToExcept .semanticLedgerRejected <|
    checkInverseTransportIso? forward backward targetIso
  pure ⟨iso⟩

namespace AppliedApplyFormal

def source
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (_ : AppliedApplyFormal source orientation wire position) := source

def target
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedApplyFormal source orientation wire position) :=
  applied.result.target

/-- The exact concrete construction accepted by this opaque formal-leaf
receipt.  Compiler factorization consumes its carrier-origin maps without
rerunning the leaf checker. -/
def constructionResult
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedApplyFormal source orientation wire position) :
    ConcreteWirePrimitive.LeafResult source wire :=
  applied.result

/-- Exact ordered leaf nodes introduced by formal application. -/
def inverseNodes
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedApplyFormal source orientation wire position) :
    List applied.target.val.NodeId :=
  applied.result.targetRemovedNodes

/-- Exact target scope at which the introduced formal leaves abstract. -/
def inverseScope
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (applied : AppliedApplyFormal source orientation wire position) :
    applied.target.val.RegionId :=
  applied.result.targetScope

/-- Construction-owned inverse landing for a transported formal leaf. -/
def inverseTransport
    {planned real : CheckedDiagram definitions}
    {joinOrientation orientation : Orientation}
    {wire : planned.val.WireId}
    {position : Nat}
    {nodes : List real.val.NodeId}
    {scope : real.val.RegionId}
    (applied : AppliedApplyFormal planned joinOrientation wire position)
    (backward : AppliedAbstractFormal real orientation nodes scope)
    (targetIso : ConcreteIso real.val applied.target.val) :
    Except WireLeafError
      (InverseLanding backward.result.checked planned) :=
  acceptInverseLanding applied.result backward.result targetIso

def tag
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {position : Nat}
    (_ : AppliedApplyFormal source orientation wire position) : StepTag :=
  .applyFormal

end AppliedApplyFormal

namespace AppliedIdentityLeaf

def source
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    (_ : AppliedIdentityLeaf source orientation wire) := source

def target
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    (applied : AppliedIdentityLeaf source orientation wire) :=
  applied.result.target

/-- The exact concrete construction accepted by this opaque identity-leaf
receipt. -/
def constructionResult
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    (applied : AppliedIdentityLeaf source orientation wire) :
    ConcreteWirePrimitive.LeafResult source wire :=
  applied.result

/-- Exact ordered identity nodes introduced by identity leaf expansion. -/
def inverseNodes
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    (applied : AppliedIdentityLeaf source orientation wire) :
    List applied.target.val.NodeId :=
  applied.result.targetRemovedNodes

/-- Exact target scope at which the introduced identity leaves abstract. -/
def inverseScope
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    (applied : AppliedIdentityLeaf source orientation wire) :
    applied.target.val.RegionId :=
  applied.result.targetScope

/-- Construction-owned inverse landing for a transported identity leaf. -/
def inverseTransport
    {planned real : CheckedDiagram definitions}
    {joinOrientation orientation : Orientation}
    {wire : planned.val.WireId}
    {nodes : List real.val.NodeId}
    {scope : real.val.RegionId}
    (applied : AppliedIdentityLeaf planned joinOrientation wire)
    (backward : AppliedIdentityAbstract real orientation nodes scope)
    (targetIso : ConcreteIso real.val applied.target.val) :
    Except WireLeafError
      (InverseLanding backward.result.checked planned) :=
  acceptInverseLanding applied.result backward.result targetIso

def tag
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    (_ : AppliedIdentityLeaf source orientation wire) : StepTag :=
  .identityLeaf

end AppliedIdentityLeaf

namespace AppliedRefLeaf

def source
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {definition : Fin definitions.length}
    (_ : AppliedRefLeaf source orientation wire definition) := source

def target
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {definition : Fin definitions.length}
    (applied : AppliedRefLeaf source orientation wire definition) :=
  applied.result.target

/-- The exact concrete construction accepted by this opaque reference-leaf
receipt. -/
def constructionResult
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {definition : Fin definitions.length}
    (applied : AppliedRefLeaf source orientation wire definition) :
    ConcreteWirePrimitive.LeafResult source wire :=
  applied.result

/-- Exact ordered reference nodes introduced by reference leaf expansion. -/
def inverseNodes
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {definition : Fin definitions.length}
    (applied : AppliedRefLeaf source orientation wire definition) :
    List applied.target.val.NodeId :=
  applied.result.targetRemovedNodes

/-- Exact target scope at which the introduced reference leaves abstract. -/
def inverseScope
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {definition : Fin definitions.length}
    (applied : AppliedRefLeaf source orientation wire definition) :
    applied.target.val.RegionId :=
  applied.result.targetScope

/-- Construction-owned inverse landing for a transported reference leaf. -/
def inverseTransport
    {planned real : CheckedDiagram definitions}
    {joinOrientation orientation : Orientation}
    {wire : planned.val.WireId}
    {definition : Fin definitions.length}
    {nodes : List real.val.NodeId}
    {scope : real.val.RegionId}
    (applied : AppliedRefLeaf planned joinOrientation wire definition)
    (backward : AppliedRefAbstract real orientation nodes scope)
    (targetIso : ConcreteIso real.val applied.target.val) :
    Except WireLeafError
      (InverseLanding backward.result.checked planned) :=
  acceptInverseLanding applied.result backward.result targetIso

def tag
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {definition : Fin definitions.length}
    (_ : AppliedRefLeaf source orientation wire definition) : StepTag :=
  .refLeaf

end AppliedRefLeaf

namespace AppliedAbstractFormal

def source
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {nodes : List source.val.NodeId}
    {scope : source.val.RegionId}
    (_ : AppliedAbstractFormal source orientation nodes scope) := source

def target
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {nodes : List source.val.NodeId}
    {scope : source.val.RegionId}
    (applied : AppliedAbstractFormal source orientation nodes scope) :=
  applied.result.target

/-- Checked reconstruction used to accept this abstraction receipt. -/
def reconstructed
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {nodes : List source.val.NodeId}
    {scope : source.val.RegionId}
    (applied : AppliedAbstractFormal source orientation nodes scope) :=
  applied.ledger.reverse.target

/-- Total reconstruction-to-source isomorphism owned by the accepted receipt. -/
def reverseIso
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {nodes : List source.val.NodeId}
    {scope : source.val.RegionId}
    (applied : AppliedAbstractFormal source orientation nodes scope) :
    ConcreteIso applied.reconstructed.val source.val :=
  applied.ledger.inverseIso

def tag
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {nodes : List source.val.NodeId}
    {scope : source.val.RegionId}
    (_ : AppliedAbstractFormal source orientation nodes scope) : StepTag :=
  .abstractFormal

end AppliedAbstractFormal

namespace AppliedIdentityAbstract

def source
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {nodes : List source.val.NodeId}
    {scope : source.val.RegionId}
    (_ : AppliedIdentityAbstract source orientation nodes scope) := source

def target
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {nodes : List source.val.NodeId}
    {scope : source.val.RegionId}
    (applied : AppliedIdentityAbstract source orientation nodes scope) :=
  applied.result.target

/-- Checked reconstruction used to accept this abstraction receipt. -/
def reconstructed
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {nodes : List source.val.NodeId}
    {scope : source.val.RegionId}
    (applied : AppliedIdentityAbstract source orientation nodes scope) :=
  applied.ledger.reverse.target

/-- Total reconstruction-to-source isomorphism owned by the accepted receipt. -/
def reverseIso
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {nodes : List source.val.NodeId}
    {scope : source.val.RegionId}
    (applied : AppliedIdentityAbstract source orientation nodes scope) :
    ConcreteIso applied.reconstructed.val source.val :=
  applied.ledger.inverseIso

def tag
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {nodes : List source.val.NodeId}
    {scope : source.val.RegionId}
    (_ : AppliedIdentityAbstract source orientation nodes scope) : StepTag :=
  .identityAbstract

end AppliedIdentityAbstract

namespace AppliedRefAbstract

def source
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {nodes : List source.val.NodeId}
    {scope : source.val.RegionId}
    (_ : AppliedRefAbstract source orientation nodes scope) := source

def target
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {nodes : List source.val.NodeId}
    {scope : source.val.RegionId}
    (applied : AppliedRefAbstract source orientation nodes scope) :=
  applied.result.target

/-- Checked reconstruction used to accept this abstraction receipt. -/
def reconstructed
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {nodes : List source.val.NodeId}
    {scope : source.val.RegionId}
    (applied : AppliedRefAbstract source orientation nodes scope) :=
  applied.ledger.reverse.target

/-- Total reconstruction-to-source isomorphism owned by the accepted receipt. -/
def reverseIso
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {nodes : List source.val.NodeId}
    {scope : source.val.RegionId}
    (applied : AppliedRefAbstract source orientation nodes scope) :
    ConcreteIso applied.reconstructed.val source.val :=
  applied.ledger.inverseIso

def tag
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {nodes : List source.val.NodeId}
    {scope : source.val.RegionId}
    (_ : AppliedRefAbstract source orientation nodes scope) : StepTag :=
  .refAbstract

end AppliedRefAbstract

def applyApplyFormal
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (position : Nat)
    (orientation : Orientation) :
    Except WireLeafError
      (AppliedApplyFormal source orientation wire position) := do
  let result ←
    (ConcreteWirePrimitive.applyFormal source wire position).mapError
      .concreteRejected
  let polarity ← requireLeafPolarity source orientation wire
  match sourceSignature : (source.val.wires wire).sig with
  | .iota => throw .semanticLedgerRejected
  | .rel sourceArguments =>
      let kind ←
        optionToExcept .semanticLedgerRejected <|
          LeavesSemantics.LeafKind.checkFormal sourceArguments position
      let factorization ←
        optionToExcept .semanticLedgerRejected <|
          LeavesSemantics.checkLeafFactorization result sourceArguments
            sourceSignature kind
      pure
        ⟨result, sourceArguments, sourceSignature, kind, factorization,
          polarity⟩

def applyIdentityLeaf
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (orientation : Orientation) :
    Except WireLeafError
      (AppliedIdentityLeaf source orientation wire) := do
  let result ←
    (ConcreteWirePrimitive.identityLeaf source wire).mapError
      .concreteRejected
  let polarity ← requireLeafPolarity source orientation wire
  match sourceSignature : (source.val.wires wire).sig with
  | .iota => throw .semanticLedgerRejected
  | .rel sourceArguments =>
      let kind ←
        optionToExcept .semanticLedgerRejected <|
          LeavesSemantics.LeafKind.checkIdentity sourceArguments
      let factorization ←
        optionToExcept .semanticLedgerRejected <|
          LeavesSemantics.checkLeafFactorization result sourceArguments
            sourceSignature kind
      pure
        ⟨result, sourceArguments, sourceSignature, kind, factorization,
          polarity⟩

def applyRefLeaf
    (source : CheckedDiagram definitions)
    (wire : source.val.WireId)
    (definition : Fin definitions.length)
    (orientation : Orientation) :
    Except WireLeafError
      (AppliedRefLeaf source orientation wire definition) := do
  let result ←
    (ConcreteWirePrimitive.refLeaf source wire definition).mapError
      .concreteRejected
  let polarity ← requireLeafPolarity source orientation wire
  match sourceSignature : (source.val.wires wire).sig with
  | .iota => throw .semanticLedgerRejected
  | .rel sourceArguments =>
      let kind ←
        optionToExcept .semanticLedgerRejected <|
          LeavesSemantics.LeafKind.checkReference sourceArguments
            definition
      let factorization ←
        optionToExcept .semanticLedgerRejected <|
          LeavesSemantics.checkLeafFactorization result sourceArguments
            sourceSignature kind
      pure
        ⟨result, sourceArguments, sourceSignature, kind, factorization,
          polarity⟩

def applyAbstractFormal
    (source : CheckedDiagram definitions)
    (nodes : List source.val.NodeId)
    (scope : source.val.RegionId)
    (orientation : Orientation) :
    Except WireLeafError
      (AppliedAbstractFormal source orientation nodes scope) := do
  let result ←
    (ConcreteWirePrimitive.abstractFormal source nodes scope).mapError
      .concreteRejected
  let polarity ← requireAbstractPolarity source orientation scope
  let reverse ←
    (ConcreteWirePrimitive.applyFormal result.checked result.targetWire 0)
      |>.mapError (fun _ => .semanticLedgerRejected)
  match sourceSignature :
      (result.checked.val.wires result.targetWire).sig with
  | .iota => throw .semanticLedgerRejected
  | .rel sourceArguments =>
      let kind ←
        optionToExcept .semanticLedgerRejected <|
          LeavesSemantics.LeafKind.checkFormal sourceArguments 0
      let ledger ←
        optionToExcept .semanticLedgerRejected <|
          checkAbstractLedger source scope result reverse sourceArguments
            sourceSignature kind
      pure ⟨result, ledger, polarity⟩

def applyIdentityAbstract
    (source : CheckedDiagram definitions)
    (nodes : List source.val.NodeId)
    (scope : source.val.RegionId)
    (orientation : Orientation) :
    Except WireLeafError
      (AppliedIdentityAbstract source orientation nodes scope) := do
  let result ←
    (ConcreteWirePrimitive.identityAbstract source nodes scope).mapError
      .concreteRejected
  let polarity ← requireAbstractPolarity source orientation scope
  let reverse ←
    (ConcreteWirePrimitive.identityLeaf result.checked result.targetWire)
      |>.mapError (fun _ => .semanticLedgerRejected)
  match sourceSignature :
      (result.checked.val.wires result.targetWire).sig with
  | .iota => throw .semanticLedgerRejected
  | .rel sourceArguments =>
      let kind ←
        optionToExcept .semanticLedgerRejected <|
          LeavesSemantics.LeafKind.checkIdentity sourceArguments
      let ledger ←
        optionToExcept .semanticLedgerRejected <|
          checkAbstractLedger source scope result reverse sourceArguments
            sourceSignature kind
      pure ⟨result, ledger, polarity⟩

def applyRefAbstract
    (source : CheckedDiagram definitions)
    (nodes : List source.val.NodeId)
    (scope : source.val.RegionId)
    (orientation : Orientation) :
    Except WireLeafError
      (AppliedRefAbstract source orientation nodes scope) := do
  let result ←
    (ConcreteWirePrimitive.refAbstract source nodes scope).mapError
      .concreteRejected
  let polarity ← requireAbstractPolarity source orientation scope
  match nodes with
  | [] => throw .semanticLedgerRejected
  | first :: _ =>
      match source.val.nodes first with
      | .ref _ definition _ =>
          let reverse ←
            (ConcreteWirePrimitive.refLeaf result.checked result.targetWire
              definition).mapError (fun _ => .semanticLedgerRejected)
          match sourceSignature :
              (result.checked.val.wires result.targetWire).sig with
          | .iota => throw .semanticLedgerRejected
          | .rel sourceArguments =>
              let kind ←
                optionToExcept .semanticLedgerRejected <|
                  LeavesSemantics.LeafKind.checkReference sourceArguments
                    definition
              let ledger ←
                optionToExcept .semanticLedgerRejected <|
                  checkAbstractLedger source scope result reverse
                    sourceArguments sourceSignature kind
              pure ⟨result, ledger, polarity⟩
      | _ => throw .semanticLedgerRejected

private theorem leafDirected
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {wire : source.val.WireId}
    {result : ConcreteWirePrimitive.LeafResult source wire}
    {sourceArguments : List Sig}
    {kind : LeavesSemantics.LeafKind definitions sourceArguments}
    (factorization :
      LeavesSemantics.LeafFactorization result sourceArguments kind)
    (polarity : CheckedLeafPolarity source orientation wire)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    Directed orientation
      (denoteChecked model.toPreModel definitionEnv source)
      (denoteChecked model.toPreModel definitionEnv result.checked) := by
  have compiledExact :
      polarity.compiled = factorization.sourceScope :=
    SiteCompilation.unique polarity.compiled factorization.sourceScope
  cases orientation with
  | forward =>
      have legal :
          polarity.compiled.frame.context.cutDepth % 2 = 1 :=
        of_decide_eq_true (by
          simpa [joinPolarityLegal] using polarity.legal)
      rw [compiledExact] at legal
      exact (factorization.directions model definitionEnv).2 legal
  | backward =>
      have legal :
          polarity.compiled.frame.context.cutDepth % 2 = 0 :=
        of_decide_eq_true (by
          simpa [joinPolarityLegal] using polarity.legal)
      rw [compiledExact] at legal
      exact (factorization.directions model definitionEnv).1 legal

private theorem abstractDirected
    {source : CheckedDiagram definitions}
    {orientation : Orientation}
    {scope : source.val.RegionId}
    {result : LeafAbstractResult source}
    (ledger : AbstractLedger source scope result)
    (polarity : CheckedAbstractPolarity source orientation scope)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    Directed orientation
      (denoteChecked model.toPreModel definitionEnv source)
      (denoteChecked model.toPreModel definitionEnv result.checked) := by
  have compiledExact : polarity.compiled = ledger.sourceScope :=
    SiteCompilation.unique polarity.compiled ledger.sourceScope
  have inverse :=
    iso_denotation ledger.inverseIso model.toPreModel definitionEnv
  cases orientation with
  | forward =>
      have legal :
          polarity.compiled.frame.context.cutDepth % 2 = 0 :=
        of_decide_eq_true (by
          simpa [severPolarityLegal] using polarity.legal)
      rw [compiledExact] at legal
      have factorLegal :
          ledger.factorization.sourceScope.frame.context.cutDepth % 2 = 0 := by
        rw [ledger.cutDepthExact]
        exact legal
      intro sourceHolds
      exact
        (ledger.factorization.directions model definitionEnv).1 factorLegal
          (inverse.mpr sourceHolds)
  | backward =>
      have legal :
          polarity.compiled.frame.context.cutDepth % 2 = 1 :=
        of_decide_eq_true (by
          simpa [severPolarityLegal] using polarity.legal)
      rw [compiledExact] at legal
      have factorLegal :
          ledger.factorization.sourceScope.frame.context.cutDepth % 2 = 1 := by
        rw [ledger.cutDepthExact]
        exact legal
      intro targetHolds
      exact inverse.mp
        ((ledger.factorization.directions model definitionEnv).2
          factorLegal targetHolds)

/-- Checked formal application is sound in the selected join direction. -/
theorem apply_formal_sound
    {source : CheckedDiagram definitions}
    (wire : source.val.WireId)
    (position : Nat)
    (orientation : Orientation)
    (applied : AppliedApplyFormal source orientation wire position)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    Directed orientation
      (denoteChecked model.toPreModel definitionEnv applied.source)
      (denoteChecked model.toPreModel definitionEnv applied.target) :=
  leafDirected applied.factorization applied.polarity model definitionEnv

/-- Checked formal abstraction is sound in the selected sever direction. -/
theorem abstract_formal_sound
    {source : CheckedDiagram definitions}
    (nodes : List source.val.NodeId)
    (scope : source.val.RegionId)
    (orientation : Orientation)
    (applied : AppliedAbstractFormal source orientation nodes scope)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    Directed orientation
      (denoteChecked model.toPreModel definitionEnv applied.source)
      (denoteChecked model.toPreModel definitionEnv applied.target) :=
  abstractDirected applied.ledger applied.polarity model definitionEnv

/-- Checked identity leaf introduction is sound in its join direction. -/
theorem identity_leaf_sound
    {source : CheckedDiagram definitions}
    (wire : source.val.WireId)
    (orientation : Orientation)
    (applied : AppliedIdentityLeaf source orientation wire)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    Directed orientation
      (denoteChecked model.toPreModel definitionEnv applied.source)
      (denoteChecked model.toPreModel definitionEnv applied.target) :=
  leafDirected applied.factorization applied.polarity model definitionEnv

/-- Checked identity abstraction is sound in its sever direction. -/
theorem identity_abstract_sound
    {source : CheckedDiagram definitions}
    (nodes : List source.val.NodeId)
    (scope : source.val.RegionId)
    (orientation : Orientation)
    (applied : AppliedIdentityAbstract source orientation nodes scope)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    Directed orientation
      (denoteChecked model.toPreModel definitionEnv applied.source)
      (denoteChecked model.toPreModel definitionEnv applied.target) :=
  abstractDirected applied.ledger applied.polarity model definitionEnv

/-- Checked folded-reference leaf introduction is sound without unfolding. -/
theorem ref_leaf_sound
    {source : CheckedDiagram definitions}
    (wire : source.val.WireId)
    (definition : Fin definitions.length)
    (orientation : Orientation)
    (applied : AppliedRefLeaf source orientation wire definition)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    Directed orientation
      (denoteChecked model.toPreModel definitionEnv applied.source)
      (denoteChecked model.toPreModel definitionEnv applied.target) :=
  leafDirected applied.factorization applied.polarity model definitionEnv

/-- Checked folded-reference abstraction is sound without macro expansion. -/
theorem ref_abstract_sound
    {source : CheckedDiagram definitions}
    (nodes : List source.val.NodeId)
    (scope : source.val.RegionId)
    (orientation : Orientation)
    (applied : AppliedRefAbstract source orientation nodes scope)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions) :
    Directed orientation
      (denoteChecked model.toPreModel definitionEnv applied.source)
      (denoteChecked model.toPreModel definitionEnv applied.target) :=
  abstractDirected applied.ledger applied.polarity model definitionEnv

end Leaves

end WirePrimitive

end VisualProof
