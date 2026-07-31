import VisualProof.Diagram.Concrete.WirePrimitive.LeavesSemantics
import VisualProof.Rule.Tag
import VisualProof.Rule.Structural

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
  let inverseIso ←
    ConcreteIsoSearch.findConcreteIso? reverse.checked.val source.val
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
